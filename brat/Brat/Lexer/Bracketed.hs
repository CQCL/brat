module Brat.Lexer.Bracketed (BToken(..), brackets) where

import Data.Bracket
import Brat.Error (BracketErrMsg(..), Error(Err), ErrorMsg(..))
import Brat.FC
import Brat.Lexer.Token

import Data.List.NonEmpty (NonEmpty(..))
import Data.Bifunctor (first)
import Text.Megaparsec (PosState(..), SourcePos(..), TraversableStream(..), VisualStream(..))
import Text.Megaparsec.Pos (mkPos)

data OpenClose = Open BracketType | Close BracketType

openClose :: Tok -> Maybe OpenClose
openClose LParen = Just (Open Paren)
openClose LSquare = Just (Open Square)
openClose LBrace = Just (Open Brace)
openClose RParen = Just (Close Paren)
openClose RSquare = Just (Close Square)
openClose RBrace = Just (Close Brace)
openClose _ = Nothing

-- Well bracketed tokens
data BToken
  = Bracketed FC BracketType [BToken]
  | FlatTok Token
 deriving (Eq, Ord)

btokLen :: BToken -> Int
btokLen (FlatTok tok) = length (show tok)
btokLen (Bracketed _ _ bs) = sum (btokLen <$> bs) + 2

instance Show BToken where
  show (FlatTok t) = show t
  show (Bracketed _ b ts) = showOpen b ++ concat (show <$> ts) ++ showClose b

instance VisualStream [BToken] where
  showTokens _ = concatMap show
  tokensLength _ = sum . fmap btokLen

instance TraversableStream [BToken] where
  reachOffsetNoLine i pos = let fileName = sourceName (pstateSourcePos pos)
                                (Pos line col, rest) = skipChars (i - pstateOffset pos + 1) (pstateInput pos)
                            in pos
                            { pstateInput = rest
                            , pstateOffset = max (pstateOffset pos) i
                            , pstateSourcePos = SourcePos fileName (mkPos line) (mkPos col)
                            }
   where
    skipChars :: Int -> [BToken] -> (Pos, [BToken])
    skipChars 0 inp@(Bracketed fc _ _:_) = (start fc, inp)
    skipChars 0 inp@(FlatTok t:_) = (start (fc t), inp)
    skipChars i ((Bracketed fc b bts):rest) =
      let Pos closeLine closeCol = end fc
          closeFC = FC (Pos closeLine (closeCol - 1)) (Pos closeLine closeCol)
      in  skipChars (i - 1) (bts ++ [FlatTok (Token closeFC (closeTok b))] ++ rest)
    skipChars i (FlatTok t:rest)
     | i >= tokenLen t = skipChars (i - tokenLen t) rest
     | otherwise = (start (fc t), FlatTok t:rest)

    closeTok Paren = RParen
    closeTok Square = RSquare
    closeTok Brace = RBrace

eofErr :: FC -> BracketType -> Error
eofErr fc b = Err (Just fc) (BracketErr (EOFInBracket b))

openCloseMismatchErr :: (FC, BracketType) -> (FC, BracketType) -> Error
openCloseMismatchErr open (fcClose, bClose)
  = Err (Just fcClose) (BracketErr (OpenCloseMismatch open bClose))

unexpectedCloseErr :: FC -> BracketType -> Error
unexpectedCloseErr fc b = Err (Just fc) (BracketErr (UnexpectedClose b))

brackets :: [Token] -> Either Error [BToken]
brackets ts = helper ts >>= \case
  (res, Nothing) -> pure res
  (_, Just (b, t:|_)) -> Left $ unexpectedCloseErr (fc t) b
 where
  -- Given a list of tokens, either
  -- (success) return [BToken] consisting of the prefix of the input [Token] in which all opened brackets are closed,
  --           and any remaining [Token] beginning with a closer that does not match any opener in the input
  --               (either Nothing = no remaining tokens; or tokens with the BracketType that the first token closes)
  -- (failure) return an error, if a bracket opened in the input, is either not closed (EOF) or does not match the closer
  helper :: [Token] -> Either Error ([BToken], Maybe (BracketType, NonEmpty Token))
  helper [] = pure ([], Nothing)
  helper (t:ts) = case openClose (_tok t) of
    Just (Open b) -> let openFC = fc t in helper ts >>= \case
      (_, Nothing) -> Left $ eofErr openFC b
      (within, Just (b', r :| rs)) ->
        let closeFC = fc r
            enclosingFC = spanFC openFC closeFC
        in  if b == b'
            then first (Bracketed enclosingFC b within:) <$> helper rs
            else Left $ openCloseMismatchErr (openFC, b) (closeFC, b')
    Just (Close b) -> pure ([], Just (b, t :| ts)) -- return closer for caller
    Nothing -> first (FlatTok t:) <$> helper ts
