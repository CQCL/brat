module Brat.Lexer.Bracketed (BToken(..), brackets) where

import Data.Bracket
import Brat.Error (BracketErrMsg(..), Error(Err), ErrorMsg(..))
import Brat.FC
import Brat.Lexer.Token

import Data.Bifunctor (first)
import Text.Megaparsec (PosState(..), SourcePos(..), TraversableStream(..), VisualStream(..))
import Text.Megaparsec.Pos (mkPos)

opener :: Tok -> Maybe BracketType
opener LParen = Just Paren
opener LSquare = Just Square
opener LBrace = Just Brace
opener _ = Nothing

closer :: Tok -> Maybe BracketType
closer RParen = Just Paren
closer RSquare = Just Square
closer RBrace = Just Brace
closer _ = Nothing

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
  show (Bracketed _ b ts) = showOpen b ++ show ts ++ showClose b

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
      let Pos closeLine closeCol = (end fc)
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
  (res, []) -> pure res
  (_, t:_) -> let Just b = closer (_tok t) -- guaranteed, helper consumes anything else
              in Left $ unexpectedCloseErr (fc t) b
 where
  -- Given a list of tokens, either
  -- (success) return [BToken] consisting of the prefix of the input [Token] in which all opened brackets are closed,
  --           and the remaining [Token] beginning with a closer that does not match any opener in the input;
  -- (failure) return an error, if a bracket opened in the input, is either not closed (EOF) or does not match the closer
  helper :: [Token] -> Either Error ([BToken], [Token])
  helper [] = pure ([], [])
  helper (t:ts)
    | Just b <- opener (_tok t) = let openFC = fc t in helper ts >>= \case
        (_, []) -> Left $ eofErr openFC b
        (within, r:rs) ->
          let Just b' = closer (_tok r) -- guaranteed, recursive call consumes anything else
              closeFC = fc r
              enclosingFC = (spanFC openFC closeFC)
          in if b == b' then
              (first ((Bracketed enclosingFC b within):)) <$> helper rs
            else
              Left $ openCloseMismatchErr (openFC, b) (closeFC, b')
    | Just _ <- closer (_tok t) = pure ([], (t:ts)) -- return closer for caller
    | otherwise = (first ((FlatTok t):)) <$> helper ts
