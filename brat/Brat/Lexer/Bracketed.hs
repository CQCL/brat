module Brat.Lexer.Bracketed (BToken(..), brackets) where

import Data.Bracket
import Brat.Error (BracketErrMsg(..), Error(Err), ErrorMsg(..))
import Brat.FC
import Brat.Lexer.Token
import Bwd

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

-- Parse between two brackets of the same type
within :: (FC, BracketType) -- The nearest opening bracket to the left of us
       -> Bwd BToken -- The tokens that we've passed since that open bracket
       -> [Token]    -- The tokens to the right of us, unparsed
       -> Either Error (FC         -- The location of the closing bracket
                       ,Bwd BToken -- The tokens between the open and close
                       ,[Token]    -- Tokens after the closing bracket
                       )
within (openFC, b) _ [] = Left $ eofErr openFC b
within ctx@(_, b) acc (t:ts)
 | Just b' <- closer (_tok t) = if b' == b
                                then pure (fc t, acc, ts)
                                else Left $ openCloseMismatchErr ctx (fc t, b')
 | Just b' <- opener (_tok t) = do
     let innerOpenFC = fc t
     (innerCloseFC, xs, ts) <- within (innerOpenFC, b') B0 ts
     let fc = spanFC innerOpenFC innerCloseFC
     within ctx (acc :< Bracketed fc b' (xs <>> [])) ts
 | otherwise = within ctx (acc :< FlatTok t) ts

brackets :: [Token] -> Either Error [BToken]
brackets ts = (<>> []) <$> bracketsWorker B0 ts
 where
  bracketsWorker :: Bwd BToken -> [Token] -> Either Error (Bwd BToken)
  bracketsWorker acc [] = pure acc
  bracketsWorker acc (t:ts)
   | Just b <- opener (_tok t) = do
       (closeFC, xs, ts) <- within (fc t, b) B0 ts
       let enclosingFC = spanFC (fc t) closeFC
       bracketsWorker (acc :< Bracketed enclosingFC b (xs <>> [])) ts
   | Just b <- closer (_tok t) = Left $ unexpectedCloseErr (fc t) b
   | otherwise = bracketsWorker (acc :< FlatTok t) ts
