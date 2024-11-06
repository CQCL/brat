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
opener LBracket = Just Bracket
opener LBrace = Just Brace
opener _ = Nothing

closer :: Tok -> Maybe BracketType
closer RParen = Just Paren
closer RBracket = Just Bracket
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
  showTokens _ ts = concatMap show ts
  tokensLength _ = sum . fmap btokLen

instance TraversableStream [BToken] where
  reachOffsetNoLine i pos = let fileName = sourceName (pstateSourcePos pos)
                                (Pos line col, rest) = worker (i - pstateOffset pos + 1) (pstateInput pos)
                            in pos
                            { pstateInput = rest
                            , pstateOffset = max (pstateOffset pos) i
                            , pstateSourcePos = SourcePos fileName (mkPos line) (mkPos col)
                            }
   where
    worker :: Int -> [BToken] -> (Pos, [BToken])
    worker 0 inp@(Bracketed fc _ _:_) = (start fc, inp)
    worker 0 inp@(FlatTok t:_) = (start (fc t), inp)
    worker i ((Bracketed fc b bts):rest) = let Pos closeLine closeCol = end fc
                                               closeFC = FC (Pos closeLine (closeCol - 1)) (Pos closeLine closeCol)
                                           in  worker (i - 1) (bts ++ [FlatTok (Token closeFC (closeTok b))] ++ rest)
    worker i (FlatTok t:rest)
     | i >= tokenLen t = worker (i - tokenLen t) rest
     | otherwise = (start (fc t), FlatTok t:rest)

    closeTok Paren = RParen
    closeTok Bracket = RBracket
    closeTok Brace = RBrace

eofErr :: FC -> BracketType -> Error
eofErr fc b = Err (Just fc) (BracketErr (EOFInBracket b))

openCloseMismatchErr :: (FC, BracketType) -> (FC, BracketType) -> Error
openCloseMismatchErr open (fcClose, bClose)
  = Err (Just fcClose) (BracketErr (OpenCloseMismatch open bClose))

unexpectedCloseErr :: FC -> BracketType -> Error
unexpectedCloseErr fc b = Err (Just fc) (BracketErr (UnexpectedClose b))

within :: (FC, BracketType) -> Bwd BToken -> [Token] -> Either Error (FC, Bwd BToken, [Token])
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
brackets ts = bracketsWorker B0 ts >>= \case
  (tokz, []) -> pure (tokz <>> [])
  _ -> error "Incomplete bracket parse" -- Shouldn't happen
 where
  bracketsWorker :: Bwd BToken -> [Token] -> Either Error (Bwd BToken, [Token])
  bracketsWorker acc [] = pure (acc, [])
  bracketsWorker acc (t:ts)
   | Just b <- opener (_tok t) = do
       (closeFC, xs, ts) <- within (fc t, b) B0 ts
       let enclosingFC = spanFC (fc t) closeFC
       bracketsWorker (acc :< Bracketed enclosingFC b (xs <>> [])) ts
   | Just b <- closer (_tok t) = Left $ unexpectedCloseErr (fc t) b
   | otherwise = bracketsWorker (acc :< FlatTok t) ts
