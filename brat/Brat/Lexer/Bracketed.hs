module Brat.Lexer.Bracketed (BToken(..), brackets) where

import Data.Bracket
import Brat.Error (BracketErrMsg(..), Error(Err), ErrorMsg(..))
import Brat.FC
import Brat.Lexer.Token
import Bwd

import Text.Megaparsec (VisualStream(..))

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

tokLen :: BToken -> Int
tokLen (FlatTok tok) = length (show tok)
tokLen (Bracketed _ _ bs) = sum (tokLen <$> bs) + 2

instance Show BToken where
  show (FlatTok t) = show t
  show (Bracketed _ b ts) = showOpen b ++ show ts ++ showClose b

instance VisualStream [BToken] where
  showTokens _ ts = concatMap show ts
  tokensLength _ = sum . fmap tokLen

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
