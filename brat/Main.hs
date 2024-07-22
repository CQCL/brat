import Brat.Compile.Scheme
import Brat.Error
import Brat.Load

import Control.Monad
import System.Environment
import System.FilePath (dropExtension)

eitherIO :: Either Error a -> IO a
eitherIO (Left e) = fail (debug e)
eitherIO (Right a) = pure a

main = do
  args <- getArgs
  let (file, compile) = case args of
                          [x] -> (x, False)
                          ["-c",x] -> (x, True)
                          _ -> error "please provide one file"
  contents <- readFile file
  (nouns, verbs, holes) <- eitherIO (loadFile file contents)
  if compile
    then do let output = compileFile (nouns, verbs)
            let outFile = (dropExtension file) <> ".ss"
            writeFile outFile output
            putStrLn output
            putStrLn $ "Wrote to file " ++ outFile

    else do putStrLn "Nouns:"
            print nouns
            putStrLn ""
            putStrLn "Verbs:"
            print verbs
            putStrLn ""
            putStrLn "Holes:"
            mapM_ print holes
