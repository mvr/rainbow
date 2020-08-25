module Simple.Main where

import Control.Monad (foldM)
import Text.Megaparsec

import Simple.Syntax
import Simple.Parser
import Simple.Driver as D

checkFile :: String -> IO ()
checkFile fn = do
  contents <- readFile fn
  let parseResult = runParser (many decl <* eof) fn contents
  
  decls <- case parseResult of
    Left err -> error $ "Parse error: " ++ errorBundlePretty err
    Right decls -> return decls

  -- putStrLn $ show decls

  foldM processDecl D.emptyEnv decls

  return ()
