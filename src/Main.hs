module Main where

import Control.Monad (foldM)
import Text.Megaparsec

import Syntax
import Parser
import Driver as D

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

main :: IO ()
main = undefined
