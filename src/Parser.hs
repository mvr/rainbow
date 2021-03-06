module Parser where

import Data.Void

import Control.Monad (join)

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Concrete as C

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

reserved :: [String]
reserved = ["let", "fun", "fst", "snd", "undin", "undout", "U", "type", "at", "with", "match", "hom", "don't", "Id", "refl", "Unit", "unitin", "postulate"]

ident :: Parser Ident
ident = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many (alphaNumChar <|> char '\'' <|> char '_')
    check x = if x `elem` reserved
              then fail $ "keyword " ++ show x ++ " cannot be an identifier"
              else return x

prodSym :: Parser ()
prodSym = pure () <* (try (symbol "*") <|> symbol "×")

funSym :: Parser ()
funSym = pure () <* (try (symbol "->") <|> symbol "→")

tensorSym :: Parser ()
tensorSym = pure () <* (try (symbol "*o") <|> symbol "⊗")

homSym :: Parser ()
homSym = pure () <* (try (symbol "-o") <|> symbol "⊸")

slice :: Parser Slice
slice = try ( symbol "_" *> pure SliceOmitted )
  <|> try ( symbol "1" *> pure SliceOne)
  <|> try ( symbol "top" *> pure SliceTop)
  <|> try ( symbol "new" *> (SliceSummonedUnit <$> ident))
  <|> (Slice <$> many ident)

unit :: Parser Unit
unit = (UnitList <$> many ident)

teleCell :: Parser TeleCell
teleCell = do
  symbol "("
  n <- ident
  symbol ":"
  nty <- term
  symbol ")"
  return $ TeleCell (Just n) nty

-- Allow binding many variables of the same type, only for Pi types to
-- avoid confusion
teleMultiCell :: Parser [TeleCell]
teleMultiCell = do
  symbol "("
  ns <- some ident
  symbol ":"
  nty <- term
  symbol ")"
  return $ fmap (\n -> TeleCell (Just n) nty) ns

teleCells :: Parser [TeleCell]
teleCells = join <$> some teleMultiCell

atomic :: Parser Term
atomic =
  try ( symbol "(" *> term <* symbol ")" )
  <|> try ( do
    symbol "("
    a <- term
    symbol "at"
    b <- term
    symbol ")"
    return (Check a b)
  )
  <|> try ( Univ <$> (symbol "U<" *> L.decimal <* symbol ">"))
  <|> try ( Unit <$ symbol "Unit" )
  <|> try ( UnitIn <$> (symbol "unitin[" *> unit <* symbol "]"))
  <|> try ( UndIn <$> (symbol "undin" *> term))
  <|> try ( UndOut <$> (symbol "undout" *> term))
  -- <|> try ( Pair <$> (symbol "<" *> term <*> symbol "," <*> term <* symbol ">"))
  <|> try (do
    symbol "<"
    a <- term
    symbol ","
    b <- term
    symbol ">"
    return (Pair a b)
  )
  <|> try (
  do
    symbol "<<"
    a <- term
    symbol ","
    b <- term
    symbol ">>"
    (slL, slR) <- do
      symbol "["
      slL <- slice
      symbol ","
      slR <- slice
      symbol "]"
      return (Just slL, Just slR)
      <|>
      return (Nothing, Nothing)

    return (TensorPair slL a slR b)
  )
  <|> try (Refl <$> (symbol "refl" *> term))
  <|> try (ZeroVar <$> (char '_' *> ident))
  <|> Var <$> ident

term :: Parser Term
term =
  try ( Fst <$> (symbol "fst" *> term))
  <|> try ( Snd <$> (symbol "snd" *> term))
  <|> try (
    do
    symbol "fun"
    xs <- some ident
    funSym
    t <- term
    return (Lam xs t)
  )
  <|> try (
    do
      symbol "match"
      s <- term
      symbol "at"
      z <- try (do
                   z <- ident
                   funSym
                   return (Just z))
            <|> pure Nothing

      mot <- term
      symbol "with"

      pat <- atomic

      funSym

      c <- term

      return (Match s z mot pat c)
    )
  <|> try (
    do
      symbol "hom"

      (tc, ac) <- do
        symbol "["
        tc <- ident
        symbol ","
        ac <- ident
        symbol "]"
        return (Just tc, Just ac)
        <|>
        return (Nothing, Nothing)


      a <- ident

      homSym

      body <- term

      return (HomLam tc ac a body)
    )

  <|> try (
    do
      symbol "("
      f <- term
      symbol "@"
      a <- term
      symbol ")"

      (fc, ac) <- do
        symbol "["
        fc <- slice
        symbol ","
        ac <- slice
        symbol "]"
        return (Just fc, Just ac)
        <|>
        return (Nothing, Nothing)


      return (HomApp fc f ac a)
    )
  <|> try (do
              a <- atomic
              funSym
              b <- term
              return (Pi [TeleCell Nothing a] b)
              )
  <|> try (Pi <$> teleCells <* funSym <*> term)
  <|> try (Sg <$> some teleCell <* prodSym <*> term)
  <|> try (do
              a <- atomic
              prodSym
              b <- term
              return (Sg [TeleCell Nothing a] b)
              )
  <|> try (One <$ symbol "1")
  <|> try (Id <$ symbol "Id" <*> atomic <*> atomic <*> atomic)
  <|> try (Tensor Nothing <$> atomic <* tensorSym <*> term)
  <|> try (do
              TeleCell n a <- teleCell
              tensorSym
              b <- term
              return (Tensor n a b)
          )
  <|> try (Hom Nothing <$> pure Nothing <*> pure Nothing <*> atomic <* homSym <*> term)
  <|> try (do
              TeleCell n a <- teleCell
              homSym
              (ac, bc) <- do
                symbol "["
                ac <- ident
                symbol ","
                bc <- ident
                symbol "]"
                return (Just ac, Just bc)
                <|>
                return (Nothing, Nothing)
              b <- term
              return (Hom bc ac n a b)
          )
  <|> try (Und <$> (symbol "♮" *> term))
  <|> (
    do
    f <- atomic
    args <- many atomic
    if length args > 0 then -- We actually need this so `App`s don't end up in patterns.
      return (App f args)
    else
      return f
  )


decl :: Parser Decl
decl =
  do
    symbol "let"
    n <- ident
    symbol ":"
    t <- term
    symbol "="
    body <- term
    return (Def n body t)
  <|>
  do
    symbol "don't"
    symbol "let"
    n <- ident
    symbol ":"
    t <- term
    symbol "="
    body <- term
    return (Dont n body t)
  <|>
  do
    symbol "postulate"
    n <- ident
    symbol ":"
    t <- term
    return (Postulate n t)
