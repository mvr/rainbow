module Simple.Parser where

import Data.Void

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Simple.Concrete as C


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
reserved = ["let", "fun", "fst", "snd", "type", "for", "with", "tensormatch"]

ident :: Parser Ident
ident = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many (alphaNumChar <|> char '\'')
    check x = if x `elem` reserved
              then fail $ "keyword " ++ show x ++ " cannot be an identifier"
              else return x

-- ident :: Parser Ident
-- ident = lexeme ((:) <$> letterChar <*> many alphaNumChar <?> "identifier")

slice :: Parser Slice
slice = Slice <$> many ident

palettePiece :: Parser PalettePiece
palettePiece = do
  symbol "("
  r <- (Just <$> ident) <|> (pure Nothing <* char '_')
  symbol "="
  rp <- palette
  symbol "⊗"
  b <- (Just <$> ident) <|> (pure Nothing <* char '_')
  symbol "="
  bp <- palette
  symbol ")"
  return $ TensorPal r rp b bp

palette :: Parser Palette
palette = Palette <$> (try (symbol "." *> return []) <|> (palettePiece `sepBy1` (symbol ",")))

palSubstPiece = do
  symbol "("
  slr <- slice
  symbol "/"
  r <- ident
  symbol "="
  rtheta <- palSubst
  symbol "⊗"
  slb <- slice
  symbol "/"
  b <- ident
  symbol "="
  btheta <- palSubst
  symbol ")"
  return $ TensorPalSub slr r rtheta slb b btheta

palSubst :: Parser PaletteSubst
palSubst = try (symbol "." *> pure (PaletteSubst []))
  <|> PaletteSubst <$>  palSubstPiece `sepBy1` (symbol ",")

-- telesubst :: Parser TeleSubst
-- telesubst = do 
--   ps <- palettesubst
--   symbol "#"
--   args <- sepBy mark (symbol ",")

-- colour :: Parser Colour
-- colour = try (symbol "⊤" *> pure ()) 

atomicTy :: Parser Ty
atomicTy = BaseTy <$> ident
           <|> try (symbol "(" *> ty <* symbol ")")
           <|> Und <$> (symbol "♮" *> ty)

ty :: Parser Ty
ty = try (Pi <$> atomicTy <* symbol "->" <*> atomicTy)
  <|> try (Sg <$> atomicTy <* symbol "*" <*> atomicTy)
  <|> try (Tensor <$> atomicTy <* symbol "⊗" <*> atomicTy)
  <|> try (Und <$> (symbol "♮" *> ty))
  <|> BaseTy <$> ident

atomic :: Parser Term
atomic = 
  try ( symbol "(" *> term <* symbol ")" )
  <|> try ( UndIn <$> (symbol "[undin" *> term <* symbol "]"))
  <|> try ( UndOut <$> (symbol "[undout" *> term <* symbol "]"))
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
    slL <- slice
    symbol "#"
    a <- term
    symbol ","
    slR <- slice
    symbol "#"
    b <- term
    symbol ">>"
    return (TensorPair slL a slR b)
  )
  <|> try (ZeroVar <$> (char '_' *> ident))
  <|> Var <$> ident
  
term :: Parser Term
term = 
  try ( Fst <$> (symbol "fst" *> term))
  <|> try ( Snd <$> (symbol "snd" *> term))
  <|> try (
    do 
    symbol "fun" 
    x <- ident
    symbol "->"
    t <- term
    return (Lam x t)
  )

-- tensormatch /p ⊗ /g | a/p, b/z, c/q for (p ⊗ g) | r#p, g#z, j#q -> C with 
--   z = n#x ⊗ m#y -> c

  <|> try (
    do
      symbol "tensormatch"
      ps <- palSubst
      symbol "|" 
      theta <- flip sepBy (symbol ",") $ do 
        t <- term
        -- symbol "/"
        -- v <- ident
        return t
      symbol "for" 
      p <- palette
      symbol "|"
      omega <- flip sepBy (symbol ",") $ do
        try (do
                col <- ident
                symbol "#"
                v <- ident
                return (v, NamedColour col)
            )
        <|>
          do
            v <- ident
            return (v, TopColour)
         
      symbol "->"
      mot <- ty
      symbol "with"
      z <- ident
      symbol "="

      xc <- ident
      symbol "#"
      x <- ident

      symbol "⊗"

      yc <- ident
      symbol "#"
      y <- ident
    
      symbol "->"

      c <- term

      return (TensorElim p omega (TeleSubst ps theta) z mot (x, xc) (y, yc) c)
    )
  <|> (
    do 
    f <- atomic
    args <- many atomic
    return (App f args)
  )

decl :: Parser Decl
decl =
  PostType <$> (symbol "type" *> ident)
  <|>
  do
    symbol "let" 
    n <- ident
    symbol ":" 
    t <- ty
    symbol "=" 
    body <- term
    return (Def n body t)
