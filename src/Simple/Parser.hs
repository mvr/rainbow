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
reserved = ["let", "fun", "fst", "snd", "type", "at", "with", "tensormatch", "hom"]

ident :: Parser Ident
ident = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many (alphaNumChar <|> char '\'')
    check x = if x `elem` reserved
              then fail $ "keyword " ++ show x ++ " cannot be an identifier"
              else return x

-- ident :: Parser Ident
-- ident = lexeme ((:) <$> letterChar <*> many alphaNumChar <?> "identifier")

prodSym :: Parser ()
prodSym = pure () <* (try (symbol "*") <|> symbol "×")

tensorSym :: Parser ()
tensorSym = pure () <* (try (symbol "*o") <|> symbol "⊗")

homSym :: Parser ()
homSym = pure () <* (try (symbol "-o") <|> symbol "⊸")

slice :: Parser Slice
slice = try ( symbol "." *> pure (Slice []) )
  <|> (Slice <$> many (NamedColour <$> ident))

palettePiece :: Parser PalettePiece
palettePiece = do
  symbol "("
  r <- (Just <$> ident) <|> (pure Nothing <* char '_')
  rp <- try (symbol "=" *> palette) 
        <|> pure (emptyPal)
  tensorSym
  b <- (Just <$> ident) <|> (pure Nothing <* char '_')
  bp <- try (symbol "=" *> palette) 
        <|> pure (emptyPal)
  symbol ")"
  return $ TensorPal r rp b bp

palette :: Parser Palette
palette = Palette <$> (try (symbol "." *> return []) <|> (palettePiece `sepBy1` (symbol ",")))

palSubstPiece = do
  symbol "("
  slr <- slice
  symbol "/"
  r <- ident
  rtheta <- try (symbol "=" *> palSubst)
            <|> pure (PaletteSubst [])
  tensorSym
  slb <- slice
  symbol "/"
  b <- ident
  btheta <- try (symbol "=" *> palSubst)
            <|> pure (PaletteSubst [])
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
ty = try (Pi <$> atomicTy <* symbol "->" <*> ty)
  <|> try (Sg <$> atomicTy <* prodSym <*> ty)
  <|> try (Tensor <$> atomicTy <* tensorSym <*> ty)
  <|> try (Hom <$> atomicTy <* homSym <*> ty)
  <|> try (Und <$> (symbol "♮" *> ty))
  <|> try (symbol "(" *> ty <* symbol ")")
  <|> BaseTy <$> ident

atomic :: Parser Term
atomic = 
  try ( symbol "(" *> term <* symbol ")" )
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
  <|> try (
    do 
      symbol "tensormatch"
      s <- term
      symbol "at"
      mot <- ty
      symbol "with"

      symbol "<<"
      x <- ident
      symbol ","
      y <- ident
      symbol ">>"
      symbol "["
      xc <- ident
      symbol ","
      yc <- ident
      symbol "]"

      symbol "->"

      c <- term      
      
      return $ TensorElimSimple s mot (x, xc) (y, yc) c
    )
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
      symbol "at" 
      p <- palette
      symbol "|"
      omega <- flip sepBy (symbol ",") $ do
        try (do
                v <- ident
                symbol "["
                col <- ident
                symbol "]"                
            
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

      symbol "<<"
      x <- ident
      symbol ","
      y <- ident
      symbol ">>"
      symbol "["
      xc <- ident
      symbol ","
      yc <- ident
      symbol "]"

      symbol "->"

      c <- term

      return (TensorElim p omega (TeleSubst ps theta) z mot (x, xc) (y, yc) c)
    )
  <|> try ( -- hom[rc, bc] b -o <<rc#a, bc#b>>
    do 
      symbol "hom" 

      symbol "["
      tc <- ident
      symbol ","
      ac <- ident
      symbol "]"

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
