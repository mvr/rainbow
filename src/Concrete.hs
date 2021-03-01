module Concrete where

import Data.Maybe (mapMaybe)
import Data.List (nub)

type Ident = String

data Palette where
  CommaPal :: Palette -> Palette -> Palette
  OnePal :: Palette
  OriginPal :: Palette
  TensorPal :: Palette -> Palette -> Palette
  UnitPal :: Ident -> Palette
  LabelPal :: Ident -> Palette -> Palette
  deriving (Show)

-- emptyPal :: Palette
-- emptyPal = OnePal

-- palExtend :: Palette -> Palette -> Palette
-- palExtend (Palette p1) (Palette p2) = Palette (p1 ++ p2)

-- palLoneTensor :: (Ident, Ident) -> PalettePiece
-- palLoneTensor (r, b) = TensorPal (Just r) emptyPal (Just b) emptyPal

-- data Colour where
--   NamedColour :: Ident -> Colour
--   ZeroColour :: Colour
--   TopColour :: Colour
--   deriving (Eq, Show)

-- palExtHom :: Palette -> Maybe Ident -> Maybe Ident -> Palette
-- palExtHom pal bodyc yc = Palette [TensorPal bodyc pal yc emptyPal]

-- colExtHom :: {- body colour -} Ident -> Colour -> Colour
-- colExtHom bodyc TopColour = NamedColour bodyc
-- colExtHom bodyc (NamedColour n) = NamedColour n
-- colExtHom bodyc ZeroColour = ZeroColour

-- FIXME: Let's try this first, a slice is specified by a list of labels that are tensored together.
data Slice where
  Slice :: [Ident] -> Slice
  SliceOmitted :: Slice
  SliceOne :: Slice
  SliceTop :: Slice
  deriving (Show, Eq)

data Unit where
  deriving (Show, Eq)

-- data Slice where
--   OneSl :: Slice
--   IdentSl :: Ident -> Slice -> Slice
--   CommaSl :: Slice -> Slice -> Slice
--   TensorSl :: Slice -> Slice -> Slice
--   deriving (Show, Eq)

data TeleCell = TeleCell (Maybe Ident) Ty
  deriving (Show)

type Ty = Term

data Term where
  Check :: Term -> Ty -> Term

  Univ :: Int -> Ty

  Pi :: [TeleCell] -> Ty -> Ty
  One :: Ty
  Sg :: [TeleCell] -> Ty -> Ty

  Und :: Ty -> Ty

  Tensor :: Maybe Ident -> Ty -> Ty -> Ty
  Hom :: Maybe Ident -> Ty -> Ty -> Ty

  Var :: Ident -> Term
  ZeroVar :: Ident -> Term

  Lam :: [Ident] -> Term -> Term
  App :: Term -> [Term] -> Term

  Pair :: Term -> Term -> Term
  Fst :: Term -> Term
  Snd :: Term -> Term

  OneIn :: Term

  UndIn :: Term -> Term
  UndOut :: Term -> Term

  TensorPair :: Maybe Slice -> Term -> Maybe Slice -> Term -> Term

  UnitIn :: Unit -> Term

  Match ::    {- target -} Term
           -> {- motive var -} Maybe Ident -> {- motive -} Ty
           -> {- pat -}    Term -- Type of the target can be recovered from this
           -> {- branch -} Term
           -> Term

  -- TensorElim :: Term
  --   -> {- motive var -} Maybe Ident -> {- motive -} Ty
  --   -> {- new left var and col -} (Ident, Maybe Ident)
  --   -> {- new right var and col -} (Ident, Maybe Ident)
  --   -> {- branch -} Term
  --   -> Term

  -- TensorElimFrob :: Palette
  --   -> {- Var names and their colours variables -} [(Ident, Colour, Ty)]
  --   -> TeleSubst
  --   -> {- which var in tele -} Ident
  --   -> {- motive -} Ty
  --   -> {- new left var and col -} (Ident, Maybe Ident)
  --   -> {- new right var and col -} (Ident, Maybe Ident)
  --   -> {- branch -} Term
  --   -> Term

  HomLam :: {- body colour -} Maybe Ident -> {- var colour -} Maybe Ident -> {- var name -} Ident -> Term -> Term
  HomApp :: Maybe Slice -> Term -> Maybe Slice -> Term -> Term

  deriving (Show)


data Pat where
  OnePat :: Pat
  UnitPat :: Ident -> Pat
  VarPat :: Ident -> Ty -> Pat
  ZeroVarPat :: Ident -> Ty -> Pat
  UndInPat :: Pat -> Pat
  PairPat :: Pat -> Pat -> Pat
  TensorPat :: Ident -> Pat -> Ident -> Pat -> Pat
  ZeroTensorPat :: Pat -> Pat -> Pat
  deriving (Show)

comprehendPat :: Term -> Maybe Pat
comprehendPat t = go False t -- Have we been zeroed by an UndIn yet?
  where
    go False (Check (Var x) ty) = Just $ VarPat x ty
    go True (Check (ZeroVar x) ty) = Just $ ZeroVarPat x ty
    go f OneIn = Just $ OnePat
    go f (Pair x y) = PairPat <$> go f x <*> go f y
    go False (TensorPair (Just (Slice [l])) x (Just (Slice [r])) y) = TensorPat <$> pure l <*> go False x <*> pure r <*> go False y
    go True (TensorPair (Just SliceOne) x (Just SliceOne) y) = ZeroTensorPat <$> go True x <*> go True y
    go f (UndIn u) = UndInPat <$> go True u
    go _ _ = Nothing

patPalette :: Pat -> Palette
patPalette OnePat = OnePal
patPalette (VarPat _ _) = OnePal
patPalette (UnitPat u) = UnitPal u
patPalette (PairPat p q) = CommaPal (patPalette p) (patPalette q)
patPalette (TensorPat sl p sr q) = TensorPal (LabelPal sl (patPalette p)) (LabelPal sr (patPalette q))
patPalette (UndInPat p) = OnePal

data Decl where
  Def :: Ident -> Term -> Ty -> Decl
  Dont :: Ident -> Term -> Ty -> Decl
  deriving (Show)
