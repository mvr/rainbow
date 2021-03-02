module Concrete where

import Data.Maybe (mapMaybe)
import Data.List (nub)

-- Let's try to keep this in exact correspondence with the surface syntax.

type Ident = String

-- FIXME: Let's try this first, a slice is specified by a list of colour labels that are tensored together.
data Slice where
  Slice :: [Ident] -> Slice
  SliceOmitted :: Slice
  SliceOne :: Slice
  SliceTop :: Slice
  deriving (Show, Eq)



data Unit where
  deriving (Show, Eq)

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
  Hom :: {- body col -} Maybe Ident ->{- var col -} Maybe Ident -> {- var name -} Maybe Ident -> Ty -> Ty -> Ty

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
  TensorPat :: Maybe Ident -> Pat -> Maybe Ident -> Pat -> Pat
  ZeroTensorPat :: Pat -> Pat -> Pat
  deriving (Show)

comprehendPat :: Term -> Maybe Pat
comprehendPat t = go False t -- Have we been zeroed by an UndIn yet?
  where
    go False (Check (Var x) ty) = Just $ VarPat x ty
    go True (Check (ZeroVar x) ty) = Just $ ZeroVarPat x ty
    go f OneIn = Just $ OnePat
    go f (Pair x y) = PairPat <$> go f x <*> go f y
    go False (TensorPair lc x rc y) = TensorPat <$> pure (comprehendCol lc) <*> go False x <*> pure (comprehendCol rc) <*> go False y
      where comprehendCol (Just (Slice [c])) = Just c
            comprehendCol Nothing = Nothing
    go True (TensorPair (Just SliceOne) x (Just SliceOne) y) = ZeroTensorPat <$> go True x <*> go True y
    go f (UndIn u) = UndInPat <$> go True u
    go _ _ = Nothing

data Decl where
  Def :: Ident -> Term -> Ty -> Decl
  Dont :: Ident -> Term -> Ty -> Decl
  deriving (Show)
