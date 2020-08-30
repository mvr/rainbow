{-# LANGUAGE GADTs #-}
module Syntax where

import Palette

data UnivLevel
  deriving (Show, Eq)
data Tele
  deriving (Show, Eq)
data TeleSubst where
  TeleSubst :: PaletteSubst -> [Term] -> TeleSubst
  deriving (Show, Eq)

type Ty = Term

data Term where 
  Check :: Term -> Ty -> Term

  Var :: Int -> Term -- DeBruijn indices for variables
  ZeroVar :: Int -> Term 

  Pi :: Ty -> Ty -> Term
  Lam :: Term -> Term
  App :: Term -> Term -> Term

  Sg :: Ty -> Ty -> Term
  Pair :: Term -> Term -> Term
  Fst :: Term -> Term
  Snd :: Term -> Term

  Id :: Ty -> Term -> Term -> Term
  Refl :: Term 
  IdElim :: Palette -> [ColourIndex] -> TeleSubst -> {- which var in tele -} Int -> {- motive -} Ty -> {- branch -} Term -> Term
  
  Univ :: UnivLevel -> Term  

  Und :: Ty -> Term
  UndIn :: Term -> Term
  UndOut :: Term -> Term

  Tensor :: Ty -> Ty -> Term
  TensorPair :: SliceIndex -> Term -> SliceIndex -> Term -> Term
  TensorElim :: Palette -> [ColourIndex] -> TeleSubst -> {- which var in tele -} Int -> {- motive -} Ty -> {- branch -} Term -> Term
  -- TensorPair :: Term -> Term -> Term
  -- TensorElim :: TeleSubst -> Tele -> Term -> Term

  Hom :: Ty -> Ty -> Term
  HomLam :: Term -> Term
  HomApp :: SliceIndex -> Term -> SliceIndex -> Term -> Term
  -- HomLam :: Term -> Term
  -- HomApp :: Term -> Term -> Term
  deriving (Show, Eq)

-- data WZ a = WZ {- regular -} a {- zeroed -} a
--   deriving (Show, Eq, Functor)
-- instance Applicative WZ where
--   pure a = WZ a a
--   (WZ f g) <*> (WZ a b) = WZ (f a) (g b)

type SemEnv = [Value]

data Closure where
  Closure :: Term -> SemEnv -> Closure
  deriving (Show, Eq)
data Closure3 where
  Closure3 :: Term -> SemEnv -> Closure3
  deriving (Show, Eq)
data ClosureTele where
  ClosureTele :: Term -> SemEnv -> ClosureTele
  deriving (Show, Eq)

type VTy = Value

data Value where
  VNeutral :: {- type -} VTy -> Neutral -> Value

  VPi :: VTy -> Closure -> Value
  VLam :: Closure -> Value

  VSg :: VTy -> Closure -> Value
  VPair :: Value -> Value -> Value

  VId :: VTy -> Value -> Value -> Value
  VRefl :: Value -> Value

  VUniv :: UnivLevel -> Value

  VUnd :: VTy -> Value
  VUndIn :: Value -> Value

  VTensor :: VTy -> Closure -> Value
  VTensorPair :: Value -> Value -> Value

  VHom :: VTy -> Closure -> Value
  VHomLam :: Closure -> Value
  deriving (Show, Eq)

data Neutral where
  NVar :: Int -> Neutral -- DeBruijn levels for variables
  NZeroVar :: Int -> Neutral

  NApp :: Neutral -> Normal -> Neutral

  NFst :: Neutral -> Neutral
  NSnd :: Neutral -> Neutral
  
  NIdElim :: {- mot -} ClosureTele -> {- branch -} ClosureTele -> {- A -} VTy -> {- a1 -} Value -> {- a2 -} Value -> {- theta -} ([Value], Neutral, [Value]) -> Neutral
  
  NUndOut :: Neutral -> Neutral

  NTensorElim :: {- mot -} ClosureTele -> {- branch -} ClosureTele -> {- theta -} ([Value], Neutral, [Value]) -> Neutral
    
  NHomApp :: Neutral -> Normal -> Neutral 
  deriving (Show, Eq)

data Normal where
  Normal :: {- type -} VTy -> {- term -} Value -> Normal 
  deriving (Show, Eq)

makeVarVal :: VTy -> {- level -} Int -> Value
makeVarVal ty lev = VNeutral ty (NVar lev)

-- Term with all colour information gone

data MonoTeleSubst where
  MonoTeleSubst :: [MonoTerm] -> MonoTeleSubst
  deriving (Show, Eq)

type MonoTy = MonoTerm

data MonoTerm where 
  MonoCheck :: MonoTerm -> MonoTy -> MonoTerm

  MonoVar :: Int -> MonoTerm
  MonoZeroVar :: Int -> MonoTerm 

  MonoPi :: MonoTy -> MonoTy -> MonoTerm
  MonoLam :: MonoTerm -> MonoTerm
  MonoApp :: MonoTerm -> MonoTerm -> MonoTerm

  MonoSg :: MonoTy -> MonoTy -> MonoTerm
  MonoPair :: MonoTerm -> MonoTerm -> MonoTerm
  MonoFst :: MonoTerm -> MonoTerm
  MonoSnd :: MonoTerm -> MonoTerm

  MonoId :: MonoTy -> MonoTerm -> MonoTerm -> MonoTerm
  MonoRefl :: MonoTerm 
  MonoIdElim :: TeleSubst -> {- which var in tele -} Int -> {- motive -} MonoTy -> {- branch -} MonoTerm -> MonoTerm
  
  MonoUniv :: UnivLevel -> MonoTerm  

  MonoUnd :: MonoTy -> MonoTerm
  MonoUndIn :: MonoTerm -> MonoTerm
  MonoUndOut :: MonoTerm -> MonoTerm

  MonoTensor :: MonoTy -> MonoTy -> MonoTerm
  MonoTensorPair :: MonoTerm -> MonoTerm -> MonoTerm
  MonoTensorElim :: MonoTeleSubst -> {- which var in tele -} Int -> {- motive -} MonoTy -> {- branch -} MonoTerm -> MonoTerm

  MonoHom :: MonoTy -> MonoTy -> MonoTerm
  MonoHomLam :: MonoTerm -> MonoTerm
  MonoHomApp :: MonoTerm -> MonoTerm -> MonoTerm
  deriving (Show, Eq)
