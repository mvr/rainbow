{-# LANGUAGE GADTs #-}
module Syntax where

import Palette

type UnivLevel = Int
  -- deriving (Show, Eq)
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
  -- IdElimSimple :: 
  -- IdElim :: Palette -> [(ColourIndex, Ty)] -> TeleSubst -> {- which var in tele -} Int -> {- motive -} Ty -> {- branch -} Term -> Term
  
  Univ :: UnivLevel -> Term  

  Und :: Ty -> Term
  UndIn :: Term -> Term
  UndOut :: Term -> Term

  Tensor :: Ty -> Ty -> Term
  TensorPair :: SliceIndex -> Term -> SliceIndex -> Term -> Term 
  TensorElim :: {- target -} Term -> {- motive -} Ty -> {- branch -} Term -> Term
  TensorElimFrob :: Palette -> [(ColourIndex, Ty)] -> TeleSubst -> {- which var in tele -} Int -> {- motive -} Ty -> {- branch -} Term -> Term

  Hom :: Ty -> Ty -> Term
  HomLam :: Term -> Term
  HomApp :: SliceIndex -> Term -> SliceIndex -> Term -> Term
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
data Closure2 where
  Closure2 :: Term -> SemEnv -> Closure2
  deriving (Show, Eq)
data Closure3 where
  Closure3 :: Term -> SemEnv -> Closure3
  deriving (Show, Eq)
data ClosureT where
  ClosureT :: Term -> SemEnv -> ClosureT
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
  
  -- NIdElim :: {- mot -} ClosureT -> {- branch -} ClosureT -> {- theta -} ([Normal], {- A -} VTy, {- a1 -} Value, {- a2 -} Value, Neutral, [Normal]) -> Neutral
  
  NUndOut :: Neutral -> Neutral

  NTensorElim :: {- mot -} Closure -> 
                 {- branch -} Closure2 -> 
                 {- aty -} VTy -> 
                 {- bty -} Closure -> 
                 {- target -} Neutral -> Neutral

  NTensorElimFrob :: {- mot -} ClosureT -> 
                 {- branch -} ClosureT -> 
                 {- tele: before, tensor, after -} ([ClosureT], ClosureT, [ClosureT]) -> 
                 {- before, tensor |- after tele -}
                 {- tele sub -} ([Value], Neutral, [Value]) -> Neutral
    
  NHomApp :: Neutral -> Normal -> Neutral 
  deriving (Show, Eq)

data Normal where
  Normal :: { nfTy :: VTy, nfTerm :: Value } -> Normal 
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
