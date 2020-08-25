{-# LANGUAGE GADTs #-}
module Syntax where

import Palette

data UnivLevel

data Tele
data TeleSubst

data Ty = Term

data Term where 
  Check :: Term -> Ty -> Term

  Var :: Int -> Term -- DeBruijn indices for variables

  Pi :: Ty -> Ty -> Term
  Lam :: Term -> Term
  App :: Term -> Term -> Term

  Sg :: Ty -> Ty -> Term
  Pair :: Term -> Term -> Term
  Fst :: Term -> Term
  Snd :: Term -> Term

  Id :: Ty -> Term -> Term -> Term
  Refl :: Term 
  IdElim :: Term -> Term -> Term

  Univ :: UnivLevel -> Term  

  Und :: Ty -> Term
  UndIn :: Term -> Term
  UndOut :: Term -> Term

  Tensor :: Ty -> Ty -> Term
  TensorPair :: Term -> Term -> Term
  TensorElim :: TeleSubst -> Tele -> Term -> Term

  Hom :: Ty -> Ty -> Term
  HomLam :: Term -> Term
  HomApp :: Term -> Term -> Term

type Env = [Value]

data Closure where
  Closure :: Term -> Env -> Closure
data Closure3 where
  Closure3 :: Term -> Env -> Closure3

data ClosureTele where
  ClosureTele :: Term -> Env -> ClosureTele

data Value where
  VNeutral :: Ty -> Neutral -> Value

  VPi :: Ty -> Closure -> Value
  VLam :: Closure -> Value

  VSg :: Ty -> Closure -> Value
  VPair :: Value -> Value -> Value

  VId :: Value -> Value -> Value
  VRefl :: Value -> Value

  VUniv :: UnivLevel -> Value

  VUnd :: Value -> Value
  VUndIn :: Value -> Value

  VTensor :: Value -> Value -> Value
  VTensorPair :: Value -> Value -> Value

  VHomLam :: Closure -> Value

data Neutral where
  NVar :: Int -> Neutral -- DeBruijn levels for variables

  NApp :: Neutral -> Normal -> Neutral

  NFst :: Neutral -> Neutral
  NSnd :: Neutral -> Neutral

  -- Actually Frobenius elim for this too? 
  NIdElim :: Closure3 -> Closure -> Value -> Value -> Value -> Neutral -- F, f, A, a1, a2, e
  
  NUndOut :: Neutral -> Neutral

  NTensorElim :: ClosureTele -> ClosureTele -> [Value] -> Neutral -- F, f, theta, e
    
  NHomApp :: Neutral -> Normal -> Neutral 
  
data Normal where
  Normal :: Value -> Value -> Normal -- tp, tm

-- eval :: 
