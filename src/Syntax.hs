{-# LANGUAGE GADTs #-}
module Syntax where

import Palette

type UnivLevel = Int

type Ty = Term

data Pat where
  OnePat :: Pat
  UnitPat :: Pat
  VarPat :: Ty -> Pat
  ZeroVarPat :: Ty -> Pat
  PairPat :: Pat -> Pat -> Pat
  ReflPat :: Pat -> Pat
  TensorPat :: Pat -> Pat -> Pat
  LeftUnitorPat :: Pat -> Pat
  RightUnitorPat :: Pat -> Pat
  UndInPat :: Pat -> Pat
  deriving (Show, Eq)

data PatShape where
  OneShape :: PatShape
  UnitShape :: PatShape
  VarShape :: PatShape
  ReflShape :: PatShape -> PatShape
  PairShape :: PatShape -> PatShape -> PatShape
  TensorShape :: PatShape -> PatShape -> PatShape
  LeftUnitorShape :: PatShape -> PatShape
  RightUnitorShape :: PatShape -> PatShape
  deriving (Show, Eq)

patToType :: Pat -> Ty
patToType OnePat = One
patToType UnitPat = Unit
patToType (VarPat ty) = ty
patToType (ZeroVarPat ty) = ty
patToType (PairPat p q) = Sg (patToType p) (patToType q)
patToType (TensorPat p q) = Tensor (patToType p) (patToType q)
patToType (UndInPat p) = Und (patToType p)

patToShape :: Pat -> PatShape
patToShape OnePat = OneShape
patToShape UnitPat = UnitShape
patToShape (VarPat _) = VarShape
patToShape (PairPat p q) = PairShape (patToShape p) (patToShape q)
patToShape (TensorPat p q) = TensorShape (patToShape p) (patToShape q)
patToShape (LeftUnitorPat p) = LeftUnitorShape (patToShape p)
patToShape (RightUnitorPat p) = RightUnitorShape (patToShape p)

shapeToPal :: PatShape -> Palette
shapeToPal = undefined

data Term where
  Check :: Term -> Ty -> Term

  Var :: Int -> Term -- DeBruijn indices for variables
  ZeroVar :: Int -> Term

  Univ :: UnivLevel -> Ty

  Match :: {- target -} Term ->
           {- motive -} Ty ->
                        Pat -> -- Contains the types at the variables
           {- branch -} Term ->
                        Term

  Sg :: Ty -> Ty -> Ty
  Pair :: Term -> Term -> Term
  Fst :: Term -> Term
  Snd :: Term -> Term

  One :: Ty
  OneIn :: Term

  Pi :: Ty -> Ty -> Ty
  Lam :: Term -> Term
  App :: Term -> Term -> Term

  Id :: Ty -> Term -> Term -> Ty
  Refl :: Term -> Term

  Und :: Ty -> Ty
  UndIn :: Term -> Term
  UndOut :: Term -> Term

  Tensor :: Ty -> Ty -> Ty
  TensorPair :: SlI -> Term -> SlI -> Term -> Term

  Unit :: Ty
  UnitIn :: UnitI -> Term

  Hom :: Ty -> Ty -> Ty
  HomLam :: Term -> Term
  HomApp :: SlI -> Term -> SlI -> Term -> Term
  deriving (Show, Eq)

-- The slice is the current top slice, used when going under a cartesian binder.
data SemEnv = SemEnv { semEnvTopSlice :: SlL, semEnvPal :: SemPal, semEnv :: [Value] }
  deriving ()

semEnvLength :: SemEnv -> Int
semEnvLength (SemEnv _ _ env) = length env

data SemTele = SemTele SemPal [Value]
  deriving ()

semEnvExt :: SemEnv -> [Value] -> SemEnv
semEnvExt (SemEnv s pal env) env' = (SemEnv s pal (env' ++ env))

semEnvComma :: SemEnv -> SemTele -> SemEnv
semEnvComma (SemEnv s pal env) (SemTele pal' env') = (SemEnv s (CommaSemPal pal pal') (env' ++ env))

-- semEnvTensor :: SlL -> SemEnv -> SlL -> SemTele -> SemEnv
-- semEnvTensor sl (SemEnv pal env) sr (SemTele pal' env') = (SemEnv (TensorSemPal sl pal sr pal') (env' ++ env))

data Closure where
  Closure :: Term -> SemEnv -> Closure
  ClosureFunc :: (Value -> Value) -> Closure
  deriving ()
data ClosurePat where
  ClosurePat :: Term -> SemEnv -> ClosurePat
  deriving ()

instance Show Closure where
  show (Closure term _) = "(Closure (" ++ show term ++ ") [...])"
  show (ClosureFunc _) = "(ClosureFunc [...])"

instance Show ClosurePat where show (ClosurePat term _) = "(ClosurePat (" ++ show term ++ ") [...])"

-- This is a closure containing a pattern
data PatClosure where
  PatClosure :: Pat -> SemEnv -> PatClosure
  deriving ()
instance Show PatClosure where show (PatClosure pat _) = "(PatClosure (" ++ show pat ++ ") [...])"
-- data PatHomClosure where
--   PatHomClosure :: Pat -> SemEnv -> PatHomClosure
--   deriving (Eq)
-- instance Show PatHomClosure where show (PatHomClosure pat _) = "(PatHomClosure (" ++ show pat ++ ") [...])"

type VTy = Value

data VPat where
  OneVPat :: VPat
  UnitVPat :: VPat
  VarVPat :: VTy -> VPat
  ZeroVarVPat :: VTy -> VPat
  PairVPat :: VPat -> PatClosure -> VPat
  ReflVPat :: VPat -> VPat
  TensorVPat :: VPat -> PatClosure -> VPat
  LeftUnitorVPat :: PatClosure -> VPat
  RightUnitorVPat :: VPat -> VPat
  UndInVPat :: VPat -> VPat
  deriving (Show)

data Value where
  VNeutral :: {- type -} VTy -> Neutral -> Value

  VPi :: VTy -> Closure -> Value
  VLam :: Closure -> Value

  VOne :: Value
  VOneIn :: Value

  VSg :: VTy -> Closure -> Value
  VPair :: Value -> Value -> Value

  VId :: VTy -> Value -> Value -> Value
  VRefl :: Value -> Value

  VUniv :: UnivLevel -> Value

  VUnd :: VTy -> Value
  VUndIn :: Value -> Value

  VUnit :: Value
  VUnitIn :: UnitL -> Value

  VTensor :: VTy -> Closure -> Value
  VTensorPair :: SlL -> Value -> SlL -> Value -> Value

  VHom :: VTy -> Closure -> Value
  VHomLam :: Closure -> Value
  deriving (Show)

data Neutral where
  NVar :: Int -> Neutral -- DeBruijn levels for variables
  NZeroVar :: Int -> Neutral

  NApp :: Neutral -> Normal -> Neutral
  NMatch :: {- target -} Normal ->
            {- motive -} Closure ->
                         PatShape ->
                         VPat ->
            {- branch -} ClosurePat ->
                         Neutral

  NFst :: Neutral -> Neutral
  NSnd :: Neutral -> Neutral

  NUndOut :: Neutral -> Neutral

  NHomApp :: SlL -> Neutral -> SlL -> Normal -> Neutral
  deriving (Show)

data Normal where
  Normal :: { nfTy :: VTy, nfTerm :: Value } -> Normal
  deriving ()

instance Show Normal where show (Normal _ t) = show t
