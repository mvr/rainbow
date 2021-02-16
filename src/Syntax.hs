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

data Pat where
  OnePat :: Pat
  UnitPat :: Pat
  VarPat :: Ty -> Pat
  PairPat :: Pat -> Pat -> Pat
  TensorPat :: Pat -> Pat -> Pat
  -- IdPat :: Pat -> Pat -> Pat
  deriving (Show, Eq)

data Term where
  Check :: Term -> Ty -> Term

  Var :: Int -> Term -- DeBruijn indices for variables
  ZeroVar :: Int -> Term

  Pi :: Ty -> Ty -> Term
  Lam :: Term -> Term
  App :: Term -> Term -> Term

  Match :: {- target -} Term ->
           -- {- type   -} Ty ->
           {- motive -} Ty ->
                        Pat ->
           {- branch -} Term ->
                        Term

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
  TensorPair :: SliceIx -> Term -> SliceIx -> Term -> Term
  -- TensorElim :: {- target -} Term -> {- motive -} Ty -> {- branch -} Term -> Term
  -- TensorElimFrob :: Palette -> [(ColourIndex, Ty)] -> TeleSubst -> {- which var in tele -} Int -> {- motive -} Ty -> {- branch -} Term -> Term

  Hom :: Ty -> Ty -> Term
  HomLam :: Pat -> Term -> Term
  HomApp :: SliceIx -> Term -> SliceIx -> Term -> Term
  deriving (Show, Eq)

data SemEnv = SemEnv SemPal [Value]
  deriving (Eq)

semEnvLength :: SemEnv -> Int
semEnvLength (SemEnv _ env) = length env

semEnvComma :: SemEnv -> SemEnv -> SemEnv
semEnvComma (SemEnv pal env) (SemEnv pal' env') = (SemEnv (cleverCommaSemPal pal pal') (env' ++ env))

semEnvTensor :: SemEnv -> SemEnv -> SemEnv
semEnvTensor (SemEnv pal env) (SemEnv pal' env') = (SemEnv (TensorSemPal pal pal') (env' ++ env))

data Closure where
  Closure :: Term -> SemEnv -> Closure
  deriving (Eq)
data Closure2 where
  Closure2 :: Term -> SemEnv -> Closure2
  deriving (Eq)
data Closure3 where
  Closure3 :: Term -> SemEnv -> Closure3
  deriving (Eq)
data ClosureT where
  ClosureT :: Term -> SemEnv -> ClosureT
  deriving (Eq)
data ClosurePat where
  ClosurePat :: Term -> SemEnv -> ClosurePat
  deriving (Eq)

instance Show Closure where show (Closure term _) = "(Closure (" ++ show term ++ ") [...])"
instance Show Closure2 where show (Closure2 term _) = "(Closure2 (" ++ show term ++ ") [...])"
instance Show Closure3 where show (Closure3 term _) = "(Closure3 (" ++ show term ++ ") [...])"
instance Show ClosureT where show (ClosureT term _) = "(ClosureT (" ++ show term ++ ") [...])"
instance Show ClosurePat where show (ClosurePat term _) = "(ClosurePat (" ++ show term ++ ") [...])"

-- This is a closure containing a pattern
data PatClosure where
  PatClosure :: Pat -> SemEnv -> PatClosure
  deriving (Eq)
instance Show PatClosure where show (PatClosure pat _) = "(PatClosure (" ++ show pat ++ ") [...])"

type VTy = Value

data VPat where
  OneVPat :: VPat
  UnitVPat :: VPat
  VarVPat :: VTy -> VPat
  PairVPat :: VPat -> PatClosure -> VPat
  TensorVPat :: VPat -> PatClosure -> VPat
  -- IdVPat :: VPat -> VPat -> VPat
  deriving (Show, Eq)

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
  VUnitIn :: UnitLvl -> Value

  VTensor :: VTy -> Closure -> Value
  VTensorPair :: SliceLvl -> Value -> SliceLvl -> Value -> Value

  VHom :: VTy -> Closure -> Value
  VHomLam :: Closure -> Value
  deriving (Show, Eq)

-- data Spine where
--   SNil :: Spine

--   SFst :: Spine -> Spine
--   SSnd :: Spine -> Spine

--   SApp :: Spine -> Normal -> Spine
--   SHomApp :: Spine -> Normal -> Spine

data StuckArg where
  SPair :: StuckArg -> StuckArg -> StuckArg
  STensor :: StuckArg -> StuckArg -> StuckArg
  SNormal :: Normal -> StuckArg
  deriving (Show, Eq)

data Neutral where
  NVar :: Int -> Neutral -- DeBruijn levels for variables
  NZeroVar :: Int -> Neutral

  NApp :: Neutral -> Normal -> Neutral
  NMatch :: {- target -} Normal ->
            {- motive -} Closure ->
                         VPat ->
            {- branch -} ClosurePat ->
                         Neutral

  -- NStuckArg :: Pat -> ClosurePat -> Value -> Neutral -- Stuck on an _argument_ that doesn't match the pattern

  NFst :: Neutral -> Neutral
  NSnd :: Neutral -> Neutral

  -- NIdElim :: {- mot -} ClosureT -> {- branch -} ClosureT -> {- theta -} ([Normal], {- A -} VTy, {- a1 -} Value, {- a2 -} Value, Neutral, [Normal]) -> Neutral

  NUndOut :: Neutral -> Neutral

  -- NTensorElim :: {- mot -} Closure ->
  --                {- branch -} Closure2 ->
  --                {- aty -} VTy ->
  --                {- bty -} Closure ->
  --                {- target -} Neutral -> Neutral

  -- NTensorElimFrob :: {- mot -} ClosureT ->
  --                {- branch -} ClosureT ->
  --                {- tele: before, tensor, after -} ([ClosureT], ClosureT, [ClosureT]) ->
  --                {- before, tensor |- after tele -}
  --                {- tele sub -} ([Value], Neutral, [Value]) -> Neutral

  NHomApp :: Neutral -> Normal -> Neutral
  deriving (Show, Eq)

data Normal where
  Normal :: { nfTy :: VTy, nfTerm :: Value } -> Normal
--  deriving (Show, Eq)
  deriving (Eq)

instance Show Normal where show (Normal _ t) = show t
