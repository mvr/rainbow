module Normalize where

import Data.List (splitAt)

-- import Control.Monad.Reader
-- import Control.Monad.Except
-- import Data.Functor.Identity

import Syntax

type Err = String

-- TODO:
-- newtype NBEM a = CheckM (ReaderT SemEnv (ExceptT Err Identity) a)
--   deriving (Functor, Applicative, Monad, MonadError Err, MonadReader SemEnv)

envLookup :: SemEnv -> Int -> Value
envLookup env i = env !! i

doApp :: Value -> Value -> Value
doApp (VLam clos) a = doClosure clos a
doApp (VNeutral (VPi aty bclo) ne) a = 
  let bty = doClosure bclo a in
    VNeutral bty (NApp ne (Normal aty a))
doApp (VNeutral ty ne) a = error $ "Unexpected " ++ show ty ++ "in doApp"
doApp t a = error $ "Unexpected term " ++ show t ++ "in doApp"

doFst :: Value -> Value
doFst (VPair a _) = a
doFst (VNeutral (VSg aty _) ne) = VNeutral aty (NFst ne)
doFst (VNeutral ty ne) = error $ "Unexpected " ++ show ty ++ "in doFst"
doFst t = error $ "Unexpected term " ++ show t ++ "in doFst"

doSnd :: Value -> Value
doSnd (VPair _ b) = b
doSnd p@(VNeutral (VSg aty bclo) ne) = 
  let a = doFst p in
    VNeutral (doClosure bclo a) (NSnd ne)
doSnd (VNeutral ty ne) = error $ "Unexpected neutral " ++ show ty ++ "in doSnd"
doSnd t = error $ "Unexpected term " ++ show t ++ "in doSnd"

doUndOut :: Value -> Value
doUndOut (VUndIn a) = a
doUndOut (VNeutral (VUnd ty) ne) = VNeutral ty (NUndOut ne)
doUndOut (VNeutral ty ne) = error $ "Unexpected neutral " ++ show ty ++ "in doUndOut"
doUndOut t = error $ "Unexpected term " ++ show t ++ "in doUndOut"

doHomApp :: Value -> Value -> Value
doHomApp (VLam clos) a = doClosure clos a
doHomApp (VNeutral (VPi aty bclo) ne) a = 
  let bty = doClosure bclo a in
    VNeutral bty (NHomApp ne (Normal aty a))
doHomApp (VNeutral ty ne) a = error $ "Unexpected neutral " ++ show ty ++ "in doHomApp"
doHomApp t a = error $ "Unexpected term " ++ show t ++ "in doHomApp"

doClosure :: Closure -> Value -> Value
doClosure (Closure t env) a = eval (a : env) t 

doClosureTele :: ClosureTele -> [Value] -> Value
doClosureTele (ClosureTele t env) as = eval (as ++ env) t 

doTensorElim :: ClosureTele -> ClosureTele -> ([Value], Value, [Value]) -> Value
doTensorElim mot br (before, (VTensorPair a b), after) = doClosureTele br (before ++ [a, b] ++ after)
doTensorElim mot br (before, t@(VNeutral (VTensor aty bclo) ne), after) = 
  VNeutral (doClosureTele mot (before ++ [t] ++ after)) (NTensorElim mot br (before, ne, after)) 
doTensorElim mot br (before, (VNeutral ty ne), after) = error $ "Unexpected neutral " ++ show ty ++ "in doTensorElim"
doTensorElim mot br (before, t, after) = error $ "Unexpected target " ++ show t ++ "in doHomApp"

-- evalTeleSub :: SemEnv -> TeleSubst -> [Value]
-- evalTeleSub = undefined

evalTeleSubAndDivide :: SemEnv -> Int -> TeleSubst -> ([Value], Value, [Value])
evalTeleSubAndDivide env idx (TeleSubst _ as) = 
  let (before, mid:after) = splitAt idx (fmap (eval env) as)
  in (before, mid, after)

eval :: SemEnv -> Term -> Value
eval env (Var i) = envLookup env i
eval env (ZeroVar i) = undefined

eval env (Check t _) = eval env t

eval env (Pi aty bty) = VPi (eval env aty) (Closure bty env)
eval env (Lam b) = VLam (Closure b env)
eval env (App f a) = doApp (eval env f) (eval env a)

eval env (Sg aty bty) = VSg (eval env aty) (Closure bty env)
eval env (Pair a b) = VPair (eval env a) (eval env b)
eval env (Fst p) = doFst (eval env p)
eval env (Snd p) = doSnd (eval env p)

  -- Id :: Ty -> Term -> Term -> Term
  -- Refl :: Term 
  -- IdElim :: Palette -> [ColourIndex] -> TeleSubst -> {- which var in tele -} Int -> {- motive -} Ty -> {- branch -} Term -> Term
  
eval env (Univ l) = VUniv l

eval env (Und ty) = VUnd (eval env ty)
eval env (UndIn a) = VUndIn (eval env a)
eval env (UndOut a) = doUndOut (eval env a)

eval env (Tensor aty bty) = VTensor (eval env aty) (Closure bty env)
eval env (TensorPair _ a _ b) = VTensorPair (eval env a) (eval env b)
eval env (TensorElim _ _ theta zIdx mot branch) = doTensorElim (ClosureTele mot env) (ClosureTele branch env) (evalTeleSubAndDivide env zIdx theta)

eval env (Hom aty bty) = VHom (eval env aty) (Closure bty env)
eval env (HomLam b) = VHomLam (Closure b env)
eval env (HomApp _ f _ a) = doHomApp (eval env f) (eval env a)

eq_nf :: Int -> (VTy, Value) -> (VTy, Value) -> Bool
eq_nf size (VPi aty1 bclo1, f1) (VPi aty2 bclo2, f2) = 
  let var = makeVarVal aty1 size in
  eq_nf (size + 1) (doClosure bclo1 var, doApp f1 var) (doClosure bclo2 var, doApp f2 var)
eq_nf size (VSg aty1 bclo1, p1) (VSg aty2 bclo2, p2) = 
  let var = makeVarVal aty1 size in
  undefined
eq_nf _ _ _  = False
-- normalize :: SemEnv -> Term -> Ty -> Term
-- normalize = undefined
