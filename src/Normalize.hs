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

lastLevel :: Value -> Int
lastLevel (VNeutral ty ne) = lastLevelNE ne
lastLevel (VPi aty bclo) = lastLevel aty `max` lastLevelClosure bclo
lastLevel (VSg aty bclo) = lastLevel aty `max` lastLevelClosure bclo
lastLevel (VTensor aty bclo) = lastLevel aty `max` lastLevelClosure bclo
lastLevel (VHom aty bclo) = lastLevel aty `max` lastLevelClosure bclo
lastLevel (VUnd aty) = lastLevel aty
lastLevel (VUndIn a) = lastLevel a
lastLevel (VPair a b) = lastLevel a `max` lastLevel b
lastLevel (VTensorPair a b) = lastLevel a `max` lastLevel b
lastLevel (VLam aclo) = lastLevelClosure aclo
lastLevel (VHomLam aclo) = lastLevelClosure aclo

lastLevelNE :: Neutral -> Int
lastLevelNE (NVar i) = i
lastLevelNE (NZeroVar i) = i
lastLevelNE (NApp f a) = lastLevelNE f `max` lastLevelNF a
lastLevelNE (NFst p) = lastLevelNE p
lastLevelNE (NSnd p) = lastLevelNE p
lastLevelNE (NUndOut p) = lastLevelNE p 
lastLevelNE (NTensorElim mot br aty bclo t)
  = lastLevelClosure mot
    `max` lastLevelClosure2 br
    `max` lastLevel aty
    `max` lastLevelClosure bclo
    `max` lastLevelNE t
lastLevelNE (NTensorElimFrob mot br (beforety, tensorclo, afterty) (before, t, after))
  = lastLevelClosureT mot
    `max` lastLevelClosureT br
    `max` (maximum $ fmap lastLevelClosureT beforety)
    `max` lastLevelClosureT tensorclo
    `max` (maximum $ fmap lastLevelClosureT afterty)
    `max` (maximum $ fmap lastLevel before)
    `max` lastLevelNE t
    `max` (maximum $ fmap lastLevel after)
lastLevelNE (NHomApp f a) = lastLevelNE f `max` lastLevelNF a

lastLevelNF :: Normal -> Int
lastLevelNF (Normal ty a) = lastLevel a

lastLevelClosure (Closure t env) = maximum (fmap lastLevel env)
lastLevelClosure2 (Closure2 t env) = maximum (fmap lastLevel env)
lastLevelClosureT (ClosureT t env) = maximum (fmap lastLevel env)

zeroBefore :: Int -> Value -> Value
zeroBefore ix (VNeutral ty ne) = VNeutral (zeroBefore ix ty) (zeroBeforeNE ix ne)
zeroBefore ix (VPi aty bclo) = VPi (zeroBefore ix aty) (zeroBeforeClosure ix bclo)
zeroBefore ix (VLam a) = VLam (zeroBeforeClosure ix a)
zeroBefore ix (VSg aty bclo) = VSg (zeroBefore ix aty) (zeroBeforeClosure ix bclo)
zeroBefore ix (VPair a b) = VPair (zeroBefore ix a) (zeroBefore ix a)
zeroBefore ix (VUniv l) = VUniv l
zeroBefore ix (VUnd ty) = VUnd (zeroBefore ix ty)
zeroBefore ix (VUndIn a) = VUndIn (zeroBefore ix a)
zeroBefore ix (VTensor aty bclo) = VTensor (zeroBefore ix aty) (zeroBeforeClosure ix bclo)
zeroBefore ix (VTensorPair a b) = VTensorPair (zeroBefore ix a) (zeroBefore ix a)
zeroBefore ix (VHom aty bclo) = VHom (zeroBefore ix aty) (zeroBeforeClosure ix bclo)
zeroBefore ix (VHomLam a) = VHomLam (zeroBeforeClosure ix a)

zeroBeforeClosure ix (Closure t env) = Closure t (fmap (zeroBefore ix) env)
zeroBeforeClosure2 ix (Closure2 t env) = Closure2 t (fmap (zeroBefore ix) env)
zeroBeforeClosureT ix (ClosureT t env) = ClosureT t (fmap (zeroBefore ix) env)

zeroBeforeNE :: Int -> Neutral -> Neutral
zeroBeforeNE ix (NVar i) | i < ix = NZeroVar i
zeroBeforeNE ix (NVar i) | otherwise = NVar i
zeroBeforeNE ix (NZeroVar i) = NZeroVar i
zeroBeforeNE ix (NApp f a) = NApp (zeroBeforeNE ix f) (zeroBeforeNF ix a)
zeroBeforeNE ix (NFst p) = NFst (zeroBeforeNE ix p)
zeroBeforeNE ix (NSnd p) = NSnd (zeroBeforeNE ix p)
zeroBeforeNE ix (NUndOut p) = NUndOut (zeroBeforeNE ix p)  
zeroBeforeNE ix (NTensorElim mot br aty bclo t)
  = NTensorElim     
    (zeroBeforeClosure ix mot) 
    (zeroBeforeClosure2 ix br)
    (zeroBefore ix aty)
    (zeroBeforeClosure ix bclo) 
    (zeroBeforeNE ix t)
zeroBeforeNE ix (NTensorElimFrob mot br (beforety, tensorclo, afterty) (before, t, after))
  = NTensorElimFrob 
    (zeroBeforeClosureT ix mot) 
    (zeroBeforeClosureT ix br)
    (fmap (zeroBeforeClosureT ix) beforety,
     zeroBeforeClosureT ix tensorclo,
     fmap (zeroBeforeClosureT ix) afterty)
    (fmap (zeroBefore ix) before, 
     zeroBeforeNE ix t,
     fmap (zeroBefore ix) after)
zeroBeforeNE ix (NHomApp f a) = NHomApp (zeroBeforeNE ix f) (zeroBeforeNF ix a)

zeroBeforeNF :: Int -> Normal -> Normal
zeroBeforeNF ix (Normal ty a) = Normal (zeroBefore ix ty) (zeroBefore ix a)

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

doClosure2 :: Closure2 -> Value -> Value -> Value
doClosure2 (Closure2 t env) a b = eval (b : a : env) t 

doClosureT :: ClosureT -> [Value] -> Value
doClosureT (ClosureT t env) as = eval (reverse as ++ env) t -- Note reverse!

doTensorElim :: Closure -> Closure2 -> Value -> Value
doTensorElim mot br (VTensorPair a b) = doClosure2 br a b
doTensorElim mot br t@(VNeutral (VTensor aty bclo) ne) = 
  VNeutral (doClosure mot t) (NTensorElim mot br aty bclo ne)
doTensorElim mot br (VNeutral ty ne) = error $ "Unexpected neutral " ++ show ty ++ "in doTensorElim"
doTensorElim mot br t = error $ "Unexpected term " ++ show t ++ "in doTensorElim"

doTensorElimFrob :: ClosureT -> ClosureT -> ([ClosureT], ClosureT, [ClosureT]) -> ([Value], Value, [Value]) -> Value
doTensorElimFrob mot br tys (before, (VTensorPair a b), after) = doClosureT br (before ++ [a, b] ++ after)
doTensorElimFrob mot br (beforety, tensorclo, afterty) (before, t@(VNeutral (VTensor _ _) ne), after) = 
  VNeutral (doClosureT mot (before ++ [t] ++ after)) (NTensorElimFrob mot br (beforety, tensorclo, afterty) (before, ne, after))
doTensorElimFrob _ _ _ (before, (VNeutral ty ne), after) = error $ "Unexpected neutral " ++ show ty ++ "in doTensorElim"
doTensorElimFrob _ _ _ (before, t, after) = error $ "Unexpected target " ++ show t ++ "in doHomApp"

-- evalTeleSub :: SemEnv -> TeleSubst -> [Value]
-- evalTeleSub = undefined

evalTeleSubAndDivide :: SemEnv -> Int -> TeleSubst -> ([Value], Value, [Value])
evalTeleSubAndDivide env idx (TeleSubst _ as) = 
  let (before, mid:after) = splitAt idx (fmap (eval env) as)
  in (before, mid, after)

evalTeleWithVarsFrom :: Int -> SemEnv -> [ClosureT] -> ([VTy], [Value])
evalTeleWithVarsFrom lev vars [] = ([], [])
evalTeleWithVarsFrom lev vars (c:cs) = 
  let ty = doClosureT c vars 
      var = makeVarVal ty lev
      (tys, vars') = evalTeleWithVarsFrom (lev+1) (var:vars) cs
  in (ty:tys, var:vars')
            
evalTeleWithVars :: Int -> [ClosureT] -> ([VTy], [Value])
evalTeleWithVars lev cs = evalTeleWithVarsFrom lev [] cs

fillTeleNormals :: Int -> [ClosureT] -> [Value] -> [Normal]
fillTeleNormals size = go size [] 
  where go _ _ [] [] = [] 
        go size env (c:cs) (v:vs) = 
          let ty = doClosureT c env
              nf = Normal ty v
          in nf : (go size (v:env) cs vs)

eval :: SemEnv -> Term -> Value
eval env (Var i) = envLookup env i
eval env (ZeroVar i) = let v =  (envLookup env i)
  in zeroBefore (lastLevel v + 1) v

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
eval env (TensorElim t mot branch) = doTensorElim (Closure mot env) (Closure2 branch env) (eval env t)
eval env (TensorElimFrob _ omega theta zidx mot br) = 
  let (beforeo, (_, zty):aftero) = splitAt zidx omega
      beforetys = fmap (flip ClosureT env . snd) beforeo
      aftertys = fmap (flip ClosureT env . snd) aftero
      zclo = ClosureT zty env
  in doTensorElimFrob (ClosureT mot env) (ClosureT br env) (beforetys, zclo, aftertys) (evalTeleSubAndDivide env zidx theta)
eval env (Hom aty bty) = VHom (eval env aty) (Closure bty env)
eval env (HomLam b) = VHomLam (Closure b env)
eval env (HomApp _ f _ a) = doHomApp (eval env f) (eval env a)

eqTy :: Int -> VTy -> VTy -> Bool
eqTy size (VUniv l1) (VUniv l2) = l1 == l2
eqTy size (VNeutral _ ne1) (VNeutral _ ne2) = eqNE size ne1 ne2
eqTy size (VUnd ty1) (VUnd ty2) = eqTy size ty1 ty2
eqTy size (VPi aty1 bclo1) (VPi aty2 bclo2) = 
  let var = makeVarVal aty1 size 
  in eqTy size aty1 aty2 &&
     eqTy (size+1) (doClosure bclo1 var) (doClosure bclo2 var) 
eqTy size (VSg aty1 bclo1) (VSg aty2 bclo2) = 
  let var = makeVarVal aty1 size 
  in eqTy size aty1 aty2 &&
     eqTy (size+1) (doClosure bclo1 var) (doClosure bclo2 var) 
eqTy size (VTensor aty1 bclo1) (VTensor aty2 bclo2) = 
  let var = makeVarVal aty1 size 
  in eqTy size aty1 aty2 &&
     eqTy (size+1) (doClosure bclo1 var) (doClosure bclo2 var)
eqTy size (VHom aty1 bclo1) (VHom aty2 bclo2) = 
  let var = makeVarVal aty1 size 
  in eqTy size aty1 aty2 &&
     eqTy (size+1) (doClosure bclo1 var) (doClosure bclo2 var)      
eqTy _ _ _ = False

eqNF :: Int -> (VTy, Value) -> (VTy, Value) -> Bool
eqNF size (VUniv _, ty1) (VUniv _, ty2) = eqTy size ty1 ty2
eqNF size (VNeutral _ _, VNeutral _ ne1) (VNeutral _ _, VNeutral _ ne2) = eqNE size ne1 ne2
eqNF size (VPi aty1 bclo1, f1) (VPi aty2 bclo2, f2) = 
  let var = makeVarVal aty1 size in
  eqNF (size + 1) (doClosure bclo1 var, doApp f1 var) (doClosure bclo2 var, doApp f2 var)
eqNF size (VSg aty1 bclo1, p1) (VSg aty2 bclo2, p2) = 
  let a1 = doFst p1
      a2 = doFst p2
      bty1 = doClosure bclo1 a1
      bty2 = doClosure bclo2 a2
      b1 = doSnd p1
      b2 = doSnd p2
  in eqNF size (aty1, a1) (aty2, a2) &&
     eqNF size (bty1, b1) (bty2, b2)
eqNF size (VUnd ty1, a1) (VUnd ty2, a2) = 
  eqNF size (ty1, doUndOut (zeroBefore size a1)) (ty2, doUndOut (zeroBefore size a2))
eqNF size (VTensor aty1 bclo1, VTensorPair a1 b1) (VTensor aty2 bclo2, VTensorPair a2 b2) = 
  let bty1 = doClosure bclo1 a1
      bty2 = doClosure bclo2 a2
  in eqNF size (aty1, a1) (aty2, a2) &&
     eqNF size (bty1, b1) (bty2, b2)
eqNF size (VTensor aty1 bclo1, VNeutral _ ne1) (VTensor aty2 bclo2, VNeutral _ ne2) = 
  eqNE size ne1 ne2
eqNF size (VHom aty1 bclo1, f1) (VHom aty2 bclo2, f2) = 
  let var = makeVarVal aty1 size in
  eqNF (size + 1) (doClosure bclo1 var, doApp f1 var) (doClosure bclo2 var, doApp f2 var)
eqNF _ _ _  = False

eqNE :: Int -> Neutral -> Neutral -> Bool
eqNE size (NVar i) (NVar j) = i == j
eqNE size (NZeroVar i) (NZeroVar j) = i == j
eqNE size (NApp f1 (Normal aty1 a1)) (NApp f2 (Normal aty2 a2)) = 
  eqNE size f1 f2 && eqNF size (aty1, a1) (aty2, a2)
eqNE size (NFst p1) (NFst p2) = eqNE size p1 p2
eqNE size (NSnd p1) (NSnd p2) = eqNE size p1 p2
eqNE size (NUndOut p1) (NUndOut p2) = eqNE size p1 p2
eqNE size (NTensorElim mot1 br1 aty1 bclo1 ne1)
          (NTensorElim mot2 br2 aty2 bclo2 ne2) =
  let avar = makeVarVal aty1 size
      bvar = makeVarVal (doClosure bclo1 avar) (size + 1)
      motvar = makeVarVal (VTensor aty1 bclo1) size
  in eqTy size aty1 aty2
     && eqTy (size+1) (doClosure bclo1 avar) (doClosure bclo2 avar)
     && eqTy (size+1) (doClosure mot1 motvar) (doClosure bclo2 motvar)
     && eqNF (size+2) (doClosure mot1 (VTensorPair avar bvar), doClosure2 br1 avar bvar) (doClosure mot2 (VTensorPair avar bvar), doClosure2 br2 avar bvar)
     && eqNE size ne1 ne2
-- I have no doubt there are at least 3 mistakes in the following
-- TODO: Should try to abstract this for the other Frob elims
eqNE size (NTensorElimFrob mot1 br1 (beforetyclos1, tensorclo1, aftertyclos1) (before1, t1, after1))
          (NTensorElimFrob mot2 br2 (beforetyclos2, tensorclo2, aftertyclos2) (before2, t2, after2)) =
  let (beforetys1, beforevars1) = evalTeleWithVars size beforetyclos1
      tensorty1@(VTensor aty1 bclo1) = doClosureT tensorclo1 beforevars1
      -- The environment to check the motive
      tensorvar1 = makeVarVal tensorty1 (size + length beforetys1)
      (aftertys1, aftervars1) = evalTeleWithVarsFrom (size + length beforetys1 + 1) (beforevars1 ++ [tensorvar1]) aftertyclos1
      -- The environment to check the branch
      avar1 = makeVarVal aty1 (size + length beforetys1)
      bty1 = doClosure bclo1 avar1
      bvar1 = makeVarVal bty1 (size + length beforetys1 + 1)
      (aftertysbr1, aftervarssub1) = evalTeleWithVarsFrom (size + length beforetys1 + 2) (beforevars1 ++ [VTensorPair avar1 bvar1]) aftertyclos1
      -- The environment to check the target
      tensortytele1 = doClosureT tensorclo1 before1 -- This is a dumb, the type gets thrown out anyway in eqNE
      telenfs1 = fillTeleNormals size (beforetyclos1 ++ [tensorclo1] ++ aftertyclos1) (before1 ++ [VNeutral tensortytele1 t1] ++ after1) 

      (beforetys2, beforevars2) = evalTeleWithVars size beforetyclos2
      tensorty2@(VTensor aty2 bclo2) = doClosureT tensorclo2 beforevars2
      tensorvar2 = makeVarVal tensorty2 (size + length beforetys2)
      (aftertys2, aftervars2) = evalTeleWithVarsFrom (size + length beforetys2 + 1) (beforevars2 ++ [tensorvar2]) aftertyclos2
  
      avar2 = makeVarVal aty2 (size + length beforetys2)
      bty2 = doClosure bclo1 avar2
      bvar2 = makeVarVal bty2 (size + length beforetys2 + 1)
      (aftertysbr2, aftervarssub2) = evalTeleWithVarsFrom (size + length beforetys2 + 2) (beforevars2 ++ [VTensorPair avar2 bvar2]) aftertyclos2

      tensortytele2 = doClosureT tensorclo2 before2
      telenfs2 = fillTeleNormals size (beforetyclos2 ++ [tensorclo2] ++ aftertyclos2) (before2 ++ [VNeutral tensortytele2 t2] ++ after2) 
  in -- Check the telescope types match. Use the variables from 1
    and (fmap (\(i, ty1, ty2) -> eqTy i ty1 ty2) (zip3 [size..] beforetys1 beforetys2))
    && eqTy (size + length beforetys1) aty1 aty2
    && eqTy (size + length beforetys1 + 1) bty1 bty2
    && and (fmap (\(i, ty1, ty2) -> eqTy i ty1 ty2) (zip3 [(size + length beforetys1 + 1)..] aftertys1 aftertys2))
     -- Check motive
    && eqTy (size + length beforetys1 + 1 + length aftertys1) 
            (doClosureT mot1 (beforevars1 ++ [tensorvar1] ++ aftervars1))
            (doClosureT mot2 (beforevars2 ++ [tensorvar2] ++ aftervars2))
     -- Check branch  
    && eqTy (size + length beforetys1 + 2 + length aftertys1) 
            (doClosureT br1 (beforevars1 ++ [avar1, bvar1] ++ aftervarssub1))
            (doClosureT br1 (beforevars2 ++ [avar2, bvar2] ++ aftervarssub2))
     -- Check target telescope substitution  
    && and (fmap (\(Normal ty1 t1, Normal ty2 t2) -> eqNF size (ty1, t1) (ty2, t2)) (zip telenfs1 telenfs2))

eqNE size (NHomApp f1 (Normal aty1 a1)) (NHomApp f2 (Normal aty2 a2)) = 
  eqNE size f1 f2 && eqNF size (aty1, a1) (aty2, a2)
eqNE _ _ _  = False

-- normalize :: SemEnv -> Term -> Ty -> Term
-- normalize = undefined


