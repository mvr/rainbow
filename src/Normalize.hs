module Normalize where

import Debug.Trace

import Data.List (splitAt)

-- import Control.Monad.Reader
-- import Control.Monad.Except
-- import Data.Functor.Identity

import Palette
import Syntax

type Err = String

-- TODO:
-- newtype NBEM a = CheckM (ReaderT SemEnv (ExceptT Err Identity) a)
--   deriving (Functor, Applicative, Monad, MonadError Err, MonadReader SemEnv)

--------------------------------------------------------------------------------
-- Zeroing

class Zero a where
  zero :: a -> a

instance Zero Value where
  zero (VNeutral ty ne) = VNeutral (zero ty) (zero ne)
  zero (VPi aty bclo) = VPi (zero aty) (zero bclo)
  zero (VLam a) = VLam (zero a)
  zero (VSg aty bclo) = VSg (zero aty) (zero bclo)
  zero (VPair a b) = VPair (zero a) (zero b)
  zero (VUniv l) = VUniv l
  zero (VUnd ty) = VUnd (zero ty)
  zero (VUndIn a) = VUndIn (zero a)
  zero (VTensor aty bclo) = VTensor (zero aty) (zero bclo)
  zero (VTensorPair asl a bsl b) = VTensorPair BotSliceLvl (zero a) BotSliceLvl (zero b)
  zero (VHom aty bclo) = VHom (zero aty) (zero bclo)
  zero (VHomLam a) = VHomLam (zero a)

instance Zero SemEnv where
  zero (SemEnv pal env) = SemEnv OriginSemPal (fmap zero env)

instance Zero Closure where zero (Closure t env) = Closure t (zero env)
-- zeroClosure2 (Closure2 t env) = Closure2 t (fmap zero env)
-- zeroClosureT (ClosureT t env) = ClosureT t (fmap zero env) --
instance Zero ClosurePat where zero (ClosurePat t env) = ClosurePat t (zero env)

instance Zero Neutral where
  zero (NVar i) = NZeroVar i
  zero (NZeroVar i) = NZeroVar i
  zero (NApp f a) = NApp (zero f) (zero a)
  zero (NFst p) = NFst (zero p)
  zero (NSnd p) = NSnd (zero p)
  zero (NUndOut p) = NUndOut (zero p)
  zero (NHomApp f a) = NHomApp (zero f) (zero a)

instance Zero Normal where
  zero (Normal ty a) = Normal (zero ty) (zero a)

--------------------------------------------------------------------------------
-- Evaluation

envLookup :: SemEnv -> Int -> Value
envLookup (SemEnv _ env) i = env !! i

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
doHomApp = undefined
-- doHomApp (VLam clos) a = doClosure clos a
-- doHomApp (VNeutral (VPi aty bclo) ne) a =
--   let bty = doClosure bclo a in
--     VNeutral bty (NHomApp ne (Normal aty a))
-- doHomApp (VNeutral ty ne) a = error $ "Unexpected neutral " ++ show ty ++ "in doHomApp"
-- doHomApp t a = error $ "Unexpected term " ++ show t ++ "in doHomApp"

doMatch :: Value -> Closure -> VPat -> ClosurePat -> Value
doMatch a mot pat br = case matchPat pat a of
  Just env' -> doClosurePat br env'
  Nothing   -> VNeutral (doClosure mot a) (NMatch (Normal (recoverPatType pat a) a) mot pat br)

recoverPatType :: VPat -> Value -> VTy
recoverPatType OneVPat a = VOne
recoverPatType UnitVPat a = VUnit
recoverPatType (VarVPat ty) a = ty

matchPat :: VPat -> Value -> Maybe SemEnv
matchPat OneVPat VOneIn = Just (SemEnv OneSemPal [])
matchPat UnitVPat (VUnitIn l) = Just (SemEnv (UnitSemPal l) [])
matchPat _ _ = undefined

evalPat :: SemEnv -> Pat -> VPat
evalPat env OnePat = OneVPat
evalPat env UnitPat = UnitVPat
evalPat env (VarPat ty) = VarVPat (eval env ty)
evalPat env (PairPat p q) = PairVPat (evalPat env p) (PatClosure q env)
evalPat env (TensorPat p q) = undefined --
evalPat env p = undefined

doClosure :: Closure -> Value -> Value
doClosure (Closure t (SemEnv pal env)) a = eval (SemEnv pal (a : env)) t

-- doClosure2 :: Closure2 -> Value -> Value -> Value
-- doClosure2 (Closure2 t env) a b = eval (b : a : env) t

-- doClosureT :: ClosureT -> [Value] -> Value
-- doClosureT (ClosureT t env) as = eval (reverse as ++ env) t -- Note reverse! -- TODO: let's not do this...

doClosurePat :: ClosurePat -> SemEnv -> Value
doClosurePat (ClosurePat t env) env' = eval (semEnvComma env env') t

doPatClosure :: PatClosure -> SemEnv  -> VPat
doPatClosure (PatClosure t env) env' = evalPat (semEnvComma env env') t

-- doTensorElim :: Closure -> Closure2 -> Value -> Value
-- doTensorElim mot br t | traceShow ("doing tensor elim on: " ++ show (mot, br, t)) False = undefined
-- doTensorElim mot br (VTensorPair a b) = doClosure2 br a b
-- doTensorElim mot br t@(VNeutral (VTensor aty bclo) ne) =
--   VNeutral (doClosure mot t) (NTensorElim mot br aty bclo ne)
-- doTensorElim mot br (VNeutral ty ne) = error $ "Unexpected neutral " ++ show ty ++ "in doTensorElim"
-- doTensorElim mot br t = error $ "Unexpected term " ++ show t ++ "in doTensorElim"

-- doTensorElimFrob :: ClosureT -> ClosureT -> ([ClosureT], ClosureT, [ClosureT]) -> ([Value], Value, [Value]) -> Value
-- doTensorElimFrob mot br tys (before, (VTensorPair a b), after) = doClosureT br (before ++ [a, b] ++ after)
-- doTensorElimFrob mot br (beforety, tensorclo, afterty) (before, t@(VNeutral (VTensor _ _) ne), after) =
--   VNeutral (doClosureT mot (before ++ [t] ++ after)) (NTensorElimFrob mot br (beforety, tensorclo, afterty) (before, ne, after))
-- doTensorElimFrob _ _ _ (before, (VNeutral ty ne), after) = error $ "Unexpected neutral " ++ show ty ++ "in doTensorElim"
-- doTensorElimFrob _ _ _ (before, t, after) = error $ "Unexpected target " ++ show t ++ "in doHomApp"

-- evalTeleSub :: SemEnv -> TeleSubst -> [Value]
-- evalTeleSub = undefined

-- evalTeleSubAndDivide :: SemEnv -> Int -> TeleSubst -> ([Value], Value, [Value])
-- evalTeleSubAndDivide env idx (TeleSubst _ as) =
--   let (before, mid:after) = splitAt idx (fmap (eval env) as)
--   in (before, mid, after)

-- evalTeleWithVarsFrom :: Int -> SemEnv -> [ClosureT] -> ([VTy], [Value])
-- evalTeleWithVarsFrom lev vars [] = ([], [])
-- evalTeleWithVarsFrom lev vars (c:cs) =
--   let ty = doClosureT c vars
--       var = makeVarVal ty lev
--       (tys, vars') = evalTeleWithVarsFrom (lev+1) (var:vars) cs
--   in (ty:tys, var:vars')

-- evalTeleWithVars :: Int -> [ClosureT] -> ([VTy], [Value])
-- evalTeleWithVars lev cs = evalTeleWithVarsFrom lev [] cs

-- fillTeleNormals :: Int -> [ClosureT] -> [Value] -> [Normal]
-- fillTeleNormals size = go size []
--   where go _ _ [] [] = []
--         go size env (c:cs) (v:vs) =
--           let ty = doClosureT c env
--               nf = Normal ty v
--           in nf : (go size (v:env) cs vs)

restrictSemEnv :: SliceIx -> SemEnv -> SemEnv
restrictSemEnv = undefined

evalSlice :: SemEnv -> SliceIx -> SliceLvl
evalSlice = undefined

eval :: SemEnv -> Term -> Value
eval env (Var i) = envLookup env i
eval env (ZeroVar i) = zero (envLookup env i)

eval env (Check t _) = eval env t

eval env (Pi aty bty) = VPi (eval env aty) (Closure bty env)
eval env (Lam b) = VLam (Closure b env)
eval env (App f a) = doApp (eval env f) (eval env a)

eval env (Match a mot pat branch) = doMatch (eval env a) (Closure mot env) (evalPat env pat) (ClosurePat branch env)

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
eval env (TensorPair asl a bsl b) = VTensorPair (evalSlice env asl) (eval (restrictSemEnv asl env) a) (evalSlice env bsl) (eval (restrictSemEnv bsl env) b)
-- eval env (TensorElim t mot branch) = doTensorElim (Closure mot env) (Closure2 branch env) (let r = eval env t in traceShow (t, r) r)
-- eval env (TensorElimFrob _ omega theta zidx mot br) =
--   let (beforeo, (_, zty):aftero) = splitAt zidx omega
--       beforetys = fmap (flip ClosureT env . snd) beforeo
--       aftertys = fmap (flip ClosureT env . snd) aftero
--       zclo = ClosureT zty env
--   in doTensorElimFrob (ClosureT mot env) (ClosureT br env) (beforetys, zclo, aftertys) (evalTeleSubAndDivide env zidx theta)
eval env (Hom aty bty) = VHom (eval env aty) (Closure bty env)
eval env (HomLam pat b) = undefined -- VHomLam (Closure b env)
eval env (HomApp _ f _ a) = doHomApp (eval env f) (eval env a)

--------------------------------------------------------------------------------
-- Equality

data Size = Size {- ctx length -} Int {- pal left depth -} Int

extSize :: Size -> SemEnv -> Size
extSize (Size depth size) (SemEnv pal env) = (Size (depth + palbit pal) (size + length env))
  where palbit OneSemPal = 0 -- For the smart comma constructor
        palbit _ = 1

extSizeLam :: Size -> Size
extSizeLam (Size depth size) = Size depth (size + 1)

data VPatPath where
  StartPath :: VPatPath
  LeftCommaPath :: VPatPath -> VPatPath
  RightCommaPath :: VPatPath -> VPatPath
  LeftTensorPath :: VPatPath -> VPatPath
  RightTensorPath :: VPatPath -> VPatPath

makeUnitVal :: Size -> VPatPath -> UnitLvl
makeUnitVal (Size depth _) _ = undefined


makeVarVal :: VTy -> {- level -} Size -> Value
makeVarVal ty (Size _ lev) = VNeutral ty (NVar lev)

-- The (Delta, p) of Delta |- p : A
makePatTele :: Size -> VPatPath -> VPat -> (SemEnv, Value)
makePatTele size _ (VarVPat ty) = let v = makeVarVal ty size in (SemEnv OneSemPal [v], v)
makePatTele size _ OneVPat = (SemEnv OneSemPal [], VOneIn)
makePatTele size path UnitVPat = let u = makeUnitVal size path in (SemEnv (UnitSemPal u) [], VUnitIn u)
makePatTele size path (PairVPat p q) =
  let (ptele, pterm) = makePatTele size (LeftCommaPath path) p
      (qtele, qterm) = makePatTele (size `extSize` ptele) (RightCommaPath path) (doPatClosure q ptele)
  in (semEnvComma ptele qtele, VPair pterm qterm)
makePatTele size path (TensorVPat p q) =
  let (ptele, pterm) = makePatTele size (LeftTensorPath path) p
      (qtele, qterm) = makePatTele (size `extSize` ptele) (RightTensorPath path) (doPatClosure q ptele)
  in (semEnvTensor ptele qtele, VTensorPair pterm qterm)



eqTy :: Size -> VTy -> VTy -> Bool
-- eqTy size ty1 ty2 | traceShow ("eqTy:", ty1, ty2) False = undefined
eqTy size (VUniv l1) (VUniv l2) = l1 == l2
eqTy size (VNeutral _ ne1) (VNeutral _ ne2) = eqNE size ne1 ne2
eqTy size (VUnd ty1) (VUnd ty2) = eqTy size ty1 ty2
eqTy size (VPi aty1 bclo1) (VPi aty2 bclo2) =
  let var = makeVarVal aty1 size
  in eqTy size aty1 aty2 &&
     eqTy (extSizeLam size) (doClosure bclo1 var) (doClosure bclo2 var)
eqTy size (VSg aty1 bclo1) (VSg aty2 bclo2) =
  let var = makeVarVal aty1 size
  in eqTy size aty1 aty2 &&
     eqTy (extSizeLam size) (doClosure bclo1 var) (doClosure bclo2 var)
eqTy size (VTensor aty1 bclo1) (VTensor aty2 bclo2) =
  let var = makeVarVal aty1 size
  in eqTy size aty1 aty2 &&
     eqTy (extSizeLam size) (doClosure bclo1 var) (doClosure bclo2 var)
eqTy size (VHom aty1 bclo1) (VHom aty2 bclo2) =
  let var = makeVarVal aty1 size
  in eqTy size aty1 aty2 &&
     eqTy (extSizeLam size) (doClosure bclo1 var) (doClosure bclo2 var)
eqTy _ _ _ = False

eqNF :: Size -> (VTy, Value) -> (VTy, Value) -> Bool
--eqNF size p1 p2 | traceShow ("eqNF:", p1, p2) False = undefined
eqNF size (VUniv _, ty1) (VUniv _, ty2) = eqTy size ty1 ty2
eqNF size (VNeutral _ _, VNeutral _ ne1) (VNeutral _ _, VNeutral _ ne2) = eqNE size ne1 ne2
eqNF size (VPi aty1 bclo1, f1) (VPi aty2 bclo2, f2) =
  let var = makeVarVal aty1 size in
  eqNF (extSizeLam size) (doClosure bclo1 var, doApp f1 var) (doClosure bclo2 var, doApp f2 var)
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
  eqNF size (ty1, doUndOut (zero a1)) (ty2, doUndOut (zero a2))
eqNF size (VTensor aty1 bclo1, VTensorPair sl1 a1 sr1 b1) (VTensor aty2 bclo2, VTensorPair sl2 a2 sr2 b2) =
  let bty1 = doClosure bclo1 a1
      bty2 = doClosure bclo2 a2
  in eqNF size (aty1, a1) (aty2, a2) &&
     eqNF size (bty1, b1) (bty2, b2) &&
     sl1 == sl2 &&
     sr1 == sr2
eqNF size (VTensor aty1 bclo1, VNeutral _ ne1) (VTensor aty2 bclo2, VNeutral _ ne2) =
  eqNE size ne1 ne2
eqNF size (VHom aty1 bclo1, f1) (VHom aty2 bclo2, f2) =
  let var = makeVarVal aty1 size in
  eqNF (extSizeLam size) (doClosure bclo1 var, doApp f1 var) (doClosure bclo2 var, doApp f2 var)
eqNF _ _ _  = False

eqNE :: Size -> Neutral -> Neutral -> Bool
-- eqNE size p1 p2 | traceShow ("eqNE: ", p1, p2) False = undefined
eqNE size (NVar i) (NVar j) = i == j
eqNE size (NZeroVar i) (NZeroVar j) = i == j
eqNE size (NApp f1 (Normal aty1 a1)) (NApp f2 (Normal aty2 a2)) =
  eqNE size f1 f2 && eqNF size (aty1, a1) (aty2, a2)
eqNE size (NMatch (Normal aty1 a1) mot1 pat1 br1) (NMatch (Normal aty2 a2) mot2 pat2 br2) =
  let motvar = makeVarVal aty1 size
      (pattele, patterm) = makePatTele size StartPath pat1
  in  eqTy size aty1 aty2
      && eqNF size (aty1, a1) (aty2, a2)
      && eqTy (extSizeLam size) (doClosure mot1 motvar) (doClosure mot2 motvar)
      && eqNF (size `extSize` pattele) (doClosure mot1 patterm, doClosurePat br1 pattele) (doClosure mot2 patterm, doClosurePat br2 pattele)
eqNE size (NFst p1) (NFst p2) = eqNE size p1 p2
eqNE size (NSnd p1) (NSnd p2) = eqNE size p1 p2
eqNE size (NUndOut p1) (NUndOut p2) = eqNE size p1 p2

-- eqNE size (NTensorElim mot1 br1 aty1 bclo1 ne1)
--           (NTensorElim mot2 br2 aty2 bclo2 ne2) =
--   let avar = makeVarVal aty1 size
--       bvar = makeVarVal (doClosure bclo1 avar) (size + 1)
--       motvar = makeVarVal (VTensor aty1 bclo1) size
--   in eqTy size aty1 aty2
--      && eqTy (size+1) (doClosure bclo1 avar) (doClosure bclo2 avar)
--      && eqTy (size+1) (doClosure mot1 motvar) (doClosure mot2 motvar)
--      && eqNF (size+2) (doClosure mot1 (VTensorPair avar bvar), doClosure2 br1 avar bvar) (doClosure mot2 (VTensorPair avar bvar), doClosure2 br2 avar bvar)
--      && eqNE size ne1 ne2
-- I have no doubt there are at least 3 mistakes in the following
-- TODO: Should try to abstract this for the other Frob elims
-- eqNE size (NTensorElimFrob mot1 br1 (beforetyclos1, tensorclo1, aftertyclos1) (before1, t1, after1))
--           (NTensorElimFrob mot2 br2 (beforetyclos2, tensorclo2, aftertyclos2) (before2, t2, after2)) =
--   let (beforetys1, beforevars1) = evalTeleWithVars size beforetyclos1
--       tensorty1@(VTensor aty1 bclo1) = doClosureT tensorclo1 beforevars1
--       -- The environment to check the motive
--       tensorvar1 = makeVarVal tensorty1 (size + length beforetys1)
--       (aftertys1, aftervars1) = evalTeleWithVarsFrom (size + length beforetys1 + 1) (beforevars1 ++ [tensorvar1]) aftertyclos1
--       -- The environment to check the branch
--       avar1 = makeVarVal aty1 (size + length beforetys1)
--       bty1 = doClosure bclo1 avar1
--       bvar1 = makeVarVal bty1 (size + length beforetys1 + 1)
--       (aftertysbr1, aftervarssub1) = evalTeleWithVarsFrom (size + length beforetys1 + 2) (beforevars1 ++ [VTensorPair avar1 bvar1]) aftertyclos1
--       -- The environment to check the target
--       tensortytele1 = doClosureT tensorclo1 before1 -- This is a dumb, the type gets thrown out anyway in eqNE
--       telenfs1 = fillTeleNormals size (beforetyclos1 ++ [tensorclo1] ++ aftertyclos1) (before1 ++ [VNeutral tensortytele1 t1] ++ after1)

--       (beforetys2, beforevars2) = evalTeleWithVars size beforetyclos2
--       tensorty2@(VTensor aty2 bclo2) = doClosureT tensorclo2 beforevars2
--       tensorvar2 = makeVarVal tensorty2 (size + length beforetys2)
--       (aftertys2, aftervars2) = evalTeleWithVarsFrom (size + length beforetys2 + 1) (beforevars2 ++ [tensorvar2]) aftertyclos2

--       avar2 = makeVarVal aty2 (size + length beforetys2)
--       bty2 = doClosure bclo1 avar2
--       bvar2 = makeVarVal bty2 (size + length beforetys2 + 1)
--       (aftertysbr2, aftervarssub2) = evalTeleWithVarsFrom (size + length beforetys2 + 2) (beforevars2 ++ [VTensorPair avar2 bvar2]) aftertyclos2

--       tensortytele2 = doClosureT tensorclo2 before2
--       telenfs2 = fillTeleNormals size (beforetyclos2 ++ [tensorclo2] ++ aftertyclos2) (before2 ++ [VNeutral tensortytele2 t2] ++ after2)
--   in -- Check the telescope types match. Use the variables from 1
--     and (fmap (\(i, ty1, ty2) -> eqTy i ty1 ty2) (zip3 [size..] beforetys1 beforetys2))
--     && eqTy (size + length beforetys1) aty1 aty2
--     && eqTy (size + length beforetys1 + 1) bty1 bty2
--     && and (fmap (\(i, ty1, ty2) -> eqTy i ty1 ty2) (zip3 [(size + length beforetys1 + 1)..] aftertys1 aftertys2))
--      -- Check motive
--     && eqTy (size + length beforetys1 + 1 + length aftertys1)
--             (doClosureT mot1 (beforevars1 ++ [tensorvar1] ++ aftervars1))
--             (doClosureT mot2 (beforevars2 ++ [tensorvar2] ++ aftervars2))
--      -- Check branch
--     && eqTy (size + length beforetys1 + 2 + length aftertys1)
--             (doClosureT br1 (beforevars1 ++ [avar1, bvar1] ++ aftervarssub1))
--             (doClosureT br1 (beforevars2 ++ [avar2, bvar2] ++ aftervarssub2))
--      -- Check target telescope substitution
--     && and (fmap (\(Normal ty1 t1, Normal ty2 t2) -> eqNF size (ty1, t1) (ty2, t2)) (zip telenfs1 telenfs2))

eqNE size (NHomApp f1 (Normal aty1 a1)) (NHomApp f2 (Normal aty2 a2)) =
  eqNE size f1 f2 && eqNF size (aty1, a1) (aty2, a2)
eqNE _ _ _  = False

-- normalize :: SemEnv -> Term -> Ty -> Term
-- normalize = undefined
