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
  zero (VTensorPair asl a bsl b) = VTensorPair (SlL 0 OneSl) (zero a) (SlL 0 OneSl) (zero b)
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
  zero (NHomApp fsl f asl a) = NHomApp (SlL 0 OneSl) (zero f) (SlL 0 OneSl) (zero a)

instance Zero Normal where
  zero (Normal ty a) = Normal (zero ty) (zero a)

--------------------------------------------------------------------------------
-- Evaluation

envLookup :: SemEnv -> Int -> Value
envLookup (SemEnv _ env) i = env !! i

envLookupSlice :: SemEnv -> SlI -> SlL
envLookupSlice (SemEnv pal _) s = lookupSlice pal s

envLookupUnit :: SemEnv -> UnitI -> UnitL
envLookupUnit (SemEnv pal _) u = lookupUnit pal u

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

doHomApp :: SlL -> Value -> SlL -> Value -> Value
doHomApp fsl (VLam clos) asl a = doHomClosure fsl clos asl a
doHomApp fsl (VNeutral (VPi aty bclo) ne) asl a =
  let bty = doHomClosure fsl bclo asl a in
    VNeutral bty (NHomApp fsl ne asl (Normal aty a))
doHomApp _ (VNeutral ty ne) _ a = error $ "Unexpected neutral " ++ show ty ++ "in doHomApp"
doHomApp _ t _ a = error $ "Unexpected term " ++ show t ++ "in doHomApp"

doMatch :: Value -> Closure -> PatShape -> VPat -> ClosurePat -> Value
doMatch a mot patsh pat br = case matchPat patsh a of
  Just env' -> doClosurePat br env'
  Nothing   -> VNeutral (doClosure mot a) (NMatch (Normal (recoverPatType pat) a) mot patsh pat br)

recoverPatType :: VPat -> VTy
recoverPatType OneVPat = VOne
recoverPatType UnitVPat = VUnit
recoverPatType (VarVPat ty) = ty
recoverPatType (ZeroVarVPat ty) = ty
recoverPatType (PairVPat p (PatClosure q env)) = VSg (recoverPatType p) (Closure (patToType q) env)
recoverPatType (ReflVPat p) = let pty = (recoverPatType p) in
  VSg pty (ClosureFunc (\x -> VSg pty (ClosureFunc (\y -> VId pty x y))))
recoverPatType (TensorVPat p (PatClosure q env)) = VTensor (recoverPatType p) (Closure (patToType q) env)
recoverPatType (LeftUnitorVPat (PatClosure p env)) = VTensor VUnit (Closure (patToType p) env)
recoverPatType (RightUnitorVPat p) = VTensor (recoverPatType p) (ClosureFunc $ \_ -> VUnit)
recoverPatType (UndInVPat p) = VUnd (recoverPatType p)

-- WARNING: this has to give the variables in reverse order in the end: youngest first
matchPat :: PatShape -> Value -> Maybe SemTele
matchPat OneShape VOneIn = pure (SemTele OneSemPal [])
matchPat UnitShape (VUnitIn l) = pure (SemTele (UnitSemPal l) [])
matchPat (PairShape p q) (VPair a b) = do
  aenv@(SemTele apal avars) <- matchPat p a
  (SemTele bpal bvars) <- matchPat q b
  return (SemTele (CommaSemPal apal bpal) (bvars ++ avars))
matchPat (TensorShape p q) (VTensorPair sl a sr b) = do
  aenv@(SemTele apal avars) <- matchPat p a
  (SemTele bpal bvars) <- matchPat q b -- OK what happens here? What environment is q evaluated in?
  return (SemTele (TensorSemPal sl apal sr bpal) (bvars ++ avars))
matchPat _ _ = undefined

evalPat :: SemEnv -> Pat -> VPat
evalPat env OnePat = OneVPat
evalPat env UnitPat = UnitVPat
evalPat env (VarPat ty) = VarVPat (eval env ty)
evalPat env (ZeroVarPat ty) = ZeroVarVPat (eval env ty)
evalPat env (PairPat p q) = PairVPat (evalPat env p) (PatClosure q env)
evalPat env (ReflPat p) = ReflVPat (evalPat env p)
evalPat env (TensorPat p q) = TensorVPat (evalPat env p) (PatClosure q env)
evalPat env (LeftUnitorPat p) = LeftUnitorVPat (PatClosure p env)
evalPat env (RightUnitorPat p) = RightUnitorVPat (evalPat env p)
evalPat env (UndInPat p) = UndInVPat (evalPat env p)

doClosure :: Closure -> Value -> Value
doClosure (Closure t (SemEnv pal env)) a = eval (SemEnv pal (a : env)) t
doClosure (ClosureFunc f) a = f a

doHomClosure :: SlL -> Closure -> SlL -> Value -> Value
doHomClosure csl (Closure t (SemEnv pal env)) asl a = eval (SemEnv (TensorSemPal csl pal asl OneSemPal) (a : env)) t
doHomClosure _ (ClosureFunc f) _ a = f a

doClosurePat :: ClosurePat -> SemTele -> Value
doClosurePat (ClosurePat t env) env' = eval (semEnvComma env env') t

-- doClosurePatVarsOnly :: ClosurePat -> [Value] -> Value
-- doClosurePatVarsOnly (ClosurePat t env) env' = eval (semEnvComma env env') t

doPatClosure :: PatClosure -> [Value] -> VPat
doPatClosure (PatClosure t env) env' = evalPat (semEnvExt env env') t

eval :: SemEnv -> Term -> Value
-- eval env t | traceShow t False = undefined
eval env (Var i) = envLookup env i
eval env (ZeroVar i) = zero (envLookup env i)

eval env (Univ l) = VUniv l

eval env (Check t _) = eval env t

eval env (Pi aty bty) = VPi (eval env aty) (Closure bty env)
eval env (Lam b) = VLam (Closure b env)
eval env (App f a) = doApp (eval env f) (eval env a)

eval env (Match a mot pat branch) = doMatch (eval env a) (Closure mot env) (patToShape pat) (evalPat env pat) (ClosurePat branch env)

eval env (Sg aty bty) = VSg (eval env aty) (Closure bty env)
eval env (Pair a b) = VPair (eval env a) (eval env b)
eval env (Fst p) = doFst (eval env p)
eval env (Snd p) = doSnd (eval env p)

eval env (Id aty a b) = VId (eval env aty) (eval env a) (eval env b)
eval env (Refl a) = VRefl (eval env a)

eval env (Und ty) = VUnd (eval env ty)
eval env (UndIn a) = VUndIn (eval env a)
eval env (UndOut a) = doUndOut (eval env a)

eval env (Tensor aty bty) = VTensor (eval env aty) (Closure bty env)
eval env (TensorPair asl a bsl b) = VTensorPair (envLookupSlice env asl) (eval env a) (envLookupSlice env bsl) (eval env b)
eval env Unit = VUnit
eval env (UnitIn u) = VUnitIn (envLookupUnit env u)
eval env (Hom aty bty) = VHom (eval env aty) (Closure bty env)
eval env (HomLam b) = VHomLam (Closure b env)
eval env (HomApp fsl f asl a) = doHomApp (envLookupSlice env fsl) (eval env f) (envLookupSlice env asl) (eval env a)

-- evalCartPatToPal :: SemPal -> Pat -> SemPal -- Really a `SemPalExt`
-- evalCartPatToPal pal OnePat = undefined

--------------------------------------------------------------------------------
-- Equality

data Size = Size {- pal left depth -} Int {- ctx length -} Int

extSize :: Size -> SemTele -> Size
extSize (Size depth size) (SemTele pal env) = (Size (depth + 1) (size + length env))
-- FIXME: Clever comma:
-- extSize (Size depth size) (SemEnv pal env) = (Size (depth + palbit pal) (size + length env))
--   where palbit OneSemPal = 0 -- For the smart comma constructor
--         palbit _ = 1

extSizeEnv :: Size -> [Value] -> Size
extSizeEnv (Size depth size) l = (Size depth (size + length l))

extSizeLam :: Size -> Size
extSizeLam (Size depth size) = Size depth (size + 1)

pathToSlice :: PatPath -> SlI
pathToSlice p = go (reverse p)
  where go [] = IdSl
        go (LeftCommaPath : p) = CommaSl (Sub $ go p) No
        go (RightCommaPath : p) = CommaSl No (Sub $ go p)
        go (LeftTensorPath : p) = TensorSl (Sub $ go p) No
        go (RightTensorPath : p) = TensorSl No (Sub $ go p)

makeUnitVal :: Size -> PatPath -> UnitL
makeUnitVal (Size depth _) _ = undefined

makeSliceVal :: Size -> PatPath -> SlL
makeSliceVal (Size depth _ ) path = SlL depth (pathToSlice path)

makeVarVal :: VTy -> {- level -} Int -> Value
makeVarVal ty lev = VNeutral ty (NVar lev)

makeVarValS :: VTy -> {- level -} Size -> Value
makeVarValS ty (Size _ lev) = VNeutral ty (NVar lev)

makeZeroVarValS :: VTy -> {- level -} Size -> Value -- FIXME: should this zero `ty` or assume it is zeroed?
makeZeroVarValS ty (Size _ lev) = VNeutral ty (NZeroVar lev)

-- FIXME: Should we be calculating the palette extension first? In
-- this function we may be able to get away with doing it as we go.

makePatPal :: Size -> PatPath -> PatShape -> SemPal
makePatPal = undefined

-- The (Delta, p) of Delta |- p : A
makeVPatTele :: Size -> PatPath -> VPat -> ([Value], Value)
makeVPatTele size path (VarVPat ty) =
  let v = makeVarValS ty size
      i = pathToSlice path
  in ([v], v)
makeVPatTele size _ OneVPat = ([], VOneIn)
makeVPatTele size path UnitVPat = let u = makeUnitVal size path in ([], VUnitIn u)
makeVPatTele size path (PairVPat p q) =
  let (ptele, pterm) = makeVPatTele size (LeftCommaPath : path) p
      (qtele, qterm) = makeVPatTele (size `extSizeEnv` ptele) (RightCommaPath : path) (doPatClosure q ptele)
  in (qtele ++ ptele, VPair pterm qterm)
makeVPatTele size path (ReflVPat p) =
  let (ptele, pterm) = makeVPatTele size path p
  in (ptele, VPair pterm (VPair pterm (VRefl pterm)))
makeVPatTele size path (TensorVPat p q) =
  let psl = makeSliceVal size (LeftTensorPath : path)
      (ptele, pterm) = makeVPatTele size (LeftTensorPath : path) p
      qsl = makeSliceVal size (RightTensorPath : path)
      (qtele, qterm) = makeVPatTele (size `extSizeEnv` ptele) (RightTensorPath : path) (doPatClosure q ptele)
  in (qtele ++ ptele , VTensorPair psl pterm qsl qterm)

makeVPatCartTele :: Size -> VPat -> ([Value], Value)
makeVPatCartTele size pat = makeVPatTele size [RightCommaPath] pat

eqTy :: Size -> VTy -> VTy -> Bool
-- eqTy size ty1 ty2 | traceShow ("eqTy:", ty1, ty2) False = undefined
eqTy size (VUniv l1) (VUniv l2) = l1 == l2
eqTy size (VNeutral _ ne1) (VNeutral _ ne2) = eqNE size ne1 ne2
eqTy size (VUnd ty1) (VUnd ty2) = eqTy size ty1 ty2
eqTy size (VPi aty1 bclo1) (VPi aty2 bclo2) =
  let var = makeVarValS aty1 size
  in eqTy size aty1 aty2 &&
     eqTy (extSizeLam size) (doClosure bclo1 var) (doClosure bclo2 var)
eqTy size (VSg aty1 bclo1) (VSg aty2 bclo2) =
  let var = makeVarValS aty1 size
  in eqTy size aty1 aty2 &&
     eqTy (extSizeLam size) (doClosure bclo1 var) (doClosure bclo2 var)
eqTy size (VId aty1 a1 b1) (VId aty2 a2 b2) =
  eqTy size aty1 aty2 &&
  eqNF size (aty1, a1) (aty1, a2) &&
  eqNF size (aty1, b1) (aty1, b2)
eqTy size (VTensor aty1 bclo1) (VTensor aty2 bclo2) =
  let var = makeVarValS aty1 size
  in eqTy size aty1 aty2 &&
     eqTy (extSizeLam size) (doClosure bclo1 var) (doClosure bclo2 var)
eqTy size VUnit VUnit = True
eqTy size (VHom aty1 bclo1) (VHom aty2 bclo2) =
  let var = makeVarValS aty1 size
  in eqTy size aty1 aty2 &&
     eqTy (extSizeLam size) (doClosure bclo1 var) (doClosure bclo2 var)
eqTy _ _ _ = False

eqNF :: Size -> (VTy, Value) -> (VTy, Value) -> Bool
--eqNF size p1 p2 | traceShow ("eqNF:", p1, p2) False = undefined
eqNF size (VUniv _, ty1) (VUniv _, ty2) = eqTy size ty1 ty2
eqNF size (VNeutral _ _, VNeutral _ ne1) (VNeutral _ _, VNeutral _ ne2) = eqNE size ne1 ne2
eqNF size (VPi aty1 bclo1, f1) (VPi aty2 bclo2, f2) =
  let var = makeVarValS aty1 size in
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
  let var = makeVarValS aty1 size in
  eqNF (extSizeLam size) (doClosure bclo1 var, doApp f1 var) (doClosure bclo2 var, doApp f2 var)
eqNF _ _ _  = False

eqNE :: Size -> Neutral -> Neutral -> Bool
-- eqNE size p1 p2 | traceShow ("eqNE: ", p1, p2) False = undefined
eqNE size (NVar i) (NVar j) = i == j
eqNE size (NZeroVar i) (NZeroVar j) = i == j
eqNE size (NApp f1 (Normal aty1 a1)) (NApp f2 (Normal aty2 a2)) =
  eqNE size f1 f2 && eqNF size (aty1, a1) (aty2, a2)
eqNE size (NMatch (Normal aty1 a1) mot1 sh1 pat1 br1) (NMatch (Normal aty2 a2) mot2 sh2 pat2 br2) =
  let motvar = makeVarValS aty1 size
      pal = makePatPal size [] sh1 -- FIXME: or CommaRight?
      (patvars, patterm) = makeVPatTele size [] pat1
      pattele = SemTele pal patvars
  in  eqTy size aty1 aty2
      && eqNF size (aty1, a1) (aty2, a2)
      && eqTy (extSizeLam size) (doClosure mot1 motvar) (doClosure mot2 motvar)
      && eqNF (size `extSize` pattele) (doClosure mot1 patterm, doClosurePat br1 pattele) (doClosure mot2 patterm, doClosurePat br2 pattele)
eqNE size (NFst p1) (NFst p2) = eqNE size p1 p2
eqNE size (NSnd p1) (NSnd p2) = eqNE size p1 p2
eqNE size (NUndOut p1) (NUndOut p2) = eqNE size p1 p2

eqNE size (NHomApp fsl1 f1 asl1 (Normal aty1 a1)) (NHomApp fsl2 f2 asl2 (Normal aty2 a2)) =
  eqNE size f1 f2 && eqNF size (aty1, a1) (aty2, a2) &&
  fsl1 == fsl2 &&
  asl1 == asl2
eqNE _ _ _  = False

-- normalize :: SemEnv -> Term -> Ty -> Term
-- normalize = undefined
