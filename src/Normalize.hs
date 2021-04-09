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
  zero (SemEnv _ pal env) = SemEnv (SlL 0 OneSl) pal (fmap zero env)

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
envLookup (SemEnv _ _ env) i = env !! i

envLookupSlice :: SemEnv -> SlI -> SlL
envLookupSlice (SemEnv d pal _) s = lookupSlice d pal s

envLookupUnit :: SemEnv -> UnitI -> UnitL
envLookupUnit (SemEnv _ pal _) u = lookupUnit pal u

doApp :: SlL -> Value -> Value -> Value
doApp s (VLam clos) a = doClosure s clos a
doApp s (VNeutral (VPi aty bclo) ne) a =
  let bty = doClosure s bclo a in
    VNeutral bty (NApp ne (Normal aty a))
doApp _ (VNeutral ty ne) a = error $ "Unexpected " ++ show ty ++ "in doApp"
doApp _ t a = error $ "Unexpected term " ++ show t ++ "in doApp"

doFst :: Value -> Value
doFst (VPair a _) = a
doFst (VNeutral (VSg aty _) ne) = VNeutral aty (NFst ne)
doFst (VNeutral ty ne) = error $ "Unexpected " ++ show ty ++ "in doFst"
doFst t = error $ "Unexpected term " ++ show t ++ "in doFst"

doSnd :: SlL -> Value -> Value
doSnd _ (VPair _ b) = b
doSnd s p@(VNeutral (VSg aty bclo) ne) =
  let a = doFst p in
    VNeutral (doClosure s bclo a) (NSnd ne)
doSnd _ (VNeutral ty ne) = error $ "Unexpected neutral " ++ show ty ++ "in doSnd"
doSnd _ t = error $ "Unexpected term " ++ show t ++ "in doSnd"

doUndOut :: Value -> Value
doUndOut (VUndIn a) = a
doUndOut (VNeutral (VUnd ty) ne) = VNeutral ty (NUndOut ne)
doUndOut (VNeutral ty ne) = error $ "Unexpected neutral " ++ show ty ++ "in doUndOut"
doUndOut t = error $ "Unexpected term " ++ show t ++ "in doUndOut"

doHomApp :: SlL -> SlL -> Value -> SlL -> Value -> Value
doHomApp d fsl (VHomLam clos) asl a = doHomClosure d fsl clos asl a
doHomApp d fsl (VNeutral (VHom aty bclo) ne) asl a =
  let bty = doHomClosure d fsl bclo asl a in
    VNeutral bty (NHomApp fsl ne asl (Normal aty a))
doHomApp _ _ (VNeutral ty ne) _ a = error $ "Unexpected neutral " ++ show ty ++ "in doHomApp"
doHomApp _ _ t _ a = error $ "Unexpected term " ++ show t ++ " in doHomApp"

doMatch :: SlL -> Value -> Closure -> PatShape -> VPat -> ClosurePat -> Value
doMatch s a mot patsh pat br = case matchPat patsh a of
  Just env' -> doClosurePat br env'
  Nothing   -> VNeutral (doClosure s mot a) (NMatch (Normal (recoverPatType pat) a) mot patsh pat br)

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
matchPat VarShape a = pure (SemTele OneSemPal [a])
matchPat OneShape VOneIn = pure (SemTele OneSemPal [])
matchPat UnitShape (VUnitIn l) = pure (SemTele (UnitSemPal l) [])
matchPat (PairShape p q) (VPair a b) = do
  aenv@(SemTele apal avars) <- matchPat p a
  (SemTele bpal bvars) <- matchPat q b
  return (SemTele (CommaSemPal apal bpal) (bvars ++ avars))
matchPat (TensorShape p q) (VTensorPair sl a sr b) = do
  aenv@(SemTele apal avars) <- matchPat p a
  (SemTele bpal bvars) <- matchPat q b
  return (SemTele (TensorSemPal sl apal sr bpal) (bvars ++ avars))
matchPat (RightUnitorShape p) (VTensorPair _ a (SlL 0 SummonedUnitSl) (VUnitIn (UnitL 0 SummonedUnit))) = matchPat p a
matchPat (RightUnitorShape p) _ = Nothing
matchPat (LeftUnitorShape p) (VTensorPair (SlL 0 SummonedUnitSl) (VUnitIn (UnitL 0 SummonedUnit)) _ a) = matchPat p a
matchPat (LeftUnitorShape p) _ = Nothing
matchPat p v = error $ "Unhandled " ++ show (p, v)

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

-- Needs to know the top slice unfortunately.
doClosure :: SlL -> Closure -> Value -> Value
doClosure s (Closure t (SemEnv _ pal env)) a = eval (SemEnv s pal (a : env)) t
doClosure s (ClosureFunc f) a = f a

doHomClosure :: SlL -> SlL -> Closure -> SlL -> Value -> Value
doHomClosure s csl (Closure t (SemEnv d pal env)) asl a = eval (SemEnv s (TensorSemPal csl pal asl OneSemPal) (a : env)) t
doHomClosure _ _ (ClosureFunc f) _ a = f a

doClosurePat :: ClosurePat -> SemTele -> Value
doClosurePat (ClosurePat t env) env' = eval (semEnvComma env env') t

doPatClosure :: PatClosure -> [Value] -> VPat
doPatClosure (PatClosure t env) env' = evalPat (semEnvExtSilent env env') t

eval :: SemEnv -> Term -> Value
-- eval env t | traceShow t False = undefined
eval env (Var i) = envLookup env i
eval env (ZeroVar i) = zero (envLookup env i)

eval env (Univ l) = VUniv l

eval env (Check t _) = eval env t

eval env (Pi aty bty) = VPi (eval env aty) (Closure bty env)
eval env (Lam b) = VLam (Closure b env)
eval env (App f a) = doApp (semEnvTopSlice env) (eval env f) (eval env a)

eval env (Match a mot pat branch) = doMatch (semEnvTopSlice env) (eval env a) (Closure mot env) (patToShape pat) (evalPat env pat) (ClosurePat branch env)

eval env (Sg aty bty) = VSg (eval env aty) (Closure bty env)
eval env (Pair a b) = VPair (eval env a) (eval env b)
eval env (Fst p) = doFst (eval env p)
eval env (Snd p) = doSnd (semEnvTopSlice env) (eval env p)

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
eval env (HomApp fsl f asl a) = doHomApp (semEnvTopSlice env) (envLookupSlice env fsl) (eval env f) (envLookupSlice env asl) (eval env a)

--------------------------------------------------------------------------------
-- Equality

data Size = Size { sizePal :: Palette, sizeTopSlice :: SlL, sizeCtxLength :: Int }

extSizeComma :: Size -> SemTele -> Size
extSizeComma (Size palshape s size) (SemTele pal env) = (Size (CommaPal palshape (semPalToShape pal)) undefined (size + length env))

extSizeEnv :: Size -> [Value] -> Size
extSizeEnv (Size depth s size) l = (Size depth s (size + length l))

extSizeLam :: Size -> Size
extSizeLam (Size depth s size) = Size depth s (size + 1)

extSizeHomLam :: Size -> Size
extSizeHomLam (Size depth s size) = Size (TensorPal depth OnePal) (slExtHom depth s) (size + 1)

sizeTopRightSl :: Size -> SlL
sizeTopRightSl (Size pal _ _) = SlL (palDepth pal) (TensorSl No (Sub IdSl))

-- To represent where we are in a pattern
-- Note: we read a path backwards: if `(a, b), (c, d)` then
-- `b` has path RightCommaPath (LeftCommaPath StartPath)

data PatPathPiece = LeftCommaPath | RightCommaPath | LeftTensorPath | RightTensorPath | LeftUnitorPath | RightUnitorPath
  deriving (Show, Eq)

type PatPath = [PatPathPiece]

pathIsTop :: PatPath -> Bool
pathIsTop p = go (reverse p)
  where go [] = True
        go (LeftCommaPath : p) = pathIsTop p
        go (RightCommaPath : p) = pathIsTop p
        go (LeftTensorPath : p) = False
        go (RightTensorPath : p) = False

pathToSlice :: Palette -> PatPath -> SlI
pathToSlice pal p = if pathIsTop p then palTopSlice pal else go pal (reverse p)
  where go pal [] = palTopSlice pal
        go (CommaPal l r) (LeftCommaPath : p) = CommaSl (Sub $ go l p) No
        go (CommaPal l r) (RightCommaPath : p) = CommaSl No (Sub $ go r p)
        go (TensorPal l r) (LeftTensorPath : p) = TensorSl (Sub $ go l p) No
        go (TensorPal l r) (RightTensorPath : p) = TensorSl No (Sub $ go r p)

makeUnitVal :: Size -> PatPath -> UnitL
makeUnitVal (Size depth _ _) _ = undefined

makeSliceVal :: Size -> PatPath -> SlL
makeSliceVal (Size pal _ _) path = SlL (palDepth pal) (pathToSlice pal path)

makeVarVal :: VTy -> {- level -} Int -> Value
makeVarVal ty lev = VNeutral ty (NVar lev)

makeVarValS :: VTy -> {- level -} Size -> Value
makeVarValS ty (Size _ _ lev) = VNeutral ty (NVar lev)

makeZeroVarValS :: VTy -> {- level -} Size -> Value -- FIXME: should this zero `ty` or assume it is zeroed?
makeZeroVarValS ty (Size _ _ lev) = VNeutral ty (NZeroVar lev)

-- FIXME: Should we be calculating the palette extension first? In
-- this function we may be able to get away with doing it as we go.

makePatPal :: Size -> PatPath -> PatShape -> SemPal
makePatPal size path VarShape = OneSemPal
makePatPal size _ OneShape = OneSemPal
makePatPal size path UnitShape = UnitSemPal undefined
makePatPal size path (PairShape p q) = CommaSemPal (makePatPal size (LeftCommaPath : path) p) (makePatPal undefined (RightCommaPath : path) q)
makePatPal size path (ReflShape p) = makePatPal size path p
makePatPal size path (TensorShape p q) =
  let psl = makeSliceVal size (LeftTensorPath : path)
      qsl = makeSliceVal size (RightTensorPath : path)
  in TensorSemPal psl (makePatPal size (LeftTensorPath : path) p) qsl (makePatPal undefined (RightTensorPath : path) q)
makePatPal size path (LeftUnitorShape p) = makePatPal size path p
makePatPal size path (RightUnitorShape p) = makePatPal size path p

-- The (Delta, p) of Delta |- p : A
makeVPatTele :: Size -> PatPath -> VPat -> ([Value], Value)
makeVPatTele size path (VarVPat ty) =
  let v = makeVarValS ty size
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
makeVPatTele size path (LeftUnitorVPat p) =
  let (ptele, pterm) = makeVPatTele size (LeftUnitorPath : path) (doPatClosure p [VUnitIn $ UnitL 0 OneUnit])
      topSlice = makeSliceVal size path
  in (ptele, VTensorPair (SlL 0 SummonedUnitSl) (VUnitIn (UnitL 0 SummonedUnit)) topSlice pterm)
makeVPatTele size path (RightUnitorVPat p) =
  let (ptele, pterm) = makeVPatTele size (RightUnitorPath : path) p
      topSlice = makeSliceVal size path
  in (ptele, VTensorPair topSlice pterm (SlL 0 SummonedUnitSl) (VUnitIn (UnitL 0 SummonedUnit)))

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
     eqTy (extSizeLam size) (doClosure (sizeTopSlice size) bclo1 var) (doClosure (sizeTopSlice size) bclo2 var)
eqTy size (VSg aty1 bclo1) (VSg aty2 bclo2) =
  let var = makeVarValS aty1 size
  in eqTy size aty1 aty2 &&
     eqTy (extSizeLam size) (doClosure (sizeTopSlice size) bclo1 var) (doClosure (sizeTopSlice size) bclo2 var)
eqTy size (VId aty1 a1 b1) (VId aty2 a2 b2) =
  eqTy size aty1 aty2 &&
  eqNF size (aty1, a1) (aty1, a2) &&
  eqNF size (aty1, b1) (aty1, b2)
eqTy size (VTensor aty1 bclo1) (VTensor aty2 bclo2) =
  let var = makeVarValS aty1 size
  in eqTy size aty1 aty2 &&
     eqTy (extSizeLam size) (doClosure (sizeTopSlice size) bclo1 var) (doClosure (sizeTopSlice size) bclo2 var)
eqTy size VUnit VUnit = True
eqTy size (VHom aty1 bclo1) (VHom aty2 bclo2) =
  let var = makeVarValS aty1 size
  in eqTy size aty1 aty2 &&
     eqTy (extSizeLam size) (doClosure (sizeTopSlice size) bclo1 var) (doClosure (sizeTopSlice size) bclo2 var)
eqTy _ _ _ = False

eqNF :: Size -> (VTy, Value) -> (VTy, Value) -> Bool
--eqNF size p1 p2 | traceShow ("eqNF:", p1, p2) False = undefined
eqNF size (VUniv _, ty1) (VUniv _, ty2) = eqTy size ty1 ty2
eqNF size (VNeutral _ _, VNeutral _ ne1) (VNeutral _ _, VNeutral _ ne2) = eqNE size ne1 ne2
eqNF size (VPi aty1 bclo1, f1) (VPi aty2 bclo2, f2) =
  let var = makeVarValS aty1 size in
  eqNF (extSizeLam size) (doClosure (sizeTopSlice size) bclo1 var, doApp (sizeTopSlice size) f1 var) (doClosure (sizeTopSlice size) bclo2 var, doApp (sizeTopSlice size) f2 var)
eqNF size (VSg aty1 bclo1, p1) (VSg aty2 bclo2, p2) =
  let a1 = doFst p1
      a2 = doFst p2
      bty1 = doClosure (sizeTopSlice size) bclo1 a1
      bty2 = doClosure (sizeTopSlice size) bclo2 a2
      b1 = doSnd (sizeTopSlice size) p1
      b2 = doSnd (sizeTopSlice size) p2
  in eqNF size (aty1, a1) (aty2, a2) &&
     eqNF size (bty1, b1) (bty2, b2)
eqNF size (VUnd ty1, a1) (VUnd ty2, a2) =
  eqNF size (ty1, doUndOut (zero a1)) (ty2, doUndOut (zero a2))
eqNF size (VTensor aty1 bclo1, VTensorPair sl1 a1 sr1 b1) (VTensor aty2 bclo2, VTensorPair sl2 a2 sr2 b2) =
  let bty1 = doClosure (sizeTopSlice size) bclo1 a1
      bty2 = doClosure (sizeTopSlice size) bclo2 a2
  in eqNF size (aty1, a1) (aty2, a2) &&
     eqNF size (bty1, b1) (bty2, b2) &&
     splitEquivalent pal (sl1, sr1) (sl2, sr2)
       where (Size pal _ _) = size
eqNF size (VTensor aty1 bclo1, VNeutral _ ne1) (VTensor aty2 bclo2, VNeutral _ ne2) =
  eqNE size ne1 ne2
eqNF size (VUnit, VUnitIn u1) (VUnit, VUnitIn u2) =
  u1 == u2
eqNF size (VUnit, VNeutral _ ne1) (VUnit, VNeutral _ ne2) =
  eqNE size ne1 ne2
eqNF size (VHom aty1 bclo1, f1) (VHom aty2 bclo2, f2) =
  let var = makeVarValS aty1 size
      newsize = extSizeHomLam size
  in
  eqNF newsize (doHomClosure (sizeTopSlice newsize) (sizeTopSlice size) bclo1 (sizeTopRightSl newsize) var, doHomApp (sizeTopSlice newsize) (sizeTopSlice size) f1 (sizeTopRightSl newsize) var)
               (doHomClosure (sizeTopSlice newsize) (sizeTopSlice size) bclo2 (sizeTopRightSl newsize) var, doHomApp (sizeTopSlice newsize) (sizeTopSlice size) f2 (sizeTopRightSl newsize) var)
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
      && eqTy (extSizeLam size) (doClosure (sizeTopSlice size) mot1 motvar) (doClosure (sizeTopSlice size) mot2 motvar)
      && eqNF (size `extSizeComma` pattele) (doClosure (sizeTopSlice size) mot1 patterm, doClosurePat br1 pattele) (doClosure (sizeTopSlice size) mot2 patterm, doClosurePat br2 pattele)
eqNE size (NFst p1) (NFst p2) = eqNE size p1 p2
eqNE size (NSnd p1) (NSnd p2) = eqNE size p1 p2
eqNE size (NUndOut p1) (NUndOut p2) = eqNE size p1 p2
eqNE size (NHomApp fsl1 f1 asl1 (Normal aty1 a1)) (NHomApp fsl2 f2 asl2 (Normal aty2 a2)) =
  eqNE size f1 f2 && eqNF size (aty1, a1) (aty2, a2) &&
  splitEquivalent pal (fsl1, asl1) (fsl2, asl2)
    where (Size pal _ _) = size
eqNE _ _ _  = False

-- normalize :: SemEnv -> Term -> Ty -> Term
-- normalize = undefined
