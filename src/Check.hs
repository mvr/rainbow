module Check where

import Debug.Trace

import Control.Monad.Reader
import Control.Monad.Except
import Data.Functor.Identity

import qualified Normalize as N
import Normalize (Size, makeVarVal, PatPathPiece(..), PatPath)
import Palette
import Syntax

type Err = String

-- FIXME: this should really be SlL so that we don't have to weaken slices when we go under binders
data EntryAnn = Marked | Col SlI | Global
  deriving (Eq, Show)

data CtxEntry = CtxEntry Value VTy EntryAnn
  deriving (Show)

entryLiftComma :: CtxEntry -> CtxEntry
entryLiftComma (CtxEntry v ty (Col s)) = CtxEntry v ty (Col (CommaSl (Sub s) No))
entryLiftComma e = e

entryLiftTensor :: CtxEntry -> CtxEntry
entryLiftTensor (CtxEntry v ty (Col s)) = CtxEntry v ty (Col (TensorSl (Sub s) No))
entryLiftTensor e = e

entryToValue :: CtxEntry -> Value
entryToValue (CtxEntry t _ _) = t

data SemCtx = SemCtx { ctxTopSlice :: SlI, ctxPal :: SemPal, ctxVars :: [CtxEntry] }
  deriving (Show)

ctxEmpty :: SemCtx
ctxEmpty = SemCtx IdSl OriginSemPal []

ctxLen :: SemCtx -> Int
ctxLen = length . ctxVars

ctxSize :: SemCtx -> Size
ctxSize ctx =
  let pal = semPalToShape $ ctxPal ctx
  in N.Size pal (sliceIndexToLevel pal (ctxTopSlice ctx)) (ctxLen ctx)

ctxLookupVar :: Int -> SemCtx -> (VTy, EntryAnn)
ctxLookupVar ix (SemCtx _ _ vars) = case vars !! ix of
  (CtxEntry _ ty ann) -> (ty, ann)

ctxSetSlice :: SlI -> SemCtx -> SemCtx
ctxSetSlice s ctx = ctx { ctxTopSlice = s }

ctxToEnv :: SemCtx -> SemEnv
ctxToEnv (SemCtx s pal vars) = SemEnv (sliceIndexToLevel (semPalToShape pal) s) pal (fmap entryToValue vars)

-- "Telescopes", two different versions for the two different ways the
-- palettes can be combined. Hopefully this duplication is worth it in
-- errors caught.
data SemCtxTele = SemCtxTele { telePal :: SemPal, teleVars :: [CtxEntry] }
  deriving (Show)
data SemHomTele = SemHomTele { homTelePal :: SemPal, homTeleVars :: [CtxEntry] }
  deriving (Show)

ctxExtComma :: SemCtxTele -> SemCtx -> SemCtx
ctxExtComma (SemCtxTele pal' env') (SemCtx s pal env)  = SemCtx (CommaSl (Sub s) (Sub IdSl)) (CommaSemPal pal pal') (env' ++ fmap entryLiftComma env)

ctxExtCommaSilent :: [CtxEntry] -> SemCtx -> SemCtx
ctxExtCommaSilent es (SemCtx s pal vars) = SemCtx s pal (es ++ vars)

-- semCtxTensor :: SlL -> SemCtx -> SlL -> SemCtxTele -> SemCtx
-- semCtxTensor sl (SemCtx pal env) sr (SemCtxTele pal' env') = (SemCtx (TensorSemPal sl pal sr pal') (env' ++ fmap entryLiftTensor env))

-- Without changing the palette at all
ctxExtVar :: Value -> VTy -> SemCtx -> SemCtx
ctxExtVar a aty (SemCtx s pal vars) = SemCtx s pal ((CtxEntry a aty (Col s)):vars)

ctxExtGlobal :: Value -> VTy -> SemCtx -> SemCtx
ctxExtGlobal a aty (SemCtx s pal vars) = SemCtx s pal ((CtxEntry a aty Global):vars)

ctxExtValZero :: Value -> VTy -> SemCtx -> SemCtx
ctxExtValZero a aty (SemCtx s pal vars) = SemCtx s pal ((CtxEntry a aty Marked):vars)

ctxExtHom :: Value -> VTy -> SemCtx -> SemCtx
ctxExtHom a aty (SemCtx s pal vars) = SemCtx (TensorSl (Sub s) (Sub IdSl)) (TensorSemPal sl pal sr OneSemPal) ((CtxEntry a aty (Col c)):(fmap entryLiftTensor vars))
  where sl = sliceIndexToLevel (semPalToShape pal) s
        sr = SlL (1 + semPalDepth pal) (TensorSl No (Sub IdSl))
        c = (TensorSl No (Sub IdSl))

newtype CheckM a = CheckM (ReaderT SemCtx (ExceptT Err Identity) a)
  deriving (Functor, Applicative, Monad, MonadError Err, MonadReader SemCtx)

runCheckM :: SemCtx -> CheckM a -> Either Err a
runCheckM env (CheckM m) = runIdentity $ runExceptT $ runReaderT m env

eval :: Term -> CheckM Value
eval aty = do
  semEnv <- asks ctxToEnv
  return $ N.eval semEnv aty

evalClosure :: Closure -> Term -> CheckM Value
evalClosure clo a = do
  semEnv <- asks ctxToEnv

  let aval = N.eval semEnv a
  return $ N.doClosure (semEnvTopSlice semEnv) clo aval

evalAndVar :: Ty -> CheckM (VTy, Value)
evalAndVar aty = do
  semEnv <- asks ctxToEnv
  let atyval = N.eval semEnv aty
  lev <- asks ctxLen
  let var = makeVarVal atyval lev
  return (atyval, var)

assertEq :: VTy -> Value -> Value -> CheckM ()
assertEq ty a b = do
  size <- asks ctxSize
  unless (N.eqNF size (ty, a) (ty, b)) $
    throwError $ "Expected " ++ show a ++ " to equal " ++ show b

check :: Term -> VTy -> CheckM ()
-- check s t ty | traceShow ("Check: " ++ show (s, t, ty)) False = undefined

check (Univ i) (VUniv j) | i < j = return ()
check (Univ i) t = throwError $ "Expecting universe over " ++ show i

check (Pi aty bty) (VUniv l) = do
  check aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtVar var atyval) $ check bty (VUniv l)
check (Pi aty bclo) t = throwError "Expected universe"

check (Lam b) (VPi aty bclo) = do
  lev <- asks ctxLen
  env <- asks ctxToEnv
  let var = makeVarVal aty lev
  let bty = N.doClosure (semEnvTopSlice env) bclo var
  local (ctxExtVar var aty) $ check b bty
check (Lam b) ty = throwError "Unexpected lambda"

check (Sg aty bty) (VUniv l) = do
  check aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtVar var atyval) $ check bty (VUniv l)
check (Sg aty bclo) t = throwError "Expected universe"

check (Pair a b) (VSg aty bclo) = do
  check a aty
  bty <- evalClosure bclo a
  check b bty
check (Pair a b) ty = throwError "Unexpected pair"

check (Id aty a b) (VUniv l) = do
  check aty (VUniv l)
  aty' <- eval aty
  check a aty'
  check b aty'
check (Id aty a b) t = throwError "Expected universe"

check (Refl t) (VId aty a b) = do
  check t aty
  tval <- eval t
  assertEq aty a tval
  assertEq aty b tval
check (Refl t) ty = throwError "Unexpected refl"

check (Und ty) (VUniv l) = local (ctxSetSlice OneSl) $ check ty (VUniv l)
check (Und ty) t = throwError "Expected universe"

check (UndIn a) (VUnd aty) = local (ctxSetSlice OneSl) $ check a aty
check (UndIn a) aty = throwError "Unexpected natural intro"

check (Tensor aty bty) (VUniv l) = do
  local (ctxSetSlice OneSl) $ check aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtValZero var atyval) $ local (ctxSetSlice OneSl) $ check bty (VUniv l)
check (Tensor aty bclo) t = throwError "Expected universe"

check t@(TensorPair asl a bsl b) (VTensor aty bclo) = do
  s <- asks ctxTopSlice
  when (not $ validSplitOf s (asl, bsl)) $ throwError $ "Invalid split of " ++ show s ++ " into " ++ show (asl, bsl)

  local (ctxSetSlice asl) $ check a aty
  bty <- evalClosure bclo a
  local (ctxSetSlice bsl) $ check b bty
check (TensorPair _ _ _ _) ty = throwError "Unexpected tensor intro"

check Unit (VUniv l) = return ()

check (UnitIn u) VUnit = do
  s <- asks ctxTopSlice
  when (not $ validUnitOf s u) $ throwError $ "Invalid unit of " ++ show s ++ " into " ++ show u

check (Hom aty bty) (VUniv l) = do
  local (ctxSetSlice OneSl) $ check aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtHom var atyval) $ check bty (VUniv l)
check (Hom aty bclo) t = throwError "Expected universe"

check (HomLam b) (VHom aty bclo) = do
  lev <- asks ctxLen
  env <- asks ctxToEnv
  let var = makeVarVal aty lev
  let bty = N.doClosure (semEnvTopSlice env) bclo var
  local (ctxExtHom var aty) $ check b bty
check (HomLam b) ty = throwError "Unexpected hom lambda"

check a ty = do
  ty' <- synth a
  size <- asks ctxSize
  when (not $ N.eqTy size ty ty') $ throwError $ "type mismatch, expected: " ++ show ty ++ " got " ++ show ty'

synth :: Term -> CheckM VTy
-- synth t | traceShow ("Synth: " ++ show (s, t)) False = undefined
synth (Var i) = do
  (ty, ann) <- asks (ctxLookupVar i)
  case ann of
    Marked -> throwError $ "Cannot use variable " ++ show i ++ " because it is marked"
    Global -> return ty
    Col c -> do
      s <- asks ctxTopSlice
      when (not $ s `cellTo` c) $ throwError $ "Cannot use variable " ++ show i ++
                                               " because the variable with annotation " ++ show c ++
                                               " is not usable in slice " ++ show s
      return ty

synth (ZeroVar i) = do
  (ty, _) <- asks (ctxLookupVar i)
  lev <- asks ctxLen
  return (N.zero ty)

synth (Check a aty) = do
  tyval <- eval aty
  check a tyval
  return tyval

synth (Fst p) = do
  ty <- synth p
  case ty of
    (VSg a b) -> return a
    _ -> throwError "expected Sg type"

synth (Snd p) = do
  ty <- synth p
  case ty of
    (VSg aty bclo) -> evalClosure bclo (Fst p)
    _ -> throwError "expected Sg type"

synth (App f a) = do
  fty <- synth f
  case fty of
    (VPi aty bclo) -> do
      check a aty
      evalClosure bclo a
    _ -> throwError "expected Pi type"

synth (HomApp fsl f asl a) = do
  s <- asks ctxTopSlice
  when (not $ validSplitOf s (fsl, asl)) $ throwError "Invalid split"

  fty <- local (ctxSetSlice fsl) $ synth f
  case fty of
    (VHom aty bclo) -> do
      local (ctxSetSlice asl) $ check a aty
      evalClosure bclo a
    _ -> throwError "expected Hom type"

synth (UndOut n) = do
  nty <- synth n
  case nty of
    (VUnd aty) -> return aty
    _ -> throwError "expected Und type"

synth (Match tar mot pat branch) = do
  size <- asks ctxSize

  let palext = N.makePatPal size [RightCommaPath] (patToShape pat)

  s <- asks ctxTopSlice
  (pattele, patterm) <- local (ctxExtComma (SemCtxTele palext [])) $ checkAndEvalPat s [] pat

  semEnv <- asks ctxToEnv

  let vpat   = N.evalPat semEnv pat
      tarty  = N.recoverPatType vpat
      tarvar = N.makeVarValS tarty size

  local (ctxExtVar tarvar tarty) $ checkTy mot
  check tar tarty
  local (ctxExtComma (SemCtxTele palext pattele)) $ check branch (N.eval (semEnvCommaSingle semEnv patterm) mot)

  return $ N.eval (semEnvExtSilentSingle semEnv (N.eval semEnv tar)) mot

synth a = throwError $ "cannot synth the type of " ++ show a

-- This duplicates some logic in `Normalise` but I think this avoids
-- being accidentally quadratic by repeatedly evalling the types

-- At this point the palette has already been added to the context.

-- `s` represents the slice that the entire pattern is being checked
-- at, not the slice at the current location in the palette.
checkAndEvalPat :: SlI -> PatPath -> Pat -> CheckM ([CtxEntry], Value)
checkAndEvalPat s path (VarPat ty) = do
  let c = sliceAtType s path
  local (ctxSetSlice c) $ checkTy ty
  (vty, v) <- evalAndVar ty
  return $ ([CtxEntry v vty (Col c)], v)

checkAndEvalPat s path (ZeroVarPat ty) = do
  local (ctxSetSlice OneSl) $ checkTy ty
  size <- asks ctxSize
  env <- asks ctxToEnv

  let vty = N.eval env ty
      v = N.makeZeroVarValS vty size

  return $ ([CtxEntry v vty Marked], v)

checkAndEvalPat s _ OnePat = pure ([], VOneIn)
checkAndEvalPat s path (UndInPat p) = do
  (ptele, pterm) <- checkAndEvalPat s undefined p -- FIXME: this is stupid
  return $ (ptele, VUndIn pterm)
checkAndEvalPat s path UnitPat = do
  size <- asks ctxSize
  let u = N.makeUnitVal size path
  return ([], VUnitIn u)
checkAndEvalPat s path (PairPat p q) = do
  (ptele, pterm) <- checkAndEvalPat s (LeftCommaPath : path) p
  (qtele, qterm) <- local (ctxExtCommaSilent ptele) $ checkAndEvalPat s (RightCommaPath : path) q
  return (qtele ++ ptele, VPair pterm qterm)
checkAndEvalPat s path (ReflPat p) = do
  (ptele, pterm) <- checkAndEvalPat s path p
  return (ptele, VPair pterm (VPair pterm (VRefl pterm)))
checkAndEvalPat s path (TensorPat p q) = do
  size <- asks ctxSize
  let psl = N.makeSliceVal size (LeftTensorPath : path)
      qsl = N.makeSliceVal size (RightTensorPath : path)
  (ptele, pterm) <- checkAndEvalPat s (LeftTensorPath : path) p
  (qtele, qterm) <- local (ctxExtCommaSilent ptele) $ checkAndEvalPat s (RightTensorPath : path) q
  return (qtele ++ ptele, VTensorPair psl pterm qsl qterm)
checkAndEvalPat s path (LeftUnitorPat p) = do
  (ptele, pterm) <- local (ctxExtValZero (VUnitIn (UnitL 0 OneUnit)) VUnit) $ checkAndEvalPat s (LeftUnitorPath : path) p
  pal <- asks ctxPal
  return (ptele, VTensorPair (SlL 0 SummonedUnitSl) (VUnitIn (UnitL 0 SummonedUnit)) (sliceIndexToLevel (semPalToShape pal) $ sliceAtType s path) pterm)
checkAndEvalPat s path (RightUnitorPat p) = do
  (ptele, pterm) <- checkAndEvalPat s (RightUnitorPath : path) p
  pal <- asks ctxPal
  return (ptele, VTensorPair (sliceIndexToLevel (semPalToShape pal) $ sliceAtType s path) pterm (SlL 0 SummonedUnitSl) (VUnitIn (UnitL 0 SummonedUnit)))


-- The slice to check a type sitting at `path` in a pattern, when the
-- ambient slice is `s`.

-- FIXME: will need a different version of this for hom match
sliceAtType :: SlI -> PatPath -> SlI
sliceAtType s p = case sliceAtType' (reverse p)  of
  (s', True) -> CommaSl No (Sub s')
  (s', False) -> CommaSl (Sub s) (Sub s')

-- Bool to ask whether we have gone under a tensor and lose stuff to the left.
sliceAtType' :: PatPath -> (SlI, Bool)
sliceAtType' [] = (IdSl, False)
sliceAtType' (LeftTensorPath : p) = (TensorSl (Sub $ fst $ sliceAtType' p) No, True)
sliceAtType' (RightTensorPath : p) = (TensorSl No (Sub $ fst $ sliceAtType' p), True)
sliceAtType' (LeftCommaPath : p) = let (s, b) = sliceAtType' p in (CommaSl (Sub $ s) No, b)
sliceAtType' (RightCommaPath : p) = case sliceAtType' p of
  (s, True) -> (CommaSl No (Sub s), True)
  (s, False) -> (CommaSl (Sub IdSl) (Sub s), False)
sliceAtType' (LeftUnitorPath : p) = (fst $ sliceAtType' p, True)
sliceAtType' (RightUnitorPath : p) = (fst $ sliceAtType' p, True)

checkTy :: Ty -> CheckM ()
-- checkTy t | traceShow ("Check ty: " ++ show t) False = undefined
checkTy (Univ i) = return ()
checkTy (Pi aty bty) = do
  checkTy aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtVar var atyval) $ checkTy bty
checkTy (Sg aty bty) = do
  checkTy aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtVar var atyval) $ checkTy bty
checkTy (Id aty a b) = do
  checkTy aty
  aty' <- eval aty
  check a aty'
  check b aty'
checkTy (Und ty) = do
  local (ctxSetSlice OneSl) $ checkTy ty
checkTy (Tensor aty bty) = do
  local (ctxSetSlice OneSl) $ checkTy aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtValZero var atyval) $ local (ctxSetSlice OneSl) $ checkTy bty
checkTy Unit = return ()
checkTy (Hom aty bty) = do
  local (ctxSetSlice OneSl) $ checkTy aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtHom var atyval) $ checkTy bty
checkTy a = do
  ty <- synth a
  case ty of
    VUniv l -> return ()
    t -> throwError $ "Expected " ++ show a ++ " to synth universe, instead got " ++ show t
