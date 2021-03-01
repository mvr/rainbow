module Check where

import Debug.Trace

import Control.Monad.Reader
import Control.Monad.Except
import Data.Functor.Identity

import qualified Normalize as N
import Normalize (Size, makeVarVal)
import Palette
import Syntax

type Err = String

-- FIXME: this should really be SlL so that we don't have to weaken slices when we go under binders
data EntryAnn = Marked | Col SlI | Global
  deriving (Eq, Show)

data CtxEntry = CtxEntry Value VTy EntryAnn
  deriving (Eq, Show)

data SemCtx = SemCtx { ctxPal :: SemPal, ctxVars :: [CtxEntry] }
  deriving (Eq, Show)

entryLiftComma :: CtxEntry -> CtxEntry
entryLiftComma (CtxEntry v ty (Col s)) = CtxEntry v ty (Col (CommaSl (Sub s) No))
entryLiftComma e = e

entryLiftTensor :: CtxEntry -> CtxEntry
entryLiftTensor (CtxEntry v ty (Col s)) = CtxEntry v ty (Col (TensorSl (Sub s) No))
entryLiftTensor e = e

entryToValue :: CtxEntry -> Value
entryToValue (CtxEntry t _ _) = t

ctxToEnv :: SemCtx -> SemEnv
ctxToEnv (SemCtx pal vars) = SemEnv pal (fmap entryToValue vars)

-- "Telescopes", two different versions for the two different ways the
-- palettes can be combined. Hopefully this duplication is worth it in
-- errors caught.
data SemCtxTele = SemCtxTele { telePal :: SemPal, teleVars :: [CtxEntry] }
  deriving (Eq, Show)
data SemHomTele = SemHomTele { homTelePal :: SemPal, homTeleVars :: [CtxEntry] }
  deriving (Eq, Show)

semCtxComma :: SemCtx -> SemCtxTele -> SemCtx
semCtxComma (SemCtx pal env) (SemCtxTele pal' env') = (SemCtx (CommaSemPal pal pal') (env' ++ fmap entryLiftComma env))

semCtxTensor :: SlL -> SemCtx -> SlL -> SemCtxTele -> SemCtx
semCtxTensor sl (SemCtx pal env) sr (SemCtxTele pal' env') = (SemCtx (TensorSemPal sl pal sr pal') (env' ++ fmap entryLiftTensor env))

-- FIXME: Aren't used anywhere? Also, they don't lift the colours like the previous
-- semTeleComma :: SemCtxTele -> SemCtxTele -> SemCtxTele
-- semTeleComma (SemCtxTele pal env) (SemCtxTele pal' env') = (SemCtxTele (CommaSemPal pal pal') (env' ++ env))

-- semTeleTensor :: SlL -> SemCtxTele -> SlL -> SemCtxTele -> SemCtxTele
-- semTeleTensor sl (SemCtxTele pal env) sr (SemCtxTele pal' env') = (SemCtxTele (TensorSemPal sl pal sr pal') (env' ++ env))

-- semTeleToEnv :: SemCtxTele -> SemEnv
-- semTeleToEnv (SemCtxTele pal vars) = SemEnv pal (fmap (\(CtxEntry v _ _) -> v) vars)

ctxEmpty :: SemCtx
ctxEmpty = SemCtx OriginSemPal []

ctxLookupVar :: Int -> SemCtx -> (VTy, EntryAnn)
ctxLookupVar ix (SemCtx _ vars) = case vars !! ix of
  (CtxEntry _ ty ann) -> (ty, ann)

-- Without changing the palette at all
ctxExtVar :: Value -> VTy -> SlI -> SemCtx -> SemCtx
ctxExtVar a aty c (SemCtx pal vars) = SemCtx pal ((CtxEntry a aty (Col c)):vars)

ctxExtMany :: [CtxEntry] -> SemCtx -> SemCtx
ctxExtMany es (SemCtx pal vars) = SemCtx pal (es ++ vars)

ctxExtGlobal :: Value -> VTy -> SemCtx -> SemCtx
ctxExtGlobal a aty (SemCtx pal vars) = SemCtx pal ((CtxEntry a aty Global):vars)

ctxExtValZero :: Value -> VTy -> SemCtx -> SemCtx
ctxExtValZero a aty (SemCtx pal vars) = SemCtx pal ((CtxEntry a aty Marked):vars)

ctxExtHom :: Value -> VTy -> SemCtx -> SemCtx
ctxExtHom = undefined
-- ctxExtHom t ty (SemCtx pal vars)
--   = SemCtx { ctxPal = Palette [TensorPal pal (Palette [])],
--              ctxVars = (CtxTerm t ty (Just rightCol)) : (fmap (ctxEntryWkColHom pal) vars)
--            }
--   where rightCol = RightSub 0 TopColour

-- patCartTele :: Pat -> (Palette, [CtxEntry])
-- patCartTele = undefined

cartWkEntry :: CtxEntry -> CtxEntry
cartWkEntry = undefined

-- ctxExtCartPat :: Pat -> SemCtx -> SemCtx
-- ctxExtCartPat pat (SemCtx pal vars) = let (palext, ctxext) = patCartTele pat in
--   SemCtx (CommaPal pal palext) (ctxext ++ fmap cartWkEntry vars)

ctxLen :: SemCtx -> Int
ctxLen = length . ctxVars

ctxSize :: SemCtx -> Size
ctxSize = undefined

envExt :: SemEnv -> Value -> SemEnv
envExt (SemEnv pal env) v = SemEnv pal (v : env)

-- teleToEnv :: SemTele -> SemEnv
-- teleToEnv (SemTele _ vars) = fmap (\(t, _, _) -> t) vars

newtype CheckM a = CheckM (ReaderT SemCtx (ExceptT Err Identity) a)
  deriving (Functor, Applicative, Monad, MonadError Err, MonadReader SemCtx)

runCheckM :: SemCtx -> CheckM a -> Either Err a
runCheckM env (CheckM m) = runIdentity $ runExceptT $ runReaderT m env

evalAndVar :: Ty -> CheckM (VTy, Value)
evalAndVar aty = do
  semEnv <- asks ctxToEnv
  let atyval = N.eval semEnv aty
  lev <- asks ctxLen
  let var = makeVarVal atyval lev
  return (atyval, var)

check :: SlI -> Term -> VTy -> CheckM ()
-- check s t ty | traceShow ("Check: " ++ show (s, t, ty)) False = undefined

check s (Univ i) (VUniv j) | i < j = return ()
check s (Univ i) t = throwError $ "Expecting universe over " ++ show i

check s (Pi aty bty) (VUniv l) = do
  check s aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtVar var atyval s) $ check s bty (VUniv l)
check s (Pi aty bclo) t = throwError "Expected universe"

check s (Lam b) (VPi aty bclo) = do
  lev <- asks ctxLen
  let var = makeVarVal aty lev
  let bty = N.doClosure bclo var
  local (ctxExtVar var aty s) $ check s b bty
check s (Lam b) ty = throwError "Unexpected lambda"

check s (Sg aty bty) (VUniv l) = do
  check s aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtVar var atyval s) $ check s bty (VUniv l)
check s (Sg aty bclo) t = throwError "Expected universe"

check s (Pair a b) (VSg aty bclo) = do
  check s a aty
  semEnv <- asks ctxToEnv
  let aval = N.eval semEnv a
  check s b (N.doClosure bclo aval)
check s (Pair a b) ty = throwError "Unexpected pair"

check s (Und ty) (VUniv l) = do
  check OneSl ty (VUniv l)
check s (Und ty) t = throwError "Expected universe"

check s (UndIn a) (VUnd aty) = do
  check OneSl a aty
check s (UndIn a) aty = throwError "Unexpected natural intro"

check s (Tensor aty bty) (VUniv l) = do
  check OneSl aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtValZero var atyval) $ check OneSl bty (VUniv l)
check s (Tensor aty bclo) t = throwError "Expected universe"

check s t@(TensorPair asl a bsl b) (VTensor aty bclo) = do
  -- traceShow "checking tensor pair" $ return ()
  -- e <- ask
  -- traceShow e $ return ()

  when (not $ validSplitOf s (asl, bsl)) $ throwError "Invalid split"

  check asl a aty
  semEnv <- asks ctxToEnv
  let aval = N.eval semEnv a
  check bsl b (N.doClosure bclo aval)
check s (TensorPair _ _ _ _) ty = throwError "Unexpected tensor intro"

check s (Hom aty bty) (VUniv l) = do
  check OneSl aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtHom var atyval) $ check (TensorSl (Sub s) Yes) bty (VUniv l)
check s (Hom aty bclo) t = throwError "Expected universe"

-- check s (HomLam b) (VHom aty bclo) = do
--   lev <- asks ctxLen
--   let var = makeVarVal aty lev
--   let bty = N.doClosure bclo var
--   local (ctxExtHom var aty) $ check b bty
-- check s (HomLam b) ty = throwError "Unexpected hom lambda"

check s a ty = do
  -- e <- asks ctxToEnv
  -- traceShow e $ return ()
  ty' <- synth s a
  size <- asks ctxSize
  when (not $ N.eqTy size ty ty') $ throwError $ "type mismatch, expected: " ++ show ty ++ " got " ++ show ty'

synth :: SlI -> Term -> CheckM VTy
-- synth s t | traceShow ("Synth: " ++ show (s, t)) False = undefined
synth s (Var i) = do
  -- s <- ask
  -- traceShow s (return ())
  (ty, ann) <- asks (ctxLookupVar i)
  case ann of
    Marked -> throwError $ "Cannot use variable " ++ show i ++ " because it is marked"
    Global -> return ty
    Col c -> do
      when (not $ c `weakenableTo` s) $ throwError $ "Cannot use variable " ++ show i ++ " because the variable with annotation " ++ show c ++ " is not usable in slice " ++ show s
      return ty

synth s (ZeroVar i) = do
  (ty, _) <- asks (ctxLookupVar i)
  lev <- asks ctxLen
  return (N.zero ty)

synth s (Check a aty) = do
  semEnv <- asks ctxToEnv
  let tyval = N.eval semEnv aty
  check s a tyval
  return tyval

synth s (Fst p) = do
  ty <- synth s p
  case ty of
    (VSg a b) -> return a
    _ -> throwError "expected Sg type"

synth s (Snd p) = do
  ty <- synth s p
  case ty of
    (VSg aty bclo) -> do
      semEnv <- asks ctxToEnv
      let aval = N.eval semEnv (Fst p)
      return $ N.doClosure bclo aval
    _ -> throwError "expected Sg type"

synth s (App f a) = do
  fty <- synth s f
  case fty of
    (VPi aty bclo) -> do
      check s a aty
      semEnv <- asks ctxToEnv
      let aval = N.eval semEnv a
      return $ N.doClosure bclo aval
    _ -> throwError "expected Pi type"

synth s (HomApp fsl f asl a) = do
  when (not $ validSplitOf s (fsl, asl)) $ throwError "Invalid split"

  fty <- synth fsl f
  case fty of
    (VHom aty bclo) -> do
      check asl a aty
      semEnv <- asks ctxToEnv
      let aval = N.eval semEnv a
      return $ N.doClosure bclo aval
    _ -> throwError "expected Hom type"

synth s (UndOut n) = do
  nty <- synth s n
  case nty of
    (VUnd aty) -> return aty
    _ -> throwError "expected Und type"

synth s (Match tar mot pat branch) = do
  size <- asks ctxSize

  let pal = N.makePatPal size (RightCommaPath StartPath) (patToShape pat)
  (pattele, patterm) <- local (flip semCtxComma (SemCtxTele pal [])) $ checkAndEvalPat s (RightCommaPath StartPath) pat

  semEnv <- asks ctxToEnv

  let vpat = N.evalPat semEnv pat
      tarty = N.recoverPatType vpat
      motvar = N.makeVarValS tarty size

  local (ctxExtVar motvar tarty s) $ checkTy s mot

  check s tar tarty

  let (_, patterm) = N.makeVPatCartTele size vpat
  local (flip semCtxComma (SemCtxTele pal pattele)) $ check (CommaSl (Sub s) Yes) branch (N.eval (envExt semEnv patterm) mot)

  return $ N.eval (envExt semEnv (N.eval semEnv tar)) mot

synth s a = throwError $ "cannot synth the type of " ++ show a

-- This duplicates some logic in `Normalise` but I think this avoids
-- being accidentally quadratic by repeatedly evalling the types

-- At this point the palette has already been added to the context.

-- `s` represents the slice that the match is being checked at, not the
checkAndEvalPat :: SlI -> PatPath -> Pat -> CheckM ([CtxEntry], Value)
checkAndEvalPat s path (VarPat ty) = do
  checkTy (sliceAtType s path) ty
  size <- asks ctxSize
  env <- asks ctxToEnv

  let vty = N.eval env ty
      v = N.makeVarValS vty size
      s = N.makeSliceVal size path
      i = N.pathToSlice path

  return $ ([CtxEntry v vty (Col i)], v)

checkAndEvalPat s _ OnePat = pure ([], VOneIn)
checkAndEvalPat s path UnitPat = do
  size <- asks ctxSize
  let u = N.makeUnitVal size path
  return ([], VUnitIn u)
checkAndEvalPat s path (PairPat p q) = do
  (ptele, pterm) <- checkAndEvalPat s (LeftCommaPath path) p
  (qtele, qterm) <- local (ctxExtMany ptele) $ checkAndEvalPat s (RightCommaPath path) q
  return (qtele ++ ptele, VPair pterm qterm)
checkAndEvalPat s path (TensorPat p q) = do
  size <- asks ctxSize
  let psl = N.makeSliceVal size (LeftTensorPath path)
      qsl = N.makeSliceVal size (RightTensorPath path)
  (ptele, pterm) <- checkAndEvalPat s (LeftTensorPath path) p
  (qtele, qterm) <- local (ctxExtMany ptele) $ checkAndEvalPat s (RightTensorPath path) q
  return (qtele ++ ptele, VTensorPair psl pterm qsl qterm)

-- The slice to check a type sitting at `path` in a pattern, when the
-- ambient slice is `s`.

-- FIXME: will need a different version of this for hom match
sliceAtType :: SlI -> PatPath -> SlI
sliceAtType s p = case sliceAtType' p  of
  (s', True) -> CommaSl No (Sub s')
  (s', False) -> CommaSl (Sub s) (Sub s')

-- Bool to ask whether we have gone under a tensor and lose stuff to the left.
sliceAtType' :: PatPath -> (SlI, Bool)
sliceAtType' StartPath = (TopSl, False)
sliceAtType' (LeftTensorPath StartPath) = (TensorSl Yes No, True)
sliceAtType' (LeftTensorPath p) = (TensorSl (Sub $ fst $ sliceAtType' p) No, True)
sliceAtType' (RightTensorPath StartPath) = (TensorSl No Yes, True)
sliceAtType' (RightTensorPath p) = (TensorSl No (Sub $ fst $ sliceAtType' p), True)
sliceAtType' (LeftCommaPath StartPath) = (CommaSl Yes No, False)
sliceAtType' (LeftCommaPath p) = let (s, flag) = sliceAtType' p in (CommaSl (Sub s) No, flag)
sliceAtType' (RightCommaPath StartPath) = (CommaSl Yes Yes, False)
sliceAtType' (RightCommaPath p) = case sliceAtType' p of
  (s, True) -> (CommaSl No (Sub s), True)
  (s, False) -> (CommaSl Yes (Sub s), False)

checkTy :: SlI -> Ty -> CheckM ()
-- checkTy t | traceShow ("Check ty: " ++ show t) False = undefined
checkTy s (Univ i) = return ()
checkTy s (Pi aty bty) = do
  checkTy s aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtVar var atyval s) $ checkTy s bty
checkTy s (Sg aty bty) = do
  checkTy s aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtVar var atyval s) $ checkTy s bty
checkTy s (Und ty) = do
  checkTy OneSl ty
checkTy s (Tensor aty bty) = do
  checkTy OneSl aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtValZero var atyval) $ checkTy OneSl bty
checkTy s (Hom aty bty) = do
  checkTy OneSl aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtHom var atyval) $ checkTy (TensorSl (Sub s) Yes) bty
checkTy s a = do
  ty <- synth s a
  case ty of
    VUniv l -> return ()
    t -> throwError $ "Expected " ++ show a ++ " to synth universe, instead got " ++ show t
