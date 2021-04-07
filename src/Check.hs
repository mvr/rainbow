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

data SemCtx = SemCtx { ctxPal :: SemPal, ctxVars :: [CtxEntry] }
  deriving (Show)

entryLiftComma :: CtxEntry -> CtxEntry
entryLiftComma (CtxEntry v ty (Col s)) = CtxEntry v ty (Col (CommaSl (Sub s) No))
entryLiftComma e = e

entryLiftTensor :: CtxEntry -> CtxEntry
entryLiftTensor (CtxEntry v ty (Col s)) = CtxEntry v ty (Col (TensorSl (Sub s) No))
entryLiftTensor e = e

entryToValue :: CtxEntry -> Value
entryToValue (CtxEntry t _ _) = t

ctxToEnv :: SemCtx -> SemEnv
ctxToEnv (SemCtx pal vars) = SemEnv (palTopSliceLevel $ semPalToShape pal) pal (fmap entryToValue vars)

-- "Telescopes", two different versions for the two different ways the
-- palettes can be combined. Hopefully this duplication is worth it in
-- errors caught.
data SemCtxTele = SemCtxTele { telePal :: SemPal, teleVars :: [CtxEntry] }
  deriving (Show)
data SemHomTele = SemHomTele { homTelePal :: SemPal, homTeleVars :: [CtxEntry] }
  deriving (Show)

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
ctxExtHom a aty (SemCtx pal vars) = SemCtx (TensorSemPal sl pal sr OneSemPal) ((CtxEntry a aty (Col c)):(fmap entryLiftTensor vars))
  where d = semPalDepth pal
        sl = SlL d IdSl
        sr = SlL (d+1) (TensorSl No (Sub IdSl))
        c  = (TensorSl No (Sub IdSl))

-- patCartTele :: Pat -> (Palette, [CtxEntry])
-- patCartTele = undefined

-- cartWkEntry :: CtxEntry -> CtxEntry
-- cartWkEntry = undefined

-- ctxExtCartPat :: Pat -> SemCtx -> SemCtx
-- ctxExtCartPat pat (SemCtx pal vars) = let (palext, ctxext) = patCartTele pat in
--   SemCtx (CommaPal pal palext) (ctxext ++ fmap cartWkEntry vars)

ctxLen :: SemCtx -> Int
ctxLen = length . ctxVars

ctxSize :: SlI -> SemCtx -> Size
ctxSize s ctx = let pal = semPalToShape $ ctxPal ctx in N.Size pal (sliceIndexToLevel pal s) (ctxLen ctx)

envExtComma :: SemEnv -> Value -> SemEnv
envExtComma (SemEnv s pal env) v = SemEnv (slExtMatch (semPalToShape pal) s) (CommaSemPal pal OneSemPal) (v : env)

envExtSilent :: SemEnv -> Value -> SemEnv
envExtSilent (SemEnv s pal env) v = SemEnv s pal (v : env)

-- teleToEnv :: SemTele -> SemEnv
-- teleToEnv (SemTele _ vars) = fmap (\(t, _, _) -> t) vars

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

assertEq :: SlI -> VTy -> Value -> Value -> CheckM ()
assertEq s ty a b = do
  size <- asks (ctxSize s)
  unless (N.eqNF size (ty, a) (ty, b)) $
    throwError $ "Expected " ++ show a ++ " to equal " ++ show b

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
  env <- asks ctxToEnv
  let var = makeVarVal aty lev
  let bty = N.doClosure (semEnvTopSlice env) bclo var
  local (ctxExtVar var aty s) $ check s b bty
check s (Lam b) ty = throwError "Unexpected lambda"

check s (Sg aty bty) (VUniv l) = do
  check s aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtVar var atyval s) $ check s bty (VUniv l)
check s (Sg aty bclo) t = throwError "Expected universe"

check s (Pair a b) (VSg aty bclo) = do
  check s a aty
  bty <- evalClosure bclo a
  check s b bty
check s (Pair a b) ty = throwError "Unexpected pair"

check s (Id aty a b) (VUniv l) = do
  check s aty (VUniv l)
  aty' <- eval aty
  check s a aty'
  check s b aty'
check s (Id aty a b) t = throwError "Expected universe"

check s (Refl t) (VId aty a b) = do
  check s t aty
  tval <- eval t
  assertEq s aty a tval
  assertEq s aty b tval
check s (Refl t) ty = throwError "Unexpected refl"

check s (Und ty) (VUniv l) = check OneSl ty (VUniv l)
check s (Und ty) t = throwError "Expected universe"

check s (UndIn a) (VUnd aty) = check OneSl a aty
check s (UndIn a) aty = throwError "Unexpected natural intro"

check s (Tensor aty bty) (VUniv l) = do
  check OneSl aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtValZero var atyval) $ check OneSl bty (VUniv l)
check s (Tensor aty bclo) t = throwError "Expected universe"

check s t@(TensorPair asl a bsl b) (VTensor aty bclo) = do
  when (not $ validSplitOf s (asl, bsl)) $ throwError $ "Invalid split of " ++ show s ++ " into " ++ show (asl, bsl)

  check asl a aty
  bty <- evalClosure bclo a
  check bsl b bty
check s (TensorPair _ _ _ _) ty = throwError "Unexpected tensor intro"

check s Unit (VUniv l) = return ()

check s (UnitIn u) VUnit = do
  when (not $ validUnitOf s u) $ throwError $ "Invalid unit of " ++ show s ++ " into " ++ show u

check s (Hom aty bty) (VUniv l) = do
  check OneSl aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtHom var atyval) $ check (TensorSl (Sub s) (Sub IdSl)) bty (VUniv l)
check s (Hom aty bclo) t = throwError "Expected universe"

check s (HomLam b) (VHom aty bclo) = do
  lev <- asks ctxLen
  env <- asks ctxToEnv
  let var = makeVarVal aty lev
  let bty = N.doClosure (semEnvTopSlice env) bclo var
  local (ctxExtHom var aty) $ check (TensorSl (Sub s) (Sub IdSl)) b bty
check s (HomLam b) ty = throwError "Unexpected hom lambda"

check s a ty = do
  ty' <- synth s a
  size <- asks (ctxSize s)
  when (not $ N.eqTy size ty ty') $ throwError $ "type mismatch, expected: " ++ show ty ++ " got " ++ show ty'

synth :: SlI -> Term -> CheckM VTy
-- synth s t | traceShow ("Synth: " ++ show (s, t)) False = undefined
synth s (Var i) = do
  (ty, ann) <- asks (ctxLookupVar i)
  case ann of
    Marked -> throwError $ "Cannot use variable " ++ show i ++ " because it is marked"
    Global -> return ty
    Col c -> do
      when (not $ s `cellTo` c) $ throwError $ "Cannot use variable " ++ show i ++ " because the variable with annotation " ++ show c ++ " is not usable in slice " ++ show s
      return ty

synth s (ZeroVar i) = do
  (ty, _) <- asks (ctxLookupVar i)
  lev <- asks ctxLen
  return (N.zero ty)

synth s (Check a aty) = do
  tyval <- eval aty
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
    (VSg aty bclo) -> evalClosure bclo (Fst p)
    _ -> throwError "expected Sg type"

synth s (App f a) = do
  fty <- synth s f
  case fty of
    (VPi aty bclo) -> do
      check s a aty
      evalClosure bclo a
    _ -> throwError "expected Pi type"

synth s (HomApp fsl f asl a) = do
  when (not $ validSplitOf s (fsl, asl)) $ throwError "Invalid split"

  fty <- synth fsl f
  case fty of
    (VHom aty bclo) -> do
      check asl a aty
      evalClosure bclo a
    _ -> throwError "expected Hom type"

synth s (UndOut n) = do
  nty <- synth s n
  case nty of
    (VUnd aty) -> return aty
    _ -> throwError "expected Und type"

synth s (Match tar mot pat branch) = do
  size <- asks (ctxSize s)

  let pal = N.makePatPal size [RightCommaPath] (patToShape pat)

  (pattele, patterm) <- local (flip semCtxComma (SemCtxTele pal [])) $ checkAndEvalPat s [] pat

  semEnv <- asks ctxToEnv

  let vpat   = N.evalPat semEnv pat
      tarty  = N.recoverPatType vpat
      motvar = N.makeVarValS tarty size

  local (flip semCtxComma (SemCtxTele OneSemPal [CtxEntry motvar tarty (Col (CommaSl (Sub s) (Sub IdSl)))])) $ checkTy s mot

  check s tar tarty

  let (_, patterm) = N.makeVPatCartTele (N.extSizeComma size (SemTele pal [])) vpat

  local (flip semCtxComma (SemCtxTele pal pattele)) $ check (CommaSl (Sub s) (Sub IdSl)) branch (N.eval (envExtComma semEnv patterm) mot)

  return $ N.eval (envExtSilent semEnv (N.eval semEnv tar)) mot

synth s a = throwError $ "cannot synth the type of " ++ show a

-- This duplicates some logic in `Normalise` but I think this avoids
-- being accidentally quadratic by repeatedly evalling the types

-- At this point the palette has already been added to the context.

-- `s` represents the slice that the match is being checked at, not the
checkAndEvalPat :: SlI -> PatPath -> Pat -> CheckM ([CtxEntry], Value)
checkAndEvalPat s path (VarPat ty) = do
  let c = sliceAtType s path
  checkTy c ty
  size <- asks (ctxSize s)
  env <- asks ctxToEnv

  let vty = N.eval env ty
      v = N.makeVarValS vty size

  return $ ([CtxEntry v vty (Col c)], v)

checkAndEvalPat s path (ZeroVarPat ty) = do
  checkTy OneSl ty
  size <- asks (ctxSize s)
  env <- asks ctxToEnv

  let vty = N.eval env ty
      v = N.makeZeroVarValS vty size

  return $ ([CtxEntry v vty Marked], v)

checkAndEvalPat s _ OnePat = pure ([], VOneIn)
checkAndEvalPat s path (UndInPat p) = do
  (ptele, pterm) <- checkAndEvalPat s undefined p -- FIXME: this is stupid
  return $ (ptele, VUndIn pterm)
checkAndEvalPat s path UnitPat = do
  size <- asks (ctxSize s)
  let u = N.makeUnitVal size path
  return ([], VUnitIn u)
checkAndEvalPat s path (PairPat p q) = do
  (ptele, pterm) <- checkAndEvalPat s (LeftCommaPath : path) p
  (qtele, qterm) <- local (ctxExtMany ptele) $ checkAndEvalPat s (RightCommaPath : path) q
  return (qtele ++ ptele, VPair pterm qterm)
checkAndEvalPat s path (ReflPat p) = do
  (ptele, pterm) <- checkAndEvalPat s path p
  return (ptele, VPair pterm (VPair pterm (VRefl pterm)))
checkAndEvalPat s path (TensorPat p q) = do
  size <- asks (ctxSize s)
  let psl = N.makeSliceVal size (LeftTensorPath : path)
      qsl = N.makeSliceVal size (RightTensorPath : path)
  (ptele, pterm) <- checkAndEvalPat s (LeftTensorPath : path) p
  (qtele, qterm) <- local (ctxExtMany ptele) $ checkAndEvalPat s (RightTensorPath : path) q
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
checkTy s (Id aty a b) = do
  checkTy s aty
  aty' <- eval aty
  check s a aty'
  check s b aty'
checkTy s (Und ty) = do
  checkTy OneSl ty
checkTy s (Tensor aty bty) = do
  checkTy OneSl aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtValZero var atyval) $ checkTy OneSl bty
checkTy s Unit = return ()
checkTy s (Hom aty bty) = do
  checkTy OneSl aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtHom var atyval) $ checkTy (TensorSl (Sub s) (Sub IdSl)) bty
checkTy s a = do
  ty <- synth s a
  case ty of
    VUniv l -> return ()
    t -> throwError $ "Expected " ++ show a ++ " to synth universe, instead got " ++ show t
