module Check where

import Debug.Trace

import Control.Monad.Reader
import Control.Monad.Except
import Data.Functor.Identity

import qualified Normalize as N
import Palette
import Syntax

type Err = String

data CtxEntry = CtxTerm Value VTy (Maybe ColourIndex)
              | CtxTopLevel Value VTy
  deriving (Eq, Show)

-- Newest variable first
data SemCtx = SemCtx { ctxPal :: Palette, ctxVars :: [CtxEntry] }
  deriving (Eq, Show)

ctxEmpty :: SemCtx
ctxEmpty = SemCtx emptyPal []

data SemTele = SemTele { semTelePal :: Palette, semTeleVars :: [(Value, VTy, (Maybe ColourIndex))] }
  deriving (Eq, Show)

ctxLookupVar :: Int -> SemCtx -> (VTy, Maybe ColourIndex)
ctxLookupVar ix (SemCtx _ vars) = case vars !! ix of
  CtxTerm _ ty c -> (ty, c)
  CtxTopLevel _ ty -> (ty, Just TopColour)

ctxExtValCol :: Value -> Value -> ColourIndex -> SemCtx -> SemCtx
ctxExtValCol a aty c (SemCtx pal vars) = SemCtx pal ((CtxTerm a aty (Just c)):vars)

ctxExtVal :: Value -> Value -> SemCtx -> SemCtx
ctxExtVal a aty  = ctxExtValCol a aty TopColour

ctxExtTop :: Value -> Value -> SemCtx -> SemCtx
ctxExtTop a aty (SemCtx pal vars) = SemCtx pal ((CtxTopLevel a aty):vars)

ctxEntryWkCol :: Int -> Palette -> ColourIndex -> CtxEntry -> CtxEntry
ctxEntryWkCol amt pal c (CtxTerm v ty (Just c')) = CtxTerm v ty (Just $ colWkAt amt pal c c')
ctxEntryWkCol amt pal c (CtxTerm v ty Nothing) = CtxTerm v ty Nothing
ctxEntryWkCol amt pal c (CtxTopLevel v ty) = CtxTopLevel v ty

ctxEntryWkColHom :: Palette -> CtxEntry -> CtxEntry
ctxEntryWkColHom pal (CtxTerm t ty (Just c')) = CtxTerm t ty (Just $ colExtHom c')
ctxEntryWkColHom pal (CtxTerm t ty Nothing) = CtxTerm t ty Nothing
ctxEntryWkColHom pal (CtxTopLevel t ty) = CtxTopLevel t ty

ctxExtTele :: SemTele -> SemCtx -> SemCtx
ctxExtTele (SemTele psi teleVars) (SemCtx pal vars) = SemCtx (palExtend psi pal) (teleentries ++ wkvars)
  where teleentries = fmap (\(v, ty, c) -> CtxTerm v ty c) teleVars
        wkvars = fmap (ctxEntryWkCol (palSize psi) pal TopColour) vars

ctxExtValZero :: Value -> Value -> SemCtx -> SemCtx
ctxExtValZero a aty (SemCtx pal vars) = SemCtx pal ((CtxTerm a aty Nothing):vars)

ctxExtHom :: Value -> VTy -> SemCtx -> SemCtx
ctxExtHom t ty (SemCtx pal vars)
  = SemCtx { ctxPal = Palette [TensorPal pal (Palette [])],
             ctxVars = (CtxTerm t ty (Just rightCol)) : (fmap (ctxEntryWkColHom pal) vars)
           }
  where rightCol = RightSub 0 TopColour

ctxEntryRestrict :: SliceIndex -> CtxEntry -> CtxEntry
ctxEntryRestrict sl (CtxTerm t ty c) = CtxTerm t ty (c >>= flip colourRestrict sl)
ctxEntryRestrict sl (CtxTopLevel t ty) = CtxTopLevel t ty

ctxRestrict :: SliceIndex -> SemCtx -> SemCtx
ctxRestrict sl (SemCtx { ctxPal, ctxVars })
  = SemCtx { ctxPal = palRestrict ctxPal sl,
             ctxVars = fmap (ctxEntryRestrict sl) ctxVars }

ctxLen :: SemCtx -> Int
ctxLen = length . ctxVars

ctxToEnv :: SemCtx -> SemEnv
ctxToEnv (SemCtx _ vars)
  = fmap (\case
             CtxTerm t _ _ -> t
             CtxTopLevel t _ -> t)
    vars

teleToEnv :: SemTele -> SemEnv
teleToEnv (SemTele _ vars) = fmap (\(t, _, _) -> t) vars

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

check :: Term -> Value -> CheckM ()
-- check t ty | traceShow ("Check: " ++ show (t, ty)) False = undefined

check (Univ i) (VUniv j) | i < j = return ()
check (Univ i) t = throwError $ "Expecting universe over " ++ show i

check (Pi aty bty) (VUniv l) = do
  check aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtVal var atyval) $ check bty (VUniv l)
check (Pi aty bclo) t = throwError "Expected universe"

check (Lam b) (VPi aty bclo) = do
  lev <- asks ctxLen
  let var = makeVarVal aty lev
  let bty = N.doClosure bclo var
  local (ctxExtVal var aty) $ check b bty
check (Lam b) ty = throwError "Unexpected lambda"

check (Sg aty bty) (VUniv l) = do
  check aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtVal var atyval) $ check bty (VUniv l)
check (Sg aty bclo) t = throwError "Expected universe"

check (Pair a b) (VSg aty bclo) = do
  check a aty
  semEnv <- asks ctxToEnv
  let aval = N.eval semEnv a
  check b (N.doClosure bclo aval)
check (Pair a b) ty = throwError "Unexpected pair"

check (Und ty) (VUniv l) = do
  local (ctxRestrict BotSlice) $ check ty (VUniv l)
check (Und ty) t = throwError "Expected universe"

check (UndIn a) (VUnd aty) = do
  local (ctxRestrict BotSlice) $ check a aty
check (UndIn a) aty = throwError "Unexpected natural intro"

check (Tensor aty bty) (VUniv l) = do
  local (ctxRestrict BotSlice) $ check aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtValZero var atyval . ctxRestrict BotSlice) $ check bty (VUniv l)
check (Tensor aty bclo) t = throwError "Expected universe"

check t@(TensorPair asl a bsl b) (VTensor aty bclo) = do
  -- traceShow "checking tensor pair" $ return ()
  -- e <- ask
  -- traceShow e $ return ()

  when (not $ validSplit (asl, bsl)) $ throwError "Invalid split"

  local (ctxRestrict asl) $ check a aty
  semEnv <- asks ctxToEnv
  let aval = N.eval semEnv a
  local (ctxRestrict bsl) $ check b (N.doClosure bclo aval)
check (TensorPair _ _ _ _) ty = throwError "Unexpected tensor intro"

check (Hom aty bty) (VUniv l) = do
  local (ctxRestrict BotSlice) $ check aty (VUniv l)
  (atyval, var) <- evalAndVar aty
  local (ctxExtHom var atyval) $ check bty (VUniv l)
check (Hom aty bclo) t = throwError "Expected universe"

check (HomLam b) (VHom aty bclo) = do
  lev <- asks ctxLen
  let var = makeVarVal aty lev
  let bty = N.doClosure bclo var
  local (ctxExtHom var aty) $ check b bty
check (HomLam b) ty = throwError "Unexpected hom lambda"

check a ty = do
  -- e <- asks ctxToEnv
  -- traceShow e $ return ()
  ty' <- synth a
  lev <- asks ctxLen
  when (not $ N.eqTy lev ty ty') $ throwError $ "type mismatch, expected: " ++ show ty ++ " got " ++ show ty'

synth :: Term -> CheckM VTy
-- synth t | traceShow ("Synth: " ++ show t) False = undefined
synth (Var i) = do
  -- s <- ask
  -- traceShow s (return ())
  (ty, c) <- asks (ctxLookupVar i)
  when (c /= Just TopColour) $ throwError $ "Cannot use variable " ++ show i
  return ty

synth (ZeroVar i) = do
  (ty, c) <- asks (ctxLookupVar i)
  lev <- asks ctxLen
  return (N.zero ty)

synth (Check a aty) = do
  semEnv <- asks ctxToEnv
  let tyval = N.eval semEnv aty
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
    (VSg aty bclo) -> do
      semEnv <- asks ctxToEnv
      let aval = N.eval semEnv (Fst p)
      return $ N.doClosure bclo aval
    _ -> throwError "expected Sg type"

synth (App f a) = do
  fty <- synth f
  case fty of
    (VPi aty bclo) -> do
      check a aty
      semEnv <- asks ctxToEnv
      let aval = N.eval semEnv a
      return $ N.doClosure bclo aval
    _ -> throwError "expected Pi type"

synth (HomApp fsl f asl a) = do
  when (not $ validSplit (fsl, asl)) $ throwError "Invalid split"

  fty <- local (ctxRestrict fsl) $ synth f
  case fty of
    (VHom aty bclo) -> do
      local (ctxRestrict asl) $ check a aty
      semEnv <- asks ctxToEnv
      let aval = N.eval semEnv a
      return $ N.doClosure bclo aval
    _ -> throwError "expected Hom type"

synth (UndOut n) = do
  nty <- synth n
  case nty of
    (VUnd aty) -> return aty
    _ -> throwError "expected Und type"


-- synth (TensorElim t mot br) = do
--   tty <- synth t

--   (aty, bclo) <- case tty of
--                   (VTensor aty bclo) -> return (aty, bclo)
--                   _ -> throwError "expected target to be Tensor"

--   lev <- asks ctxLen

--   let mott = makeVarVal (VTensor aty bclo) lev
--   local (ctxExtVal mott (VTensor aty bclo)) $ checkTy mot

--   let psi = Palette []
--   let (psi', r, b) = palAddTensor psi TopColour
--   let bra = makeVarVal aty lev
--       brbty = N.doClosure bclo bra
--       brb = makeVarVal brbty (lev+1)
--       brtele = SemTele psi' [(brb, brbty, Just b), (bra, aty, Just r)]

--   semEnv <- asks ctxToEnv

--   local (ctxExtTele brtele) $ check br (N.eval (VTensorPair bra brb : semEnv) mot)

--   return $ N.eval ((N.eval semEnv t) : semEnv) mot

-- --synth (TensorElimFrob psi omega theta tIdx mot br) | traceShow (psi, omega, theta, tIdx, mot, br) False = undefined
-- synth (TensorElimFrob psi omega theta tIdx mot br) = do
--   -- TODO: add sanity checks on the lengths of psi omega theta etc

--   local (ctxExtTele (SemTele psi [])) $ checkTeleSubst psi omega theta

--   mottele <- evalTele psi omega
--   local (ctxExtTele mottele) $ checkTy mot

--   let (_, (_, tty, Just zcol):teletysbefore) = splitAt (length omega - tIdx - 1) (semTeleVars mottele)
--   (aty, bclo) <- case tty of
--                    (VTensor aty bclo) -> return (aty, bclo)
--                    _ -> throwError "expected target to be Tensor"

--   let (psi', r, b) = palAddTensor psi zcol
--   let (_, _:omegaafter) = splitAt tIdx omega
--   lev <- asks ctxLen
--   let bra = makeVarVal aty (lev + length teletysbefore)
--       brbty = N.doClosure bclo bra
--       brb = makeVarVal brbty (lev + length teletysbefore + 1)

--       doWk = fmap (\(t, ty, c) -> (t, ty, fmap (colWkAt 1 psi' zcol) c))
--       doWk2 = fmap (\(c, ty) -> (colWkAt 1 psi' zcol c, ty))

--   let telebeforeandtensor = SemTele psi' ((VTensorPair bra brb, VTensor aty bclo, Just $ colWkAt 1 psi' zcol zcol) : doWk teletysbefore)

--   teleafter <- local (ctxExtTele telebeforeandtensor) $ evalTele emptyPal (doWk2 omegaafter)

--   -- traceShow "in tensorelimfrob:" $ return ()
--   -- traceShow telebeforeandtensor $ return ()
--   -- traceShow omegaafter $ return ()
--   -- traceShow teleafter $ return ()

--   let telesplit = SemTele psi' (semTeleVars teleafter ++ [(brb, brbty, Just b), (bra, aty, Just r)] ++ teletysbefore)
--       subunsplit = teleToEnv teleafter ++ teleToEnv telebeforeandtensor

--   semEnv <- asks ctxToEnv
--   local (ctxExtTele telesplit) $ check br (N.eval (subunsplit ++ semEnv) mot)

--   thetaval <- evalSubst psi omega theta

--   return $ N.eval (thetaval ++ semEnv) mot

synth a = throwError $ "cannot synth the type of " ++ show a

checkTeleSubst :: Palette -> [(ColourIndex, Ty)] -> TeleSubst -> CheckM ()
checkTeleSubst psi cs (TeleSubst kappa as) = go cs as []
  where go [] [] teleenv = return ()
        go ((c,ty):cs) (a:as) teleenv = do
          semEnv <- asks ctxToEnv
          let tyval = N.eval (teleenv ++ semEnv) ty
          local (ctxRestrict (sliceWkTop (palSize psi) $ sliceSubst (colourToSlice c) kappa)) $ check a tyval
          go cs as (N.eval semEnv a : teleenv)

evalTele :: Palette -> [(ColourIndex, Ty)] -> CheckM SemTele
evalTele pal [] = return $ SemTele pal []
evalTele pal ((c, ty):cs) = do
  semEnv <- asks ctxToEnv
  lev <- asks ctxLen
  let tyval = N.eval semEnv ty
      var = makeVarVal tyval lev
  traceShow "in evalTele:" $ return ()
  traceShow semEnv $ return ()
  traceShow ty $ return ()
  traceShow tyval $ return ()
  (SemTele _ vs) <- local (ctxExtValCol var tyval c) $ evalTele pal cs
  return (SemTele pal (vs ++ [(var, tyval, Just c)]))

evalSubst :: Palette -> [(ColourIndex, Ty)] -> TeleSubst -> CheckM [Value]
evalSubst psi [] (TeleSubst kappa []) = return [] -- TODO: check the palette subst?
evalSubst psi ((c,ty):cs) (TeleSubst kappa (a:as)) = do
  semEnv <- asks ctxToEnv
  let tyval = N.eval semEnv ty
      aval = (N.eval semEnv a)
  vs <- local (ctxExtValCol aval tyval c) $ evalSubst psi cs (TeleSubst kappa as)
  return $ (aval:vs)

checkTy :: Ty -> CheckM ()
-- checkTy t | traceShow ("Check ty: " ++ show t) False = undefined
checkTy (Univ i) = return ()
checkTy (Pi aty bty) = do
  checkTy aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtVal var atyval) $ checkTy bty
checkTy (Sg aty bty) = do
  checkTy aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtVal var atyval) $ checkTy bty
checkTy (Und ty) = do
  local (ctxRestrict BotSlice) $ checkTy ty
checkTy (Tensor aty bty) = do
  local (ctxRestrict BotSlice) $ checkTy aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtValZero var atyval . ctxRestrict BotSlice) $ checkTy bty
checkTy (Hom aty bty) = do
  local (ctxRestrict BotSlice) $ checkTy aty
  (atyval, var) <- evalAndVar aty
  local (ctxExtHom var atyval) $ checkTy bty
checkTy a = do
  ty <- synth a
  case ty of
    VUniv l -> return ()
    t -> throwError $ "Expected " ++ show a ++ " to synth universe, instead got " ++ show t
