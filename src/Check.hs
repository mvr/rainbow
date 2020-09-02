module Check where

import Control.Monad.Reader
import Control.Monad.Except
import Data.Functor.Identity

import qualified Normalize as N
import Palette
import Syntax

type Err = String

data CtxEntry = CtxTerm Value VTy (Maybe ColourIndex)
              | CtxTopLevel Value Ty
  deriving (Show)
              
data SemCtx = SemCtx { ctxPal :: Palette, ctxVars :: [CtxEntry] }

ctxEntryWkColHom :: Palette -> CtxEntry -> CtxEntry
ctxEntryWkColHom pal (CtxTerm t ty (Just c')) = CtxTerm t ty (Just $ colExtHom c')
ctxEntryWkColHom pal (CtxTerm t ty Nothing) = CtxTerm t ty Nothing
ctxEntryWkColHom pal (CtxTopLevel t ty) = CtxTopLevel t ty

ctxExtVal :: Value -> Value -> SemCtx -> SemCtx
ctxExtVal a aty (SemCtx pal vars) = SemCtx pal ((CtxTerm a aty (Just TopColour)):vars)

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

newtype CheckM a = CheckM (ReaderT SemCtx (ExceptT Err Identity) a)
  deriving (Functor, Applicative, Monad, MonadError Err, MonadReader SemCtx)

evalAndVar :: Ty -> CheckM (VTy, Value)
evalAndVar aty = do
  semEnv <- asks ctxToEnv
  let atyval = N.eval semEnv aty
  lev <- asks ctxLen
  let var = makeVarVal atyval lev
  return (atyval, var)

check :: Term -> Value -> CheckM ()

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
  ty' <- synth a
  lev <- asks ctxLen
  when (not $ N.eqTy lev ty ty') $ throwError $ "type mismatch, expected: " ++ show ty ++ " got " ++ show ty'

synth :: Term -> CheckM VTy
synth = undefined

checkTy :: Ty -> CheckM ()
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
    t -> throwError "Expected universe"
