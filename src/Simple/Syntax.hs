{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
module Simple.Syntax where

import Debug.Trace

import Control.Monad (forM)
import Control.Monad.Reader
import Control.Monad.Except
import Data.Functor.Identity

import Palette

data Ty where
  BaseTy :: Int -> Ty

  Pi :: Ty -> Ty -> Ty -- Not actually dependent
  Sg :: Ty -> Ty -> Ty

  Und :: Ty -> Ty
  Tensor :: Ty -> Ty -> Ty
  Hom :: Ty -> Ty -> Ty
  deriving (Eq, Show)

data Tele where
  Tele :: Palette -> [(ColourIndex, Ty)] -> Tele -- Maybe ColourIndex
  deriving (Show)

data TeleSubst where
  TeleSubst :: PaletteSubst -> [Term] -> TeleSubst
  deriving (Show)

data Term where 
  Check :: Term -> Ty -> Term

  Var :: Int -> Term -- DeBruijn indices for variables
  ZeroVar :: Int -> Term

  Lam :: Term -> Term
  App :: Term -> Term -> Term

  Pair :: Term -> Term -> Term
  Fst :: Term -> Term
  Snd :: Term -> Term
  
  UndIn :: Term -> Term
  UndOut :: Term -> Term
  
  TensorPair :: SliceIndex -> Term -> SliceIndex -> Term -> Term
  TensorElim :: Palette -> [ColourIndex] -> TeleSubst -> {- which var in tele -} Int -> {- motive -} Ty -> {- branch -} Term -> Term

  HomLam :: Term -> Term
  HomApp :: SliceIndex -> Term -> SliceIndex -> Term -> Term

  deriving (Show)

tensorElimSimple :: Term -> {- motive -} Ty -> {- branch -} Term -> Term
tensorElimSimple s mot c = TensorElim (Palette []) [TopColour] (TeleSubst (PaletteSubst []) [s]) 0 mot c 

data EnvEntry = EnvTerm (Maybe ColourIndex) Ty
              | EnvTopLevel Ty
  deriving (Show)             
              
data Env = Env { envPal :: Palette, envVars :: [EnvEntry] }
  deriving (Show)

emptyEnv :: Env
emptyEnv = Env emptyPal []

envLookupVarCol :: Env -> Int -> Maybe ColourIndex
envLookupVarCol (Env { envVars }) i = case envVars !! i of
  EnvTerm c _ -> c
  EnvTopLevel _ -> Just TopColour

envLookupVar :: Env -> Int -> (Maybe ColourIndex, Ty)
envLookupVar (Env { envVars }) i = case envVars !! i of
  EnvTerm c ty -> (c, ty)
  EnvTopLevel ty -> (Just TopColour, ty)

envEntryRestrict :: SliceIndex -> EnvEntry -> EnvEntry
envEntryRestrict sl (EnvTerm c ty) = EnvTerm (c >>= flip colourRestrict sl) ty
envEntryRestrict sl (EnvTopLevel ty) = EnvTopLevel ty

envEntryWkCol :: Int -> Palette -> ColourIndex -> EnvEntry -> EnvEntry
envEntryWkCol amt pal c (EnvTerm (Just c') ty) = EnvTerm (Just $ palWkAt amt pal c c') ty 
envEntryWkCol amt pal c (EnvTerm Nothing ty) = EnvTerm Nothing ty
envEntryWkCol amt pal c (EnvTopLevel ty) = EnvTopLevel ty

envEntryWkColHom :: Palette -> EnvEntry -> EnvEntry
envEntryWkColHom pal (EnvTerm (Just c') ty) = EnvTerm (Just $ palWkTensor pal c') ty 
envEntryWkColHom pal (EnvTerm Nothing ty) = EnvTerm Nothing ty
envEntryWkColHom pal (EnvTopLevel ty) = EnvTopLevel ty

envRestrict :: SliceIndex -> Env -> Env
envRestrict sl (Env { envPal, envVars }) 
  = Env { envPal = palRestrict envPal sl,
          envVars = fmap (envEntryRestrict sl) envVars }

envExtendTele :: Tele -> Env -> Env
envExtendTele (Tele telePal teleVars) (Env envPal envVars ) 
  = Env { envPal = palExtend telePal envPal,
          envVars = fmap (\(c, ty) -> EnvTerm (Just c) ty) teleVars ++ fmap (envEntryWkCol (length teleVars) envPal TopColour) envVars }

envExtendSingle :: Ty -> Env -> Env
envExtendSingle ty m@(Env _ vars) = m { envVars = (EnvTerm (Just TopColour) ty) : vars }  

envExtendSingleHom :: Ty -> Env -> Env
envExtendSingleHom ty (Env pal vars) 
  = Env { envPal = Palette [TensorPal pal (Palette [])],
          envVars = (EnvTerm (Just rightCol) ty) : (fmap (envEntryWkColHom pal) vars)
        }  
  where rightCol = RightSub 0 TopColour

envExtendTop :: Ty -> Env -> Env
envExtendTop ty m@(Env _ vars) = m { envVars = (EnvTopLevel ty) : vars }  

type Err = String

newtype CheckM a = CheckM (ReaderT Env (ExceptT Err Identity) a)
  deriving (Functor, Applicative, Monad, MonadError Err, MonadReader Env)

runCheckM :: Env -> CheckM a -> Either Err a
runCheckM env (CheckM m) = runIdentity $ runExceptT $ runReaderT m env

check :: Term -> Ty -> CheckM ()

check (Lam b) (Pi aty bty) = do
  local (envExtendSingle aty) $ check b bty
check (Lam b) ty = throwError "Unexpected lambda"

check (HomLam b) (Hom aty bty) = do
  local (envExtendSingleHom aty) $ check b bty
check (HomLam b) ty = throwError "Unexpected hom lambda"
  
check (Pair a b) (Sg aty bty) = do
  check a aty
  check b bty
check (Pair a b) ty = throwError "Unexpected pair"

check t@(TensorPair asl a bsl b) (Tensor aty bty) = do 
  when (not $ validSplit (asl, bsl)) $ throwError "Invalid split"

  local (envRestrict asl) $ check a aty 
  local (envRestrict bsl) $ check b bty 
  
check (TensorPair _ _ _ _) ty = throwError "Unexpected tensor intro"

check (UndIn a) (Und aty) = do
  local (envRestrict BotSlice) $ check a aty 
check (UndIn a) aty = throwError "Unexpected natural intro"

check a ty = do
  ty' <- synth a
  when (ty /= ty') $ throwError $ "type mismatch, expected: " ++ show ty ++ " got " ++ show ty'

synth :: Term -> CheckM Ty
synth (Var i) = do
  (c, ty) <- asks (flip envLookupVar i)
  when (c /= Just TopColour) $ throwError $ "Cannot use variable " ++ show i
  return ty

synth (ZeroVar i) = do
  (c, ty) <- asks (flip envLookupVar i)
  return ty

synth (Check a aty) = do
  check a aty
  return aty

synth (Fst p) = do
  ty <- synth p
  case ty of 
    (Sg a b) -> return a
    _ -> throwError "expected Sg type"

synth (Snd p) = do
  ty <- synth p
  case ty of 
    (Sg a b) -> return b
    _ -> throwError "expected Sg type"

synth (App f a) = do
  fty <- synth f
  case fty of 
    (Pi aty bty) -> do 
      check a aty
      return bty
    _ -> throwError "expected Pi type"

synth (HomApp fsl f asl a) = do
  when (not $ validSplit (fsl, asl)) $ throwError "Invalid split"

  fty <- local (envRestrict fsl) $ synth f
  case fty of 
    (Hom aty bty) -> do 
      local (envRestrict asl) $ check a aty 
      return bty
    _ -> throwError "expected Hom type"

synth (UndOut n) = do
  nty <- synth n
  case nty of
    (Und aty) -> return aty
    _ -> throwError "expected Und type"

synth (TensorElim psi omegacols theta idx mot branch) = do
  tys <- synthTele theta omegacols

  let (omegabefore, zcol:omegaafter) = splitAt idx omegacols
  let (tybefore, zty:tyafter) = splitAt idx tys
  let (psi', r, b) = palAddTensor psi zcol

  (aty, bty) <- case zty of 
                  (Tensor aty bty) -> return (aty, bty)
                  _ -> throwError "expected target to be Tensor"

  -- This is going to be a lot harder with dependent types...
  let omegacols' = (fmap (palWkAt 1 psi' zcol) omegabefore) ++ [r, b] ++ (fmap (palWkAt 1 psi' zcol) omegaafter)
  let tys' = tybefore ++ [aty, bty] ++ tyafter
  let tele = Tele psi' (zip omegacols' tys')

  local (envExtendTele tele) $ check branch mot
  return mot

synth a = throwError $ "cannot synth the type of " ++ show a

synthTele :: TeleSubst -> [ColourIndex] -> CheckM [Ty]
synthTele (TeleSubst kappa as) cs = forM (zip as cs) $ \(a, c) -> 
  local (envRestrict $ sliceSubst (colourToSlice c) kappa) (synth a)


-- synth a sl = do
--   (sl', a') <- synthSynSpl a
--   when (sl /= sl') $ throwError "split mismatch"
--   return a'

-- synthSynSpl :: Term -> CheckM (SliceIndex, Ty)
-- synthSynSpl (Var i) = asks (flip envLookupVar i)

-- synthSynSpl (Fst p) = do
--   (sl, ty) <- synthSynSpl p
--   case ty of 
--     (Sg a b) -> return (sl, a)
--     _ -> throwError "expected Sg type"

-- synthSynSpl (App f a) = do
--   (sl, fty) <- synthSynSpl f
--   case fty of 
--     (Pi aty bty) -> do 
--       check a aty sl
--       return (sl, bty)
--     _ -> throwError "expected Pi type"

-- synthSynSpl a = throwError $ "cannot synth the type of " ++ show a

-- checkSynSpl :: Term -> Ty -> CheckM SliceIndex
-- checkSynSpl (Lam b) (Pi aty bty) = throwError "Lambda requires a slice annotation"

-- checkSynSpl (TensorPair a b) (Tensor aty bty) = do 
--   asl <- checkSynSpl a aty
--   bsl <- checkSynSpl b bty
--   return $ unionSplit (asl, bsl)
-- checkSynSpl (TensorPair a b) ty = throwError "Unexpected tensor intro"

-- checkSynSpl (UndIn a) (Und aty) = do
--   check a aty BotSlice
--   return BotSlice

-- checkSynSpl a ty = do
--   (sl, ty') <- synthSynSpl a
--   when (ty /= ty') $ throwError "type mismatch"
--   return sl
