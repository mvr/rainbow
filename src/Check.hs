module Check where

import Control.Monad.Reader
import Control.Monad.Except
import Data.Functor.Identity

import qualified Normalize as N
import Palette
import Syntax

type Err = String

data SemCtx = SemCtx { ctxPal :: Palette, ctxVars :: [(Value, Value, ColourIndex)] }

ctxExtVal :: Value -> Value -> SemCtx -> SemCtx
ctxExtVal = undefined

ctxLen :: SemCtx -> Int
ctxLen = length . ctxVars

ctxToEnv :: SemCtx -> SemEnv
ctxToEnv = undefined

newtype CheckM a = CheckM (ReaderT SemCtx (ExceptT Err Identity) a)
  deriving (Functor, Applicative, Monad, MonadError Err, MonadReader SemCtx)

check :: Term -> Value -> CheckM ()

check (Lam b) (VPi aty bclo) = do
  lev <- asks ctxLen
  let var = makeVarVal aty lev
  let bty = N.doClosure bclo var
  local (ctxExtVal var aty) $ check b bty
check (Lam b) ty = throwError "Unexpected lambda"

-- check (HomLam b) (Hom aty bty) = do
--   local (envExtendSingleHom aty) $ check b bty
-- check (HomLam b) ty = throwError "Unexpected hom lambda"
  
check (Pair a b) (VSg aty bclo) = do
  check a aty
  semEnv <- asks ctxToEnv
  let asem = N.eval semEnv a
  check b (N.doClosure bclo asem)
check (Pair a b) ty = throwError "Unexpected pair"

-- check t@(TensorPair asl a bsl b) (Tensor aty bty) = do 
--   when (not $ validSplit (asl, bsl)) $ throwError "Invalid split"

--   local (envRestrict asl) $ check a aty 
--   local (envRestrict bsl) $ check b bty 
  
-- check (TensorPair _ _ _ _) ty = throwError "Unexpected tensor intro"

-- check (UndIn a) (Und aty) = do
--   local (envRestrict BotSlice) $ check a aty 
-- check (UndIn a) aty = throwError "Unexpected natural intro"

-- check a ty = do
--   ty' <- synth a
--   when (ty /= ty') $ throwError $ "type mismatch, expected: " ++ show ty ++ " got " ++ show ty'

synth :: Term -> CheckM Ty
synth = undefined
