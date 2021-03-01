{-# LANGUAGE NamedFieldPuns #-}
module Driver (emptyEnv, processDecl) where

import Debug.Trace

import Control.Monad.State
import Data.List (findIndex, find)
import Data.Maybe (fromJust, fromMaybe)

import qualified Concrete as C
import qualified Syntax as S
import qualified Check as S
import qualified Normalize as N
import Palette

-- The name is optional so we can conveniently write
-- e.g. non-dependent sums and products
data BindEntry = BindTerm (Maybe C.Ident)
               | BindTopLevel C.Ident
  deriving (Show)

data Bindings = Bindings { bindVars :: [BindEntry] }

bindsLookup :: Bindings -> C.Ident -> Int
bindsLookup binds name = case findIndex (\be -> case be of
                                            BindTerm (Just n') -> name == n'
                                            BindTerm Nothing   -> False
                                            BindTopLevel n'    -> name == n') (bindVars binds) of
  Just i -> i
  Nothing -> error $ "Unbound variable " ++ name

bindsExt :: Bindings -> Maybe C.Ident -> Bindings
bindsExt binds@(Bindings { bindVars }) name = binds { bindVars = (BindTerm name):bindVars }

bindsExtMany :: Bindings -> [BindEntry] -> Bindings
bindsExtMany binds@(Bindings { bindVars }) names = binds { bindVars = names ++ bindVars }

-- guessSlice :: C.Palette -> Bindings -> C.Term -> C.Slice
-- guessSlice pal env (C.Check a ty) = guessSlice pal env a
-- guessSlice pal env (C.Var name) = C.Slice [bindsLookupColour env name]
-- guessSlice pal env (C.ZeroVar name) = C.Slice []
-- guessSlice pal env (C.Univ i) = C.Slice []
-- guessSlice pal env (C.Lam name t) = guessSlice pal env t
-- guessSlice pal env (C.App f []) = guessSlice pal env f
-- guessSlice pal env (C.App f args) = guessSlice pal env (C.App f (init args)) `C.sliceUnion` guessSlice pal env (last args)
-- guessSlice pal env (C.Pair a b) = (guessSlice pal env a) `C.sliceUnion` (guessSlice pal env b)
-- guessSlice pal env (C.Fst p) = guessSlice pal env p
-- guessSlice pal env (C.Snd p) = guessSlice pal env p
-- guessSlice pal env (C.UndIn a) = guessSlice pal env a
-- guessSlice pal env (C.UndOut a) = guessSlice pal env a
-- guessSlice pal env (C.TensorPair slL a slR b) = (guessSlice pal env a) `C.sliceUnion` (guessSlice pal env b)
-- -- guessSlice pal env (C.TensorElim s z mot (x, xc) (y, yc) br) = (guessSlice pal env s) `C.sliceUnion` (guessSlice pal env mot) `C.sliceUnion` (guessSlice pal env br)
-- -- guessSlice pal env (C.TensorElimFrob psi omega theta z mot (x, xc) (y, yc) c) = (guessSliceTele pal env theta) `C.sliceUnion` (guessSlice pal env c)
-- guessSlice pal env (C.HomLam bodyc yc y body) = guessSlice pal env body
-- guessSlice pal env (C.HomApp slL f slR a) = (guessSlice pal env f) `C.sliceUnion` (guessSlice pal env a)

bindColour :: C.Palette -> C.Ident -> Maybe SlI
bindColour C.OnePal col = Nothing
bindColour C.OriginPal col = Nothing
bindColour (C.UnitPal _) col = Nothing
bindColour (C.LabelPal i s) col
  | i == col = Just TopSl
  | otherwise = bindColour s col
bindColour (C.CommaPal l r) col =
  case (bindColour l col, bindColour r col) of
    (Nothing, Nothing) -> Nothing
    (Nothing, Just TopSl) -> Just (CommaSl No Yes)
    (Just TopSl, Nothing) -> Just (CommaSl Yes No)
    (Nothing, Just r) -> Just (CommaSl No (Sub r))
    (Just l, Nothing) -> Just (CommaSl (Sub l) No)
bindColour (C.TensorPal l r) col =
  case (bindColour l col, bindColour r col) of
    (Nothing, Nothing) -> Nothing
    (Nothing, Just TopSl) -> Just (TensorSl No Yes)
    (Just TopSl, Nothing) -> Just (TensorSl Yes No)
    (Nothing, Just r) -> Just (TensorSl No (Sub r))
    (Just l, Nothing) -> Just (TensorSl (Sub l) No)

bindSlice :: C.Palette -> C.Slice -> Maybe SlI
bindSlice pal (C.Slice cols) = mconcat <$> traverse (bindColour pal) cols

bindUnit :: C.Palette -> C.Unit -> Maybe UnitI
bindUnit = undefined

type SymCounter = Int

genColLike :: C.Ident -> State SymCounter C.Ident
genColLike n = do
  i <- get
  put (i+1)
  return $ "?" ++ n ++ show i

patPal :: C.Pat -> C.Palette
patPal = undefined

patVars :: C.Pat -> [BindEntry]
patVars C.OnePat = []
patVars (C.UnitPat _) = []
patVars (C.VarPat x _) = [BindTerm (Just x)]
patVars (C.PairPat p q) = patVars q ++ patVars p
patVars (C.TensorPat _ p _ q) = patVars q ++ patVars p

bindPat :: C.Palette -> Bindings -> C.Pat -> State SymCounter S.Pat
bindPat pal env (C.OnePat) = pure S.OnePat
bindPat pal env (C.UnitPat _) = pure S.UnitPat
bindPat pal env (C.VarPat _ ty) = S.VarPat <$> bind pal env ty
bindPat pal env (C.PairPat p q) = do
  p' <- bindPat pal env p
  q' <- bindPat pal (bindsExtMany env (patVars p)) q
  return $ S.PairPat p' q'
bindPat pal env (C.TensorPat _ p _ q) = do
  p' <- bindPat pal env p
  q' <- bindPat pal (bindsExtMany env (patVars p)) q
  return $ S.TensorPat p' q'

bind :: C.Palette -> Bindings -> C.Term -> State SymCounter S.Term
bind pal env (C.Check a ty) = S.Check <$> (bind pal env a) <*> (bind pal env ty)
bind pal env (C.Var name) = pure $ S.Var (bindsLookup env name)
bind pal env (C.ZeroVar name) = pure $ S.ZeroVar (bindsLookup env name)
bind pal env (C.Univ i) = pure (S.Univ i)
bind pal env (C.Lam [] t) = bind pal env t
bind pal env (C.Lam (name:names) t) = S.Lam <$> (bind pal (bindsExt env (Just name)) (C.Lam names t))
bind pal env (C.App f []) = bind pal env f
bind pal env (C.App f args) = S.App <$> (bind pal env (C.App f (init args))) <*> (bind pal env (last args)) -- yes this could be done better
bind pal env (C.Pair a b) = S.Pair <$> (bind pal env a) <*> (bind pal env b)
bind pal env (C.Fst p) = S.Fst <$> (bind pal env p)
bind pal env (C.Snd p) = S.Snd <$> (bind pal env p)
bind pal env (C.UndIn a) = S.UndIn <$> (bind pal env a)
bind pal env (C.UndOut a) = S.UndOut <$> (bind pal env a)
bind pal env (C.Pi [] b) = bind pal env b
bind pal env (C.Pi (C.TeleCell n ty : cells) b) = S.Pi <$> (bind pal env ty) <*> (bind pal (bindsExt env n) (C.Pi cells b))
bind pal env (C.Sg [] b) = bind pal env b
bind pal env (C.Sg (C.TeleCell n ty : cells) b) = S.Sg <$> (bind pal env ty) <*> (bind pal (bindsExt env n) (C.Sg cells b))
bind pal env (C.Und a) = S.Und <$> bind pal env a
bind pal env (C.Tensor n a b) = S.Tensor <$> bind pal env a <*> bind pal (bindsExt env n) b
bind pal env (C.Hom n a b) = S.Hom <$> bind pal env a <*> bind pal (bindsExt env n) b

bind pal env t@(C.TensorPair slL a slR b) = do
  -- let slL' = fromMaybe (guessSlice pal env a) slL
  --     slR' = fromMaybe (guessSlice pal env b) slR
  let slL' = fromJust slL
      slR' = fromJust slR
  bounda <- bind pal env a
  boundb <- bind pal env b

  return $ S.TensorPair (fromJust $ bindSlice pal slL') bounda (fromJust $ bindSlice pal slR') boundb

bind pal env (C.HomLam bodyc yc y body) = do
  bodyc' <- case bodyc of
           Just bodyc -> pure bodyc
           Nothing -> genColLike "t"
  yc' <- case yc of
           Just yc -> pure yc
           Nothing -> genColLike y

  boundbody <- bind (C.TensorPal (C.LabelPal bodyc' pal) (C.LabelPal yc' C.OnePal)) (bindsExt env (Just y)) body
  return $ S.HomLam boundbody

bind pal env (C.HomApp slL f slR a) = do
  -- let slL' = fromMaybe (guessSlice pal env f) slL
  --     slR' = fromMaybe (guessSlice pal env a) slR
  let slL' = fromJust slL
      slR' = fromJust slR

  boundf <- bind pal env f
  bounda <- bind pal env a

  return $ S.HomApp
    (fromJust $ bindSlice pal slL')
    boundf
    (fromJust $ bindSlice pal slR')
    bounda

bind pal env (C.Match t z mot patterm br) = do
  boundt <- bind pal env t

  let pat = fromJust $ C.comprehendPat patterm

  boundmot <- bind (C.CommaPal pal C.OnePal) (bindsExt env z) mot

  let patpal = patPal pat
  boundpat <- bindPat (C.CommaPal pal patpal) env pat

  boundbr <- bind (C.CommaPal pal (C.patPalette pat)) (bindsExtMany env (patVars pat)) br

  return $ S.Match boundt boundmot boundpat boundbr

data Env = Env { envBindings :: Bindings, envCheckCtx :: S.SemCtx }

processDecl :: Env -> C.Decl -> IO Env
processDecl env@(Env binds@(Bindings bindings) checkCtx) (C.Def name cbody cty) = do
  let body = evalState (bind C.OriginPal binds cbody) 0
  let ty = evalState (bind C.OriginPal binds cty) 0

  case S.runCheckM checkCtx $ S.checkTy TopSl ty of
    Left err -> putStrLn $ "Error in type of " ++ name ++ ": " ++ err
    Right () -> return ()

  let semEnv = S.ctxToEnv checkCtx
  let semTy = N.eval semEnv ty

  case S.runCheckM checkCtx $ S.check TopSl body semTy of
    Left err -> putStrLn $ "Error in: " ++ name ++ ": " ++ err
    Right () -> putStrLn $ "Checked: " ++ name

  let semBody = N.eval semEnv body

  return (Env (Bindings ((BindTopLevel name):bindings)) (S.ctxExtGlobal semBody semTy checkCtx))

-- processDecl env@(Env binds checkEnv) (C.Dont name cbody cty) = do
--   let body = evalState (bind (C.Palette []) binds cbody) 0
--   let ty = bindTy binds cty

--   case S.runCheckM checkEnv $ S.check body ty of
--     Left err -> putStrLn $ "Correctly failed: " ++ name ++ " because " ++ err
--     Right () -> putStrLn $ "Error: " ++ name ++ " should not have typechecked!"

--   return env

emptyEnv :: Env
emptyEnv = Env (Bindings []) (S.ctxEmpty)
