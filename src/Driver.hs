{-# LANGUAGE NamedFieldPuns #-}
module Driver (emptyEnv, processDecl) where

import Debug.Trace

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Data.List (findIndex, find)
import Data.Maybe (fromJust, fromMaybe)

import qualified Concrete as C
import qualified Syntax as S
import qualified Check as S
import qualified Normalize as N
import Palette

-- The name is optional so we can conveniently write
-- e.g. non-dependent sums and products
data BindEntry = BindTerm {- name -} (Maybe C.Ident) {- colour -} (Maybe C.Ident)
               | BindTopLevel C.Ident
  deriving (Show)

type SymCounter = Int
data BindState = BindState { symCounter :: SymCounter, bindPalette :: C.Palette, binds :: [BindEntry] }
type BindM = Reader BindState

bindsLookup :: C.Ident -> BindM Int
bindsLookup name = do
  vars <- asks binds
  case findIndex (\be -> case be of
                           BindTerm (Just n') _ -> name == n'
                           BindTerm Nothing _   -> False
                           BindTopLevel n'    -> name == n') vars of
    Just i -> return i
    Nothing -> error $ "Unbound variable " ++ name

bindsLookupColour :: C.Ident -> BindM (Maybe C.Ident)
bindsLookupColour name = do
  vars <- asks binds
  case find (\be -> case be of
                      BindTerm (Just n) _ -> name == n
                      BindTerm Nothing _   -> False
                      BindTopLevel _    -> False) vars of
    (Just (BindTerm _ (Just c))) -> return (Just c)
    _ -> return Nothing

-- bindsExt :: [BindEntry] -> Maybe C.Ident -> [BindEntry]
-- bindsExt  }) name = binds { bindVars = (BindTerm name):bindVars }

-- bindsExtMany :: [BindEntry] -> [BindEntry] -> [BindEntry]
-- bindsExtMany

guessSlice :: C.Term -> BindM C.Slice
guessSlice (C.Check a ty) = guessSlice a
guessSlice (C.Var name) = do
  c <- bindsLookupColour name
  case c of
    Just c -> return $ C.Slice [c]
    Nothing -> return $ C.SliceOmitted
guessSlice (C.ZeroVar name) = pure $ C.Slice []
guessSlice (C.Univ i) = pure $ C.Slice []
guessSlice (C.Lam name t) = guessSlice t
guessSlice (C.App f []) = guessSlice f
guessSlice (C.App f args) = C.sliceUnion <$> guessSlice (C.App f (init args)) <*> guessSlice (last args)
guessSlice (C.Pair a b) = C.sliceUnion <$> (guessSlice a) <*> (guessSlice b)
guessSlice (C.Fst p) = guessSlice p
guessSlice (C.Snd p) = guessSlice p
guessSlice (C.UndIn a) = guessSlice a
guessSlice (C.UndOut a) = guessSlice a
guessSlice (C.TensorPair slL a slR b) = C.sliceUnion <$> (guessSlice a) <*> (guessSlice b)
guessSlice (C.HomLam bodyc yc y body) = guessSlice body
guessSlice (C.HomApp slL f slR a) = C.sliceUnion <$> (guessSlice f) <*> (guessSlice a)

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

bindSlice :: C.Slice -> BindM (Maybe SlI)
bindSlice (C.Slice cols) = do
  pal <- asks bindPalette
  return $ mconcat <$> traverse (bindColour pal) cols
bindSlice (C.SliceOne) = return $ Just OneSl

bindUnit :: C.Palette -> C.Unit -> Maybe UnitI
bindUnit = undefined

bindsExtLam :: Maybe C.Ident -> BindState -> BindState
bindsExtLam n state@(BindState { binds }) = state { binds = (BindTerm n Nothing):binds }

bindsExtHom :: Maybe C.Ident -> Maybe C.Ident -> Maybe C.Ident -> BindState -> BindState
bindsExtHom n nc ac state@(BindState { binds, bindPalette })
  = state { bindPalette = pal nc ac,
            binds = (BindTerm n nc):binds }
  where pal Nothing Nothing = C.TensorPal bindPalette C.OnePal
        pal Nothing (Just ac) = C.TensorPal (C.LabelPal ac bindPalette) C.OnePal
        pal (Just nc) Nothing = C.TensorPal bindPalette (C.LabelPal nc C.OnePal)
        pal (Just nc) (Just ac) = C.TensorPal (C.LabelPal ac bindPalette) (C.LabelPal nc C.OnePal)

bindsExtMany :: [BindEntry] -> BindState -> BindState
bindsExtMany ns state@(BindState { binds }) = state { binds = ns ++ binds }

bindsExtCommaPal :: C.Palette -> BindState -> BindState
bindsExtCommaPal pal state@(BindState { bindPalette })
  = state { bindPalette = C.CommaPal bindPalette pal }




-- genColLike :: C.Ident -> BindM C.Ident
-- genColLike n = do
--   i <- asks symCounter
--   put (i+1)
--   return $ "?" ++ n ++ show ix

patVars :: C.Pat -> [BindEntry]
patVars p = go Nothing p
  where
  go c C.OnePat = []
  go c (C.UnitPat _) = []
  go c (C.VarPat x _) = [BindTerm (Just x) c]
  go c (C.ZeroVarPat x _) = [BindTerm (Just x) Nothing]
  go c (C.PairPat p q) = go c q ++ go c p
  go c (C.TensorPat l p r q) = go (Just r) q ++ go (Just l) p
  go c (C.UndInPat p) = go Nothing p

bindPat :: C.Pat -> BindM S.Pat
bindPat (C.OnePat) = pure S.OnePat
bindPat (C.UnitPat _) = pure S.UnitPat
bindPat (C.VarPat _ ty) = S.VarPat <$> bind ty
bindPat (C.ZeroVarPat _ ty) = S.ZeroVarPat <$> bind ty
bindPat (C.UndInPat p) = S.UndInPat <$> bindPat p
bindPat (C.PairPat p q) = do
  p' <- bindPat p
  q' <- local (bindsExtMany (patVars p)) $ bindPat q
  return $ S.PairPat p' q'
bindPat (C.TensorPat _ p _ q) = do
  p' <- bindPat p
  q' <- local (bindsExtMany (patVars p)) $ bindPat q

  return $ S.TensorPat p' q'
bindPat (C.ZeroTensorPat p q) = do
  p' <- bindPat p
  q' <- local (bindsExtMany (patVars p)) $ bindPat q
  return $ S.TensorPat p' q'

bind :: C.Term -> BindM S.Term
bind (C.Check a ty) = S.Check <$> (bind a) <*> (bind ty)
bind (C.Var name) = S.Var <$> (bindsLookup name)
bind (C.ZeroVar name) = S.ZeroVar <$> (bindsLookup name)
bind (C.Univ i) = pure (S.Univ i)
bind (C.Lam [] t) = bind t
bind (C.Lam (name:names) t) = S.Lam <$> (local (bindsExtLam (Just name)) $ bind (C.Lam names t))
bind (C.App f []) = bind f
bind (C.App f args) = S.App <$> (bind (C.App f (init args))) <*> (bind (last args)) -- yes this could be done better
bind (C.Pair a b) = S.Pair <$> (bind a) <*> (bind b)
bind (C.Fst p) = S.Fst <$> (bind p)
bind (C.Snd p) = S.Snd <$> (bind p)
bind (C.UndIn a) = S.UndIn <$> (bind a)
bind (C.UndOut a) = S.UndOut <$> (bind a)
bind (C.Pi [] b) = bind b
bind (C.Pi (C.TeleCell n ty : cells) b) = S.Pi <$> (bind ty) <*> (local (bindsExtLam n) $ bind (C.Pi cells b))
bind (C.Sg [] b) = bind b
bind (C.Sg (C.TeleCell n ty : cells) b) = S.Sg <$> (bind ty) <*> (local (bindsExtLam n) $ bind (C.Sg cells b))
bind (C.Und a) = S.Und <$> bind a
bind (C.Tensor n a b) = S.Tensor <$> bind a <*> local (bindsExtLam n ) (bind b)
bind (C.Hom n nc a ambc b) = S.Hom <$> bind a <*> local (bindsExtHom n nc ambc) (bind b)

bind t@(C.TensorPair sl a sr b) = do
  sl' <- case sl of
    Nothing -> guessSlice a
    (Just sl) -> pure sl
  sr' <- case sr of
    Nothing -> guessSlice b
    (Just sr) -> pure sr
  boundsl <- bindSlice sl'
  boundsr <- bindSlice sr'

  bounda <- bind a
  boundb <- bind b

  return $ S.TensorPair (fromJust $ boundsl) bounda (fromJust $ boundsr) boundb

bind (C.HomLam bodyc yc y body) = do
  boundbody <- local (bindsExtHom (Just y) yc bodyc) $ bind body
  return $ S.HomLam boundbody

bind (C.HomApp sl f sr a) = do
  sl' <- case sl of
    Nothing -> guessSlice f
    (Just sl) -> pure sl
  sr' <- case sr of
    Nothing -> guessSlice a
    (Just sr) -> pure sr
  boundsl <- bindSlice sl'
  boundsr <- bindSlice sr'

  boundf <- bind f
  bounda <- bind a

  return $ S.HomApp
    (fromJust $ boundsl)
    boundf
    (fromJust $ boundsr)
    bounda

bind (C.Match t z mot patterm br) = do
  boundt <- bind t

  let pat = fromJust $ C.comprehendPat patterm

  boundmot <- local (bindsExtLam z) $ bind mot

  let patpal = C.patPalette pat
  boundpat <- local (bindsExtCommaPal patpal) $ bindPat pat

  boundbr <- local (bindsExtCommaPal patpal . bindsExtMany (patVars pat)) $ bind br

  return $ S.Match boundt boundmot boundpat boundbr

data Env = Env { envBindings :: [BindEntry], envCheckCtx :: S.SemCtx }

processDecl :: Env -> C.Decl -> IO Env
processDecl env@(Env bindings checkCtx) (C.Def name cbody cty) = do
  let ty   = runReader (bind cty) (BindState 0 C.OriginPal bindings)
  let body = runReader (bind cbody) (BindState 0 C.OriginPal bindings)

  case S.runCheckM checkCtx $ S.checkTy TopSl ty of
    Left err -> putStrLn $ "Error in type of " ++ name ++ ": " ++ err
    Right () -> return ()

  let semEnv = S.ctxToEnv checkCtx
  let semTy = N.eval semEnv ty

  case S.runCheckM checkCtx $ S.check TopSl body semTy of
    Left err -> putStrLn $ "Error in: " ++ name ++ ": " ++ err
    Right () -> putStrLn $ "Checked: " ++ name

  let semBody = N.eval semEnv body

  return (Env ((BindTopLevel name):bindings) (S.ctxExtGlobal semBody semTy checkCtx))

-- processDecl env@(Env binds checkEnv) (C.Dont name cbody cty) = do
--   let body = evalState (bind (C.Palette []) binds cbody) 0
--   let ty = bindTy binds cty

--   case S.runCheckM checkEnv $ S.check body ty of
--     Left err -> putStrLn $ "Correctly failed: " ++ name ++ " because " ++ err
--     Right () -> putStrLn $ "Error: " ++ name ++ " should not have typechecked!"

--   return env

emptyEnv :: Env
emptyEnv = Env [] S.ctxEmpty
