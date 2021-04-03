{-# LANGUAGE NamedFieldPuns #-}
module Driver (emptyEnv, processDecl) where

import Debug.Trace

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Data.List (findIndex, find)
import Data.Maybe (fromJust, fromMaybe)

import qualified Concrete as C
import qualified Palette as S
import qualified Syntax as S
import qualified Check as S
import qualified Normalize as N

data Colour where
  NamedCol :: C.Ident -> Colour
  GenSymCol :: Int -> Colour
  deriving (Show, Eq)

data Slice where
  Slice :: [Colour] -> Slice
  SliceOne :: Slice
  SliceTop :: Slice
  SliceSummonedUnit :: C.Ident -> Slice
  deriving (Show, Eq)

providedSlice :: C.Slice -> Slice
providedSlice (C.Slice cs) = Slice $ fmap NamedCol cs
providedSlice (C.SliceOne) = SliceOne
providedSlice (C.SliceSummonedUnit l) = SliceSummonedUnit l
providedSlice (C.SliceTop) = SliceTop

sliceUnion :: Slice -> Slice -> Slice
sliceUnion (Slice l) (Slice r) = Slice $ l ++ r

data BindPalette where
  CommaPal :: BindPalette -> BindPalette -> BindPalette
  OnePal :: BindPalette
  OriginPal :: BindPalette
  TensorPal :: BindPalette -> BindPalette -> BindPalette
  UnitPal :: C.Ident -> BindPalette
  LabelPal :: Colour -> BindPalette -> BindPalette
  deriving (Show)

data BindPat where
  OnePat :: BindPat
  UnitPat :: C.Ident -> BindPat
  VarPat :: C.Ident -> C.Ty -> BindPat
  ZeroVarPat :: C.Ident -> C.Ty -> BindPat
  UndInPat :: BindPat -> BindPat
  PairPat :: BindPat -> BindPat -> BindPat
  ReflPat :: BindPat -> BindPat
  TensorPat :: Colour -> BindPat -> Colour -> BindPat -> BindPat
  LeftUnitorPat :: BindPat -> BindPat
  RightUnitorPat :: BindPat -> BindPat
  ZeroTensorPat :: BindPat -> BindPat -> BindPat
  deriving (Show)

patPalette :: BindPat -> BindPalette
patPalette OnePat = OnePal
patPalette (VarPat _ _) = OnePal
patPalette (UnitPat u) = UnitPal u
patPalette (PairPat p q) = CommaPal (patPalette p) (patPalette q)
patPalette (TensorPat sl p sr q) = TensorPal (LabelPal sl (patPalette p)) (LabelPal sr (patPalette q))
patPalette (UndInPat p) = OnePal

-- The name is optional so we can conveniently write
-- e.g. non-dependent sums and products
data BindEntry = BindTerm {- name -} (Maybe C.Ident) {- colour -} (Maybe Colour)
               | BindTopLevel C.Ident
  deriving (Show)

type SymCounter = Int
data BindState = BindState { bindPalette :: BindPalette, binds :: [BindEntry], bindsSummoned :: Maybe C.Ident }
type BindM = ReaderT BindState (State SymCounter)

bindsLookup :: C.Ident -> BindM Int
bindsLookup name = do
  vars <- asks binds
  case findIndex (\be -> case be of
                           BindTerm (Just n') _ -> name == n'
                           BindTerm Nothing _   -> False
                           BindTopLevel n'    -> name == n') vars of
    Just i -> return i
    Nothing -> error $ "Unbound variable " ++ name

bindsLookupColour :: C.Ident -> BindM (Maybe Colour)
bindsLookupColour name = do
  vars <- asks binds
  case find (\be -> case be of
                      BindTerm (Just n) _ -> name == n
                      BindTerm Nothing _   -> False
                      BindTopLevel _    -> False) vars of
    (Just (BindTerm _ (Just c))) -> return (Just c)
    _ -> return Nothing

guessSlice :: C.Term -> BindM Slice
guessSlice (C.Check a ty) = guessSlice a
guessSlice (C.Var name) = do
  c <- bindsLookupColour name
  case c of
    Just c -> return $ Slice [c]
    Nothing -> return $ Slice []
guessSlice (C.ZeroVar name) = pure $ Slice []
guessSlice (C.Univ i) = pure $ Slice []
guessSlice (C.Lam name t) = guessSlice t
guessSlice (C.App f []) = guessSlice f
guessSlice (C.App f args) = sliceUnion <$> guessSlice (C.App f (init args)) <*> guessSlice (last args)
guessSlice (C.Pair a b) = sliceUnion <$> (guessSlice a) <*> (guessSlice b)
guessSlice (C.Fst p) = guessSlice p
guessSlice (C.Snd p) = guessSlice p
guessSlice (C.UndIn a) = guessSlice a
guessSlice (C.UndOut a) = guessSlice a
guessSlice (C.TensorPair slL a slR b) = sliceUnion <$> (guessSlice a) <*> (guessSlice b)
guessSlice (C.HomLam bodyc yc y body) = guessSlice body
guessSlice (C.HomApp slL f slR a) = sliceUnion <$> (guessSlice f) <*> (guessSlice a)

bindColour :: BindPalette -> Colour -> Maybe S.SlI
bindColour OnePal col = Nothing
bindColour OriginPal col = Nothing
bindColour (UnitPal _) col = Nothing
bindColour (LabelPal i s) col
  | i == col = Just S.IdSl
  | otherwise = bindColour s col
bindColour (CommaPal l r) col =
  case (bindColour l col, bindColour r col) of
    (Nothing, Nothing) -> Nothing
    (Nothing, Just r) -> Just (S.CommaSl S.No (S.Sub r))
    (Just l, Nothing) -> Just (S.CommaSl (S.Sub l) S.No)
    (Just l, Just r) -> Just (S.CommaSl S.No (S.Sub r))
bindColour (TensorPal l r) col =
  case (bindColour l col, bindColour r col) of
    (Nothing, Nothing) -> Nothing
    (Nothing, Just r) -> Just (S.TensorSl S.No (S.Sub r))
    (Just l, Nothing) -> Just (S.TensorSl (S.Sub l) S.No)
    (Just l, Just r) -> Just (S.TensorSl S.No (S.Sub r))

bindSlice :: Slice -> BindM (Maybe S.SlI)
bindSlice (Slice cols) = do
  pal <- asks bindPalette
  return $ foldr S.slackSliceTensor S.OneSl <$> traverse (bindColour pal) cols
bindSlice SliceOne = return $ Just S.OneSl
bindSlice (SliceSummonedUnit l) = return $ Just S.SummonedUnitSl
bindSlice SliceTop = return $ Just S.IdSl

findUnitLabel :: BindPalette -> C.Ident -> Maybe S.UnitI
findUnitLabel OnePal col = Nothing
findUnitLabel OriginPal col = Nothing
findUnitLabel (UnitPal u) col | u == col = Just S.HereUnit -- Id
findUnitLabel (LabelPal i s) col = findUnitLabel s col
findUnitLabel (CommaPal l r) col =
  case (findUnitLabel l col, findUnitLabel r col) of
    (Nothing, Nothing) -> Nothing
    (Nothing, Just r) -> Just (S.RightCommaUnit r)
    (Just l, Nothing) -> Just (S.LeftCommaUnit l)
    (Just l, Just r) -> Just (S.RightCommaUnit r)
findUnitLabel (TensorPal l r) col =
  case (findUnitLabel l col, findUnitLabel r col) of
    (Nothing, Nothing) -> Nothing
    (Nothing, Just r) -> Just (S.TensorUnit S.No (S.Sub r))
    (Just l, Nothing) -> Just (S.TensorUnit (S.Sub l) S.No)
    (Just l, Just r) -> Just (S.TensorUnit S.No (S.Sub r))

bindUnitLabel :: Maybe C.Ident -> BindPalette -> C.Ident -> Maybe S.UnitI
bindUnitLabel (Just summoned) _ u | summoned == u = Just S.SummonedUnit
bindUnitLabel _ pal u = findUnitLabel pal u

bindUnit :: C.Unit -> BindM (Maybe S.UnitI)
bindUnit (C.UnitList us) = do
  pal <- asks bindPalette
  summoned <- asks bindsSummoned
  return $ mconcat <$> traverse (bindUnitLabel summoned pal) us

bindsExtLam :: Maybe C.Ident -> BindState -> BindState
bindsExtLam n state@(BindState { binds }) = state { binds = (BindTerm n Nothing):binds }

bindsExtHom :: Colour -> Colour -> Maybe C.Ident -> BindState -> BindState
bindsExtHom bodyc yc y state@(BindState { binds, bindPalette })
  = state { bindPalette = TensorPal (LabelPal bodyc bindPalette) (LabelPal yc OnePal),
            binds = (BindTerm y (Just yc)):(fmap addColour binds) }
  where addColour (BindTerm y Nothing) = BindTerm y (Just bodyc)
        addColour b = b

bindsExtMany :: [BindEntry] -> BindState -> BindState
bindsExtMany ns state@(BindState { binds }) = state { binds = ns ++ binds }

bindsExtCommaPal :: BindPalette -> BindState -> BindState
bindsExtCommaPal pal state@(BindState { bindPalette })
  = state { bindPalette = CommaPal bindPalette pal }

bindsExtSlice :: Slice -> BindState -> BindState
bindsExtSlice (SliceSummonedUnit l) state@(BindState { bindsSummoned }) = state { bindsSummoned = Just l }
bindsExtSlice _ state = state

genCol :: BindM Colour
genCol = do
  i <- get
  put (i+1)
  return $ GenSymCol i

fillPatCols :: C.Pat -> BindM BindPat
fillPatCols (C.OnePat) = pure OnePat
fillPatCols (C.UnitPat u) = pure (UnitPat u)
fillPatCols (C.VarPat x ty) = pure (VarPat x ty)
fillPatCols (C.ZeroVarPat x ty) = pure (ZeroVarPat x ty)
fillPatCols (C.UndInPat p) = UndInPat <$> fillPatCols p
fillPatCols (C.PairPat p q) = PairPat <$> fillPatCols p <*> fillPatCols q
fillPatCols (C.ReflPat p) = ReflPat <$> fillPatCols p
fillPatCols (C.TensorPat l p r q) = do
  l' <- case l of
           Just c -> pure (NamedCol c)
           Nothing -> genCol
  r' <- case r of
           Just c -> pure (NamedCol c)
           Nothing -> genCol
  TensorPat <$> pure l' <*> fillPatCols p <*> pure r' <*> fillPatCols q
fillPatCols (C.LeftUnitorPat p) = LeftUnitorPat <$> fillPatCols p
fillPatCols (C.RightUnitorPat p) = RightUnitorPat <$> fillPatCols p

patVars :: BindPat -> [BindEntry]
patVars p = go Nothing p
  where
  go c OnePat = []
  go c (UnitPat _) = []
  go c (VarPat x _) = [BindTerm (Just x) c]
  go c (ZeroVarPat x _) = [BindTerm (Just x) Nothing]
  go c (PairPat p q) = go c q ++ go c p
  go c (TensorPat l p r q) = go (Just r) q ++ go (Just l) p
  go c (LeftUnitorPat p) = go c p
  go c (RightUnitorPat p) = go c p
  go c (UndInPat p) = go Nothing p

bindPat :: BindPat -> BindM S.Pat
bindPat (OnePat) = pure S.OnePat
bindPat (UnitPat _) = pure S.UnitPat
bindPat (VarPat _ ty) = S.VarPat <$> bind ty
bindPat (ZeroVarPat _ ty) = S.ZeroVarPat <$> bind ty
bindPat (UndInPat p) = S.UndInPat <$> bindPat p
bindPat (PairPat p q) = do
  p' <- bindPat p
  q' <- local (bindsExtMany (patVars p)) $ bindPat q
  return $ S.PairPat p' q'
bindPat (ReflPat p) = S.ReflPat <$> bindPat p
bindPat (TensorPat _ p _ q) = do
  p' <- bindPat p
  q' <- local (bindsExtMany (patVars p)) $ bindPat q

  return $ S.TensorPat p' q'
bindPat (LeftUnitorPat p) = S.LeftUnitorPat <$> bindPat p
bindPat (RightUnitorPat p) = S.RightUnitorPat <$> bindPat p
bindPat (ZeroTensorPat p q) = do
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
bind (C.Refl a) = S.Refl <$> bind a
bind (C.UndIn a) = S.UndIn <$> (bind a)
bind (C.UndOut a) = S.UndOut <$> (bind a)
bind (C.Unit) = pure S.Unit
bind (C.Pi [] b) = bind b
bind (C.Pi (C.TeleCell n ty : cells) b) = S.Pi <$> (bind ty) <*> (local (bindsExtLam n) $ bind (C.Pi cells b))
bind (C.Sg [] b) = bind b
bind (C.Sg (C.TeleCell n ty : cells) b) = S.Sg <$> (bind ty) <*> (local (bindsExtLam n) $ bind (C.Sg cells b))
bind (C.Id aty a b) = S.Id <$> bind aty <*> bind a <*> bind b
bind (C.Und a) = S.Und <$> bind a
bind (C.Tensor n a b) = S.Tensor <$> bind a <*> local (bindsExtLam n ) (bind b)
bind (C.Hom bodyc yc y a b) = do
  bodyc' <- case bodyc of
           Just c -> pure (NamedCol c)
           Nothing -> genCol
  yc' <- case yc of
           Just c -> pure (NamedCol c)
           Nothing -> genCol
  S.Hom <$> bind a <*> local (bindsExtHom bodyc' yc' y) (bind b)

bind t@(C.TensorPair sl a sr b) = do
  sl' <- case sl of
    Nothing -> guessSlice a
    (Just C.SliceOmitted) -> guessSlice a
    (Just sl) -> pure (providedSlice sl)
  sr' <- case sr of
    Nothing -> guessSlice b
    (Just C.SliceOmitted) -> guessSlice b
    (Just sr) -> pure (providedSlice sr)
  boundsl <- bindSlice sl'
  bounda <- local (bindsExtSlice sl') $ bind a

  boundsr <- bindSlice sr'
  boundb <- local (bindsExtSlice sr') $ bind b

  return $ S.TensorPair (fromJust $ boundsl) bounda (fromJust $ boundsr) boundb

bind (C.HomLam bodyc yc y body) = do
  bodyc' <- case bodyc of
           Just c -> pure (NamedCol c)
           Nothing -> genCol
  yc' <- case yc of
           Just c -> pure (NamedCol c)
           Nothing -> genCol
  boundbody <- local (bindsExtHom bodyc' yc' (Just y)) $ bind body
  return $ S.HomLam boundbody

bind (C.HomApp sl f sr a) = do
  sl' <- case sl of
    Nothing -> guessSlice f
    (Just sl) -> pure (providedSlice sl)
  sr' <- case sr of
    Nothing -> guessSlice a
    (Just sr) -> pure (providedSlice sr)
  boundsl <- bindSlice sl'
  boundf <- local (bindsExtSlice sl') $ bind f

  boundsr <- bindSlice sr'
  bounda <- local (bindsExtSlice sr') $ bind a

  return $ S.HomApp
    (fromJust $ boundsl)
    boundf
    (fromJust $ boundsr)
    bounda

bind (C.UnitIn u) = do
  boundu <- bindUnit u
  return $ S.UnitIn (fromJust $ boundu) -- FIXME: error handling

bind (C.Match t z mot patterm br) = do
  boundt <- bind t

  let pat = fromJust $ C.comprehendPat patterm
  pat' <- fillPatCols pat

  boundmot <- local (bindsExtLam z) $ bind mot

  let patpal = patPalette pat'
  boundpat <- local (bindsExtCommaPal patpal) $ bindPat pat'

  boundbr <- local (bindsExtCommaPal patpal . bindsExtMany (patVars pat')) $ bind br

  return $ S.Match boundt boundmot boundpat boundbr

data Env = Env { envBindings :: [BindEntry], envCheckCtx :: S.SemCtx }

processDecl :: Env -> C.Decl -> IO Env
processDecl env@(Env bindings checkCtx) (C.Def name cbody cty) = do
  let ty   = evalState (runReaderT (bind cty) (BindState OriginPal bindings Nothing)) 0
  let body = evalState (runReaderT (bind cbody) (BindState OriginPal bindings Nothing)) 0

  case S.runCheckM checkCtx $ S.checkTy S.IdSl ty of
    Left err -> putStrLn $ "Error in type of " ++ name ++ ": " ++ err
    Right () -> return ()

  let semEnv = S.ctxToEnv checkCtx
  let semTy = N.eval semEnv ty

  case S.runCheckM checkCtx $ S.check S.IdSl body semTy of
    Left err -> putStrLn $ "Error in: " ++ name ++ ": " ++ err
    Right () -> putStrLn $ "Checked: " ++ name

  let semBody = N.eval semEnv body

  return (Env ((BindTopLevel name):bindings) (S.ctxExtGlobal semBody semTy checkCtx))

processDecl env@(Env bindings checkCtx) (C.Dont name cbody cty) = do
  let ty   = evalState (runReaderT (bind cty) (BindState OriginPal bindings Nothing)) 0
  let body = evalState (runReaderT (bind cbody) (BindState OriginPal bindings Nothing)) 0

  let semEnv = S.ctxToEnv checkCtx
  let semTy = N.eval semEnv ty

  case S.runCheckM checkCtx $ S.check S.IdSl body semTy of
    Left err -> putStrLn $ "Correctly failed: " ++ name ++ " because " ++ err
    Right () -> putStrLn $ "Error: " ++ name ++ " should not have typechecked!"

  return env

processDecl env@(Env bindings checkCtx) (C.Postulate name cty) = do
  let ty   = evalState (runReaderT (bind cty) (BindState OriginPal bindings Nothing)) 0

  let semEnv = S.ctxToEnv checkCtx
  let semTy = N.eval semEnv ty

  putStrLn $ "Postulated: " ++ name

  let semTy = N.eval semEnv ty
      semVar = S.VNeutral semTy (S.NVar (length bindings))

  return (Env ((BindTopLevel name):bindings) (S.ctxExtGlobal semVar semTy checkCtx))


emptyEnv :: Env
emptyEnv = Env [] S.ctxEmpty
