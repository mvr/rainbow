{-# LANGUAGE NamedFieldPuns #-}
module Driver where

import Debug.Trace

import Control.Monad.State
import Data.List (findIndex, find)
import Data.Maybe (fromJust, fromMaybe)

import qualified Concrete as C
import qualified Syntax as S
import qualified Check as S
import qualified Normalize as N
import Palette

data BindEntry = BindTerm (Maybe C.Ident) C.Colour
               | BindTopLevel C.Ident
  deriving (Show)

data Bindings = Bindings { bindVars :: [BindEntry] }

bindsLookup :: Bindings -> C.Ident -> Int
bindsLookup binds name = case findIndex (\be -> case be of
                                            BindTerm (Just n') _ -> name == n'
                                            BindTerm Nothing _ -> False
                                            BindTopLevel n' -> name == n') (bindVars binds) of
  Just i -> i
  Nothing -> error $ "Unbound variable " ++ name

bindsLookupColour :: Bindings -> C.Ident -> C.Colour
bindsLookupColour binds name = case find (\be -> case be of
                                            BindTerm (Just n') _ -> name == n'
                                            BindTerm Nothing _ -> False
                                            BindTopLevel n' -> name == n') (bindVars binds) of
                                 
  Just (BindTerm _ c) -> c 
  Just (BindTopLevel _) -> C.TopColour
  Nothing -> error $ "Unbound variable " ++ name

bindsExt :: Bindings -> Maybe C.Ident -> Bindings
bindsExt binds@(Bindings { bindVars }) name = binds { bindVars = (BindTerm name C.TopColour):bindVars }

entryExtHom :: C.Ident -> BindEntry -> BindEntry
entryExtHom bodyc (BindTerm n c) = BindTerm n (C.colExtHom bodyc c)
entryExtHom bodyc (BindTopLevel n) = BindTopLevel n

bindsExtHom :: Bindings -> C.Ident -> C.Ident -> C.Ident -> Bindings
bindsExtHom binds@(Bindings { bindVars }) bodyc yc y 
  = binds { bindVars = (BindTerm (Just y) (C.NamedColour yc)):(fmap (entryExtHom bodyc) bindVars) }

-- bindsExtTele :: Binds -> 
bindsExtTele (Bindings vars) omega = Bindings (reverse omega ++ vars)

guessSliceTele :: C.Palette -> Bindings -> C.TeleSubst -> C.Slice
guessSliceTele pal env (C.TeleSubst _ ts) = foldl C.sliceUnion (C.Slice []) $ fmap (guessSlice pal env) ts

-- TODO: this doesn't handle shadowed variables at all
guessSlice :: C.Palette -> Bindings -> C.Term -> C.Slice
guessSlice pal env (C.Check a ty) = guessSlice pal env a
guessSlice pal env (C.Var name) = C.Slice [bindsLookupColour env name]
guessSlice pal env (C.ZeroVar name) = C.Slice []
guessSlice pal env (C.Univ i) = C.Slice []
guessSlice pal env (C.Lam name t) = guessSlice pal env t
guessSlice pal env (C.App f []) = guessSlice pal env f
guessSlice pal env (C.App f args) = guessSlice pal env (C.App f (init args)) `C.sliceUnion` guessSlice pal env (last args)
guessSlice pal env (C.Pair a b) = (guessSlice pal env a) `C.sliceUnion` (guessSlice pal env b)
guessSlice pal env (C.Fst p) = guessSlice pal env p
guessSlice pal env (C.Snd p) = guessSlice pal env p
guessSlice pal env (C.UndIn a) = guessSlice pal env a
guessSlice pal env (C.UndOut a) = guessSlice pal env a
guessSlice pal env (C.TensorPair slL a slR b) = (guessSlice pal env a) `C.sliceUnion` (guessSlice pal env b)
guessSlice pal env (C.TensorElim s z mot (x, xc) (y, yc) br) = (guessSlice pal env s) `C.sliceUnion` (guessSlice pal env mot) `C.sliceUnion` (guessSlice pal env br)
guessSlice pal env (C.TensorElimFrob psi omega theta z mot (x, xc) (y, yc) c) = (guessSliceTele pal env theta) `C.sliceUnion` (guessSlice pal env c)
guessSlice pal env (C.HomLam bodyc yc y body) = guessSlice pal env body
guessSlice pal env (C.HomApp slL f slR a) = (guessSlice pal env f) `C.sliceUnion` (guessSlice pal env a)

bindPalPiece :: C.PalettePiece -> PalettePiece
bindPalPiece (C.TensorPal _ pL _ pR) = TensorPal (bindPal pL) (bindPal pR)

bindPal :: C.Palette -> Palette
bindPal (C.Palette ps) = Palette $ fmap bindPalPiece ps

bindColour :: C.Palette -> C.Colour -> Maybe ColourIndex
bindColour pal (C.TopColour) = Just TopColour
bindColour (C.Palette []) (C.NamedColour n) = error $ "Unknown colour " ++ n
bindColour (C.Palette ((C.TensorPal nL pL nR pR):ps)) (C.NamedColour n) 
  | nL == Just n = Just $ LeftSub 0 TopColour
  | nR == Just n = Just $ RightSub 0 TopColour
  | Just c <- bindColour pL (C.NamedColour n) = Just $ LeftSub 0 c
  | Just c <- bindColour pR (C.NamedColour n) = Just $ RightSub 0 c
  | Just (LeftSub i c) <- bindColour (C.Palette ps) (C.NamedColour n) = Just $ LeftSub (i+1) c
  | Just (RightSub i c) <- bindColour (C.Palette ps) (C.NamedColour n) = Just $ RightSub (i+1) c
  | otherwise = Nothing

bindSlice :: C.Palette -> C.Slice -> Maybe SliceIndex
bindSlice pal (C.Slice cols) = mconcat <$> fmap colourToSlice <$> traverse (bindColour pal) cols

bindPalSubstPiece :: C.Palette -> Bindings -> C.SubstPiece -> SubstPiece
bindPalSubstPiece pal env (C.TensorPalSub slL _ psL slR _ psR) 
  = TensorPalSub (fromJust $ bindSlice pal slL) (bindPalSubst pal env psL) (fromJust $ bindSlice pal slR) (bindPalSubst pal env psR)

bindPalSubst :: C.Palette -> Bindings -> C.PaletteSubst -> PaletteSubst
bindPalSubst pal env (C.PaletteSubst ps) = PaletteSubst $ fmap (bindPalSubstPiece pal env) ps

bindTele :: C.Palette -> Bindings -> C.Palette -> [(C.Ident, C.Colour, C.Ty)] -> State SymCounter [(ColourIndex, S.Ty)]
bindTele pal env psi [] = return []
bindTele pal env psi ((n,c,ty):cs) = do
  boundty <- bind (C.palRestrict (C.palExtend psi pal) (C.Slice [c])) env ty
  let boundc = fromJust $ bindColour psi c

  rest <- bindTele pal (bindsExt env (Just n)) psi cs
  
  return $ (boundc, boundty):rest

bindTeleSubst :: C.Palette -> Bindings -> C.TeleSubst -> State SymCounter S.TeleSubst
bindTeleSubst pal env (C.TeleSubst kappa as) = do 
  ts <- mapM (bind pal env) as 
  return $ S.TeleSubst (bindPalSubst pal env kappa) ts

type SymCounter = Int

genColLike :: C.Ident -> State SymCounter C.Ident
genColLike n = do
  i <- get
  put (i+1)
  return $ "?" ++ n ++ show i

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
  let slL' = fromMaybe (guessSlice pal env a) slL
      slR' = fromMaybe (guessSlice pal env b) slR 
  bounda <- bind (C.palRestrict pal slL') env a
  boundb <- bind (C.palRestrict pal slR') env b
  
  return $ S.TensorPair (fromJust $ bindSlice pal slL') bounda (fromJust $ bindSlice pal slR') boundb

bind pal env (C.TensorElimFrob psi omega theta z mot (x, xc) (y, yc) br) = do
  xc' <- case xc of 
           Just xc -> pure xc
           Nothing -> genColLike x
  yc' <- case yc of 
           Just yc -> pure yc
           Nothing -> genColLike y

  let zIdx = fromJust $ findIndex (\(n,_,_) -> n == z) omega
      zCol = (\(_,c,_) -> c) $ fromJust $ find (\(n,_,_) -> n == z) omega
      (before, _:after) = splitAt zIdx omega

  let motomega = fmap (\(n, c, ty) -> BindTerm (Just n) c) omega

  boundmot <- bind (C.palExtend psi pal) (bindsExtTele env motomega) mot
  
  let bromega = fmap (\(n, c, ty) -> BindTerm (Just n) c) before
                ++ [(BindTerm (Just x) (C.NamedColour xc')), (BindTerm (Just y) (C.NamedColour yc'))] 
                ++ fmap (\(n, c, ty) -> BindTerm (Just n) c) after

  boundtheta <- bindTeleSubst pal env theta
  boundbr <- bind (C.palExtend (C.palAddTensor psi zCol (xc', yc')) pal) (bindsExtTele env bromega) br

  boundomega <- bindTele pal env psi omega

  return $ S.TensorElimFrob 
      (bindPal psi)
      boundomega
      boundtheta
      zIdx
      boundmot
      boundbr

bind pal@(C.Palette cpals) env (C.TensorElim s z mot (x, xc) (y, yc) c) = do
  xc' <- case xc of 
           Just xc -> pure xc
           Nothing -> genColLike x
  yc' <- case yc of 
           Just yc -> pure yc
           Nothing -> genColLike y

  bounds <- bind pal env s
  boundbr <- bind (C.Palette $ (C.palLoneTensor (xc', yc')):cpals) (bindsExtTele env [(BindTerm (Just x) (C.NamedColour xc')), (BindTerm (Just y) (C.NamedColour yc'))]) c
  
  boundmot <- bind pal (bindsExt env z) mot 

  return $ S.TensorElim bounds boundmot boundbr
  
bind pal env (C.HomLam bodyc yc y body) = do
  bodyc' <- case bodyc of 
           Just bodyc -> pure bodyc
           Nothing -> genColLike "t"
  yc' <- case yc of 
           Just yc -> pure yc
           Nothing -> genColLike y

  boundbody <- bind (C.palExtHom pal (Just bodyc') (Just yc')) (bindsExtHom env bodyc' yc' y) body
  return $ S.HomLam boundbody

bind pal env (C.HomApp slL f slR a) = do
  let slL' = fromMaybe (guessSlice pal env f) slL
      slR' = fromMaybe (guessSlice pal env a) slR 

  boundf <- bind (C.palRestrict pal slL') env f
  bounda <- bind (C.palRestrict pal slR') env a

  return $ S.HomApp 
    (fromJust $ bindSlice pal slL') 
    boundf
    (fromJust $ bindSlice pal slR') 
    bounda

data Env = Env { envBindings :: Bindings, envCheckCtx :: S.SemCtx }

processDecl :: Env -> C.Decl -> IO Env
processDecl env@(Env binds@(Bindings bindings) checkCtx) (C.Def name cbody cty) = do
  let body = evalState (bind (C.Palette []) binds cbody) 0
  let ty = evalState (bind (C.Palette []) binds cty) 0

  
  case S.runCheckM checkCtx $ S.checkTy ty of   
    Left err -> putStrLn $ "Error in type of " ++ name ++ ": " ++ err
    Right () -> return ()

  let semEnv = S.ctxToEnv checkCtx
  let semTy = N.eval semEnv ty

  case S.runCheckM checkCtx $ S.check body semTy of 
    Left err -> putStrLn $ "Error in: " ++ name ++ ": " ++ err
    Right () -> putStrLn $ "Checked: " ++ name
  
  let semBody = N.eval semEnv body

  return (Env (Bindings ((BindTopLevel name):bindings)) (S.ctxExtTop semBody semTy checkCtx))

-- processDecl env@(Env binds checkEnv) (C.Dont name cbody cty) = do
--   let body = evalState (bind (C.Palette []) binds cbody) 0
--   let ty = bindTy binds cty
  
--   case S.runCheckM checkEnv $ S.check body ty of 
--     Left err -> putStrLn $ "Correctly failed: " ++ name ++ " because " ++ err
--     Right () -> putStrLn $ "Error: " ++ name ++ " should not have typechecked!"
  
--   return env 

emptyEnv :: Env
emptyEnv = Env (Bindings []) (S.ctxEmpty)
