{-# LANGUAGE NamedFieldPuns #-}
module Simple.Driver where

import Debug.Trace

import Data.List (findIndex, find)
import Data.Maybe (fromJust, fromMaybe)

import qualified Simple.Concrete as C
import qualified Simple.Syntax as S
import Palette

data BindEntry = BindTerm C.Ident C.Colour
               | BindTopLevel C.Ident
  deriving (Show)

data Bindings = Bindings { bindTypes :: [C.Ident], bindVars :: [BindEntry] }

bindsLookup :: Bindings -> C.Ident -> Int
bindsLookup binds name = case findIndex (\be -> case be of
                                            BindTerm n' _ -> name == n'
                                            BindTopLevel n' -> name == n') (bindVars binds) of
  Just i -> i
  Nothing -> error $ "Unbound variable " ++ name

bindsLookupColour :: Bindings -> C.Ident -> C.Colour
bindsLookupColour binds name = case find (\be -> case be of
                                            BindTerm n' _ -> name == n'
                                            BindTopLevel n' -> name == n') (bindVars binds) of
                                 
  Just (BindTerm _ c) -> c 
  Just (BindTopLevel _) -> C.TopColour
  Nothing -> error $ "Unbound variable " ++ name

bindsLookupTy :: Bindings -> C.Ident -> Int
bindsLookupTy binds name = case findIndex (\(n') -> name == n') (bindTypes binds) of
  Just i -> i
  Nothing -> error $ "Unknown type " ++ name

bindsExt :: Bindings -> C.Ident -> Bindings
bindsExt binds@(Bindings { bindVars }) name = binds { bindVars = (BindTerm name C.TopColour):bindVars }

entryExtHom :: C.Ident -> BindEntry -> BindEntry
entryExtHom bodyc (BindTerm n c) = BindTerm n (C.colExtHom bodyc c)
entryExtHom bodyc (BindTopLevel n) = BindTopLevel n

bindsExtHom :: Bindings -> C.Ident -> C.Ident -> C.Ident -> Bindings
bindsExtHom binds@(Bindings { bindVars }) bodyc yc y 
  = binds { bindVars = (BindTerm y (C.NamedColour yc)):(fmap (entryExtHom bodyc) bindVars) }

-- bindsExtTele :: Binds -> 
bindsExtTele (Bindings tys vars) omega = Bindings tys (omega ++ vars)

guessSliceTele :: C.Palette -> Bindings -> C.TeleSubst -> C.Slice
guessSliceTele pal env (C.TeleSubst _ ts) = foldl C.sliceUnion (C.Slice []) $ fmap (guessSlice pal env) ts

-- TODO: this doesn't handle shadowed variables at all
guessSlice :: C.Palette -> Bindings -> C.Term -> C.Slice
guessSlice pal env (C.Check a ty) = guessSlice pal env a
guessSlice pal env (C.Var name) = C.Slice [bindsLookupColour env name]
guessSlice pal env (C.ZeroVar name) = C.Slice []
guessSlice pal env (C.Lam name t) = guessSlice pal env t
guessSlice pal env (C.App f []) = guessSlice pal env f
guessSlice pal env (C.App f args) = guessSlice pal env (C.App f (init args)) `C.sliceUnion` guessSlice pal env (last args)
guessSlice pal env (C.Pair a b) = (guessSlice pal env a) `C.sliceUnion` (guessSlice pal env b)
guessSlice pal env (C.Fst p) = guessSlice pal env p
guessSlice pal env (C.Snd p) = guessSlice pal env p
guessSlice pal env (C.UndIn a) = guessSlice pal env a
guessSlice pal env (C.UndOut a) = guessSlice pal env a
guessSlice pal env (C.TensorPair slL a slR b) = (guessSlice pal env a) `C.sliceUnion` (guessSlice pal env b)
guessSlice pal env (C.TensorElim psi omega theta z mot (x, xc) (y, yc) c) = (guessSliceTele pal env theta) `C.sliceUnion` (guessSlice pal env c)
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

bindTeleSubst :: C.Palette -> Bindings -> C.TeleSubst -> S.TeleSubst
bindTeleSubst pal env (C.TeleSubst kappa as) = S.TeleSubst (bindPalSubst pal env kappa) (fmap (bind pal env) as)

-- Silly...
bindTy :: Bindings -> C.Ty -> S.Ty
bindTy env (C.BaseTy n) = S.BaseTy $ bindsLookupTy env n
bindTy env (C.Pi a b) = S.Pi (bindTy env a) (bindTy env b)
bindTy env (C.Sg a b) = S.Sg (bindTy env a) (bindTy env b)
bindTy env (C.Und a) = S.Und (bindTy env a) 
bindTy env (C.Tensor a b) = S.Tensor (bindTy env a) (bindTy env b)
bindTy env (C.Hom a b) = S.Hom (bindTy env a) (bindTy env b)

bind :: C.Palette -> Bindings -> C.Term -> S.Term
bind pal env (C.Check a ty) = S.Check (bind pal env a) (bindTy env ty)
bind pal env (C.Var name) = S.Var (bindsLookup env name)
bind pal env (C.ZeroVar name) = S.ZeroVar (bindsLookup env name)
bind pal env (C.Lam name t) = S.Lam (bind pal (bindsExt env name) t)
bind pal env (C.App f []) = bind pal env f
bind pal env (C.App f args) = S.App (bind pal env (C.App f (init args))) (bind pal env (last args)) -- yes this could be done better 
bind pal env (C.Pair a b) = S.Pair (bind pal env a) (bind pal env b)
bind pal env (C.Fst p) = S.Fst (bind pal env p)
bind pal env (C.Snd p) = S.Snd (bind pal env p)
bind pal env (C.UndIn a) = S.UndIn (bind pal env a)
bind pal env (C.UndOut a) = S.UndOut (bind pal env a)

bind pal env t@(C.TensorPair slL a slR b) 
  = let slL' = fromMaybe (guessSlice pal env a) slL
        slR' = fromMaybe (guessSlice pal env b) slR in
    S.TensorPair 
      (fromJust $ bindSlice pal slL') 
      (bind (C.palRestrict pal slL') env a) 
      (fromJust $ bindSlice pal slR') 
      (bind (C.palRestrict pal slR') env b)

bind pal env (C.TensorElim psi omega theta z mot (x, xc) (y, yc) c)
  = S.TensorElim 
      (bindPal psi)
      (fmap (fromJust . bindColour psi . snd) omega) 
      (bindTeleSubst pal env theta) 
      zIdx
      (bindTy env mot) 
      (bind (C.Palette $ cpsis ++ cpals) (bindsExtTele env omega') c)
      -- (bind (C.Palette $ cpsis ++ cpals) undefined c)
  where zIdx = (fromJust $ findIndex ((== z) . fst) omega)
        zCol = snd $ fromJust $ find ((==z) . fst) omega
        (C.Palette cpsis) = C.palAddTensor psi zCol (xc, yc)
        (C.Palette cpals) = pal
        (before, _:after) = splitAt zIdx omega
        omega' = fmap (uncurry BindTerm) before
                 ++ [(BindTerm x (C.NamedColour xc)), (BindTerm y (C.NamedColour yc))] 
                 ++ fmap (uncurry BindTerm) after

bind pal env (C.TensorElimSimple s mot (x, xc) (y, yc) c)
  = S.TensorElim 
    (Palette [])
    [TopColour]
    (S.TeleSubst (PaletteSubst []) [bind pal env s])
    0
    (bindTy env mot)
    (bind (C.Palette $ (C.palLoneTensor (xc, yc)):cpals) (bindsExtTele env [(BindTerm x (C.NamedColour xc)), (BindTerm y (C.NamedColour yc))]) c)
  where (C.Palette cpals) = pal

bind pal env (C.HomLam bodyc yc y body)
  = S.HomLam (bind (C.palExtHom pal bodyc yc) (bindsExtHom env bodyc yc y) body)

bind pal env (C.HomApp slL f slR a)
  = let slL' = fromMaybe (guessSlice pal env f) slL
        slR' = fromMaybe (guessSlice pal env a) slR in
    S.HomApp 
    (fromJust $ bindSlice pal slL') 
    (bind (C.palRestrict pal slL') env f) 
    (fromJust $ bindSlice pal slR') 
    (bind (C.palRestrict pal slR') env a)

data Env = Env { envBindings :: Bindings, envCheckEnv :: S.Env }

processDecl :: Env -> C.Decl -> IO Env
processDecl env@(Env binds@(Bindings postTypes bindings) checkEnv) (C.Def name cbody cty) = do
  let body = bind (C.Palette []) binds cbody
  let ty = bindTy binds cty
  
  case S.runCheckM checkEnv $ S.check body ty of 
    Left err -> putStrLn $ "Error: " ++ err
    Right () -> putStrLn $ "Checked: " ++ name
  
  return (Env (Bindings postTypes ((BindTopLevel name):bindings)) (S.envExtendTop ty checkEnv))

processDecl env@(Env binds checkEnv) (C.Dont name cbody cty) = do
  let body = bind (C.Palette []) binds cbody
  let ty = bindTy binds cty
  
  case S.runCheckM checkEnv $ S.check body ty of 
    Left err -> putStrLn $ "Correctly failed: " ++ name ++ " because " ++ err
    Right () -> putStrLn $ "Error: " ++ name ++ " should not have typechecked!"
  
  return env 

processDecl env@(Env binds@(Bindings postTypes bindings) checkEnv) (C.PostType name) = do  
  putStrLn $ "Postulated type: " ++ name

  return (Env (Bindings (name:postTypes) bindings) checkEnv)

emptyEnv :: Env
emptyEnv = Env (Bindings [] []) (S.emptyEnv)
