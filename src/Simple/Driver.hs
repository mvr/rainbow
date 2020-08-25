{-# LANGUAGE NamedFieldPuns #-}
module Simple.Driver where

import Debug.Trace

import Data.List (findIndex, find)
import Data.Maybe (fromJust)

import qualified Simple.Concrete as C
import qualified Simple.Syntax as S
import Palette

data Bindings = Bindings { bindTypes :: [C.Ident], bindVars :: [C.Ident] }

bindsLookup :: Bindings -> C.Ident -> Int
bindsLookup binds name = case findIndex (\(n') -> name == n') (bindVars binds) of
  Just i -> i
  Nothing -> error $ "Unbound variable " ++ name

bindsLookupTy :: Bindings -> C.Ident -> Int
bindsLookupTy binds name = case findIndex (\(n') -> name == n') (bindTypes binds) of
  Just i -> i
  Nothing -> error $ "Unknown type " ++ name

bindsExt :: Bindings -> C.Ident -> Bindings
bindsExt binds@(Bindings { bindVars }) name = binds { bindVars = name:bindVars }

-- bindsExtTele :: Binds -> 
bindsExtTele (Bindings tys vars) omega = Bindings tys (omega ++ vars)

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
bindSlice pal (C.Slice cols) = mconcat <$> fmap colourToSlice <$> traverse (bindColour pal) (fmap C.NamedColour cols) -- TODO

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
  = -- traceShow (pal, t) $ 
  S.TensorPair 
      (fromJust $ bindSlice pal slL) 
      (bind (C.palRestrict pal slL) env a) 
      (fromJust $ bindSlice pal slR) 
      (bind (C.palRestrict pal slR) env b)

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
        (before, _:after) = splitAt zIdx (fmap fst omega)
        omega' = before ++ [x, y] ++ after

  -- HomLam :: Ident -> Term -> Term
  -- HomApp :: Term -> Term -> Term

data Env = Env { envBindings :: Bindings, envCheckEnv :: S.Env }

processDecl :: Env -> C.Decl -> IO Env
processDecl env@(Env binds@(Bindings postTypes bindings) checkEnv) (C.Def name cbody cty) = do
  let body = bind (C.Palette []) binds cbody
  let ty = bindTy binds cty
  
  case S.runCheckM checkEnv $ S.check body ty of 
    Left err -> putStrLn $ "Error: " ++ err
    Right () -> putStrLn $ "Checked: " ++ name
  
  return (Env (Bindings postTypes (name:bindings)) (S.envExtendTop ty checkEnv))

processDecl env@(Env binds@(Bindings postTypes bindings) checkEnv) (C.PostType name) = do  
  putStrLn $ "Postulated type: " ++ name

  return (Env (Bindings (name:postTypes) bindings) checkEnv)

emptyEnv :: Env
emptyEnv = Env (Bindings [] []) (S.emptyEnv)
