{-# LANGUAGE GADTs #-}
module Simple.Concrete where

import Debug.Trace

import Data.Maybe (mapMaybe)

type Ident = String

data PalettePiece where
  TensorPal :: Maybe Ident -> Palette -> Maybe Ident -> Palette -> PalettePiece
  -- UnitPal :: PalettePiece
  deriving (Show)

data Palette = Palette [PalettePiece]
  deriving (Show)

emptyPal :: Palette
emptyPal = Palette []

data Colour where
  NamedColour :: Ident -> Colour
  ZeroColour :: Colour
  TopColour :: Colour
  deriving (Show)

palLoneTensor :: (Ident, Ident) -> PalettePiece
palLoneTensor (r, b) = TensorPal (Just r) emptyPal (Just b) emptyPal

palAddTensor :: Palette -> Colour -> (Ident, Ident) -> Palette
palAddTensor (Palette ps) TopColour (r, b) = Palette $ (palLoneTensor (r, b)):ps
palAddTensor (Palette []) c (r, b) = error $ "Colour " ++ show c ++ " not found"
palAddTensor (Palette ((TensorPal cL pL@(Palette pLs) cR pR@(Palette pRs)):ps)) (NamedColour c) (r, b) 
  | cL == Just c = Palette ((TensorPal cL (Palette $ (palLoneTensor (r, b)):pLs) cR (Palette pRs)):ps)
  | cR == Just c = Palette ((TensorPal cL (Palette pLs) cR (Palette $ (palLoneTensor (r, b)):pRs)):ps)
  | otherwise = let Palette ps' = palAddTensor (Palette ps) (NamedColour c) (r, b) in
                  Palette $ (TensorPal cL (palAddTensor pL (NamedColour c) (r, b)) cL (palAddTensor pR (NamedColour c) (r, b))) : ps'
-- TODO: This could cause confusing errors if the colour name appears more than once. 

palExtHom :: Palette -> Ident -> Ident -> Palette
palExtHom pal bodyc yc = Palette [TensorPal (Just bodyc) pal (Just yc) emptyPal]

data Slice where 
  Slice :: {- Colour names -} [Ident] -> Slice
  deriving (Show, Eq)

-- palRestrictHalf :: Slice -> Maybe Ident -> Palette -> Maybe (Maybe Ident, Palette)
-- palRestrictHalf (Slice ns) (Just n) pal 
--   | n `elem` ns = Just (Just n, pal)
--   | otherwise = case palRestrict pal (Slice ns) of
--       Just pal' -> Just (Nothing, pal')
--       Nothing -> Nothing
-- palRestrictHalf sl Nothing pal = 
--   case palRestrict pal sl of
--     Just pal' -> Just (Nothing, pal')
--     Nothing -> Nothing

-- palPieceRestrict :: PalettePiece -> Slice -> Maybe Palette
-- palPieceRestrict p@(TensorPal cL pL cR pR) sl
--   = let rpL = palRestrictHalf sl cL pL 
--         rpR = palRestrictHalf sl cR pR in
--     case (rpL, rpR) of
--       (Just (cL', pL'), Just (cR', pR')) -> Just $ Palette [TensorPal cL' pL' cR' pR']
--       (Nothing, Just (_, pR')) -> Just pR'
--       (Just (_, pL'), Nothing) -> Just pL'
--       (Nothing, Nothing) -> Nothing

-- palRestrict :: Palette -> Slice -> Maybe Palette
-- -- palRestrict pal sl | traceShow (pal, sl) False = undefined
-- palRestrict (Palette []) sl = Just (Palette [])
-- palRestrict (Palette ps) sl = foldl combine Nothing (fmap (flip palPieceRestrict sl) ps) 
--   where combine Nothing ps = ps
--         combine ps Nothing = ps
--         combine (Just (Palette ps)) (Just (Palette ps')) = Just (Palette $ ps ++ ps')

palRestrictHalf :: Slice -> Maybe Ident -> Palette -> Maybe (Maybe Ident, Palette)
palRestrictHalf sl@(Slice ns) (Just n) pal 
  | n `elem` ns = Just (Just n, pal)
  | otherwise = palRestrictWName pal sl 
palRestrictHalf sl Nothing pal = palRestrictWName pal sl 

palPieceRestrict :: PalettePiece -> Slice -> Maybe (Maybe Ident, Palette)
palPieceRestrict p@(TensorPal cL pL cR pR) sl
  = let rpL = palRestrictHalf sl cL pL 
        rpR = palRestrictHalf sl cR pR in
    case (rpL, rpR) of
      (Just (cL', pL'), Just (cR', pR')) -> Just (Nothing, Palette [TensorPal cL' pL' cR' pR'])
      (Nothing, Just (cR', pR')) -> Just (cR', pR')
      (Just (cL', pL'), Nothing) -> Just (cL', pL')
      (Nothing, Nothing) -> Nothing

palRestrictWName :: Palette -> Slice -> Maybe (Maybe Ident, Palette)
-- palRestrict pal sl | traceShow (pal, sl) False = undefined
-- palRestrictWName (Palette []) sl = Just (Nothing, Palette [])
palRestrictWName pal@(Palette ps) sl = foldl combine Nothing (fmap (flip palPieceRestrict sl) ps) 
  where combine Nothing ps = ps
        combine ps Nothing = ps
        combine (Just (_, Palette ps)) (Just (_, Palette ps')) = Just (Nothing, pal) -- If the slice touches more than one subpal then it must be the whole thing.

palRestrict :: Palette -> Slice -> Palette
palRestrict pal sl = case palRestrictWName pal sl of
  Just (_, pal') -> pal'
  Nothing -> emptyPal

data SubstPiece where
  TensorPalSub :: Slice -> Ident -> PaletteSubst -> Slice -> Ident -> PaletteSubst -> SubstPiece
  -- UnitPalSub :: Unit -> SubstPiece 
  deriving (Show)
  
data PaletteSubst = PaletteSubst [SubstPiece]
  deriving (Show)
  
data TeleSubst where
  TeleSubst :: PaletteSubst -> [Term] -> TeleSubst
  deriving (Show)

data Ty where
  BaseTy :: Ident -> Ty

  Pi :: Ty -> Ty -> Ty
  Sg :: Ty -> Ty -> Ty

  Und :: Ty -> Ty
  Tensor :: Ty -> Ty -> Ty
  Hom :: Ty -> Ty -> Ty
  deriving (Show)

data Term where
  Check :: Term -> Ty -> Term

  Var :: Ident -> Term
  ZeroVar :: Ident -> Term

  Lam :: Ident -> Term -> Term
  App :: Term -> [Term] -> Term

  Pair :: Term -> Term -> Term
  Fst :: Term -> Term
  Snd :: Term -> Term
  
  UndIn :: Term -> Term
  UndOut :: Term -> Term
  
  TensorPair :: Slice -> Term -> Slice -> Term -> Term
  TensorElim :: Palette 
    -> {- Var names and their colours variables -} [(Ident, Colour)] 
    -> TeleSubst 
    -> {- which var in tele -} Ident 
    -> {- motive -} Ty 
    -> {- new left var and col -} (Ident, Ident) 
    -> {- new right var and col -} (Ident, Ident)
    -> {- branch -} Term 
    -> Term

  TensorElimSimple :: Term
    -> {- motive -} Ty 
    -> {- new left var and col -} (Ident, Ident) 
    -> {- new right var and col -} (Ident, Ident)
    -> {- branch -} Term 
    -> Term

  HomLam :: {- body colour -} Ident -> {- var colour -} Ident -> {- var name -} Ident -> Term -> Term
  HomApp :: Slice -> Term -> Slice -> Term -> Term
  
  deriving (Show)

data Decl where
  PostType :: Ident -> Decl
  Def :: Ident -> Term -> Ty -> Decl
  deriving (Show)
