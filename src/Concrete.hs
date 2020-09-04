module Concrete where

import Data.Maybe (mapMaybe)
import Data.List (nub)

type Ident = String

data PalettePiece where
  TensorPal :: Maybe Ident -> Palette -> Maybe Ident -> Palette -> PalettePiece
  -- UnitPal :: PalettePiece
  deriving (Show)

data Palette = Palette [PalettePiece]
  deriving (Show)

emptyPal :: Palette
emptyPal = Palette []

palLoneTensor :: (Ident, Ident) -> PalettePiece
palLoneTensor (r, b) = TensorPal (Just r) emptyPal (Just b) emptyPal

data Colour where
  NamedColour :: Ident -> Colour
  ZeroColour :: Colour
  TopColour :: Colour
  deriving (Eq, Show)

palAddTensor :: Palette -> Colour -> (Ident, Ident) -> Palette
palAddTensor (Palette ps) TopColour (r, b) = Palette $ (palLoneTensor (r, b)):ps
palAddTensor (Palette []) c (r, b) = error $ "Colour " ++ show c ++ " not found"
palAddTensor (Palette ((TensorPal cL pL@(Palette pLs) cR pR@(Palette pRs)):ps)) (NamedColour c) (r, b) 
  | cL == Just c = Palette ((TensorPal cL (Palette $ (palLoneTensor (r, b)):pLs) cR (Palette pRs)):ps)
  | cR == Just c = Palette ((TensorPal cL (Palette pLs) cR (Palette $ (palLoneTensor (r, b)):pRs)):ps)
  | otherwise = let Palette ps' = palAddTensor (Palette ps) (NamedColour c) (r, b) in
                  Palette $ (TensorPal cL (palAddTensor pL (NamedColour c) (r, b)) cL (palAddTensor pR (NamedColour c) (r, b))) : ps'
-- TODO: This could cause confusing errors if the colour name appears more than once. 

palExtHom :: Palette -> Maybe Ident -> Maybe Ident -> Palette
palExtHom pal bodyc yc = Palette [TensorPal bodyc pal yc emptyPal]

colExtHom :: {- body colour -} Ident -> Colour -> Colour
colExtHom bodyc TopColour = NamedColour bodyc
colExtHom bodyc (NamedColour n) = NamedColour n
colExtHom bodyc ZeroColour = ZeroColour

data Slice where 
  Slice :: {- Colour names -} [Colour] -> Slice
  deriving (Show, Eq)

sliceUnion :: Slice -> Slice -> Slice
sliceUnion (Slice sl1) (Slice sl2) = Slice $ nub (sl1 ++ sl2)

palRestrictHalf :: Slice -> Maybe Ident -> Palette -> Maybe (Maybe Ident, Palette)
palRestrictHalf sl@(Slice ns) (Just n) pal 
  | (NamedColour n) `elem` ns = Just (Just n, pal)
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

data TeleCell = TeleCell (Maybe Ident) Ty
  deriving (Show)
  
data PaletteSubst = PaletteSubst [SubstPiece]
  deriving (Show)
  
data TeleSubst where
  TeleSubst :: PaletteSubst -> [Term] -> TeleSubst
  deriving (Show)

type Ty = Term

data Term where
  Check :: Term -> Ty -> Term

  Univ :: Int -> Ty

  Pi :: [TeleCell] -> Ty -> Ty
  Sg :: [TeleCell] -> Ty -> Ty

  Und :: Ty -> Ty
  Tensor :: Maybe Ident -> Ty -> Ty -> Ty
  Hom :: Maybe Ident -> Ty -> Ty -> Ty

  Var :: Ident -> Term
  ZeroVar :: Ident -> Term

  Lam :: [Ident] -> Term -> Term
  App :: Term -> [Term] -> Term

  Pair :: Term -> Term -> Term
  Fst :: Term -> Term
  Snd :: Term -> Term
  
  UndIn :: Term -> Term
  UndOut :: Term -> Term
  
  TensorPair :: Maybe Slice -> Term -> Maybe Slice -> Term -> Term

  TensorElim :: Term
    -> {- motive var -} Maybe Ident -> {- motive -} Ty 
    -> {- new left var and col -} (Ident, Maybe Ident) 
    -> {- new right var and col -} (Ident, Maybe Ident)
    -> {- branch -} Term 
    -> Term

  TensorElimFrob :: Palette 
    -> {- Var names and their colours variables -} [(Ident, Colour)] 
    -> TeleSubst 
    -> {- which var in tele -} Ident 
    -> {- motive -} Ty 
    -> {- new left var and col -} (Ident, Maybe Ident) 
    -> {- new right var and col -} (Ident, Maybe Ident)
    -> {- branch -} Term 
    -> Term

  HomLam :: {- body colour -} Maybe Ident -> {- var colour -} Maybe Ident -> {- var name -} Ident -> Term -> Term
  HomApp :: Maybe Slice -> Term -> Maybe Slice -> Term -> Term
  
  deriving (Show)

data Decl where
  Def :: Ident -> Term -> Ty -> Decl
  Dont :: Ident -> Term -> Ty -> Decl
  deriving (Show)
