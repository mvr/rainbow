{-# LANGUAGE GADTs #-}
module Palette where

import Debug.Trace

data PalettePiece where
  TensorPal :: Palette -> Palette -> PalettePiece
  -- UnitPal :: PalettePiece
  deriving (Show)

data Palette = Palette [PalettePiece]
  deriving (Show)

emptyPal :: Palette
emptyPal = Palette []

data SubstPiece where
  TensorPalSub :: SliceIndex -> PaletteSubst -> SliceIndex -> PaletteSubst -> SubstPiece
  -- UnitPalSub :: Unit -> SubstPiece 
  deriving (Show)
  
data PaletteSubst = PaletteSubst [SubstPiece]
  deriving (Show)

data ColourIndex where -- DeBruijn indices for colours
  TopColour :: ColourIndex
  LeftSub :: Int -> ColourIndex -> ColourIndex
  RightSub :: Int -> ColourIndex -> ColourIndex
  deriving (Show, Eq)

data SliceIndex where 
  BotSlice :: SliceIndex
  TopSlice :: SliceIndex 
  SubSlice :: Int -> SliceIndex -> SliceIndex -> SliceIndex
  deriving (Show, Eq)

instance Semigroup SliceIndex where
  (<>) = curry unionDisjointSlice

instance Monoid SliceIndex where
  mempty = BotSlice

colourToSlice :: ColourIndex -> SliceIndex
colourToSlice TopColour       = TopSlice
colourToSlice (LeftSub i sl)  = SubSlice i (colourToSlice sl) BotSlice
colourToSlice (RightSub i sl) = SubSlice i BotSlice (colourToSlice sl)
  
palRestrict :: Palette -> SliceIndex -> Palette
palRestrict _ BotSlice = Palette []
palRestrict p TopSlice = p
palRestrict (Palette ps) (SubSlice i slL BotSlice) = let (TensorPal pl pr) = ps !! i in 
  palRestrict pl slL
palRestrict (Palette ps) (SubSlice i BotSlice slR) = let (TensorPal pl pr) = ps !! i in 
  palRestrict pr slR
palRestrict (Palette ps) (SubSlice i slL slR) = let (TensorPal pl pr) = ps !! i in 
  Palette [TensorPal (palRestrict pl slL) (palRestrict pr slR)]

colourRestrict :: ColourIndex -> SliceIndex -> Maybe ColourIndex
-- colourRestrict c sl | traceShow (c, sl) False = undefined  
colourRestrict c TopSlice = Just c
colourRestrict c BotSlice = Nothing
colourRestrict TopColour (SubSlice j slL slR) = Nothing
colourRestrict (LeftSub i c)  (SubSlice j slL BotSlice) | i == j = colourRestrict c slL
colourRestrict (LeftSub i c)  (SubSlice j BotSlice _)   | i == j = Nothing
colourRestrict (LeftSub i c)  (SubSlice j slL slR)      | i == j = LeftSub  0 <$> colourRestrict c slL
colourRestrict (RightSub i c) (SubSlice j BotSlice slR) | i == j = colourRestrict c slR
colourRestrict (RightSub i c) (SubSlice j _ BotSlice)   | i == j = Nothing
colourRestrict (RightSub i c) (SubSlice j slL slR)      | i == j = RightSub 0 <$> colourRestrict c slR
colourRestrict _ _ = Nothing

validSplit :: (SliceIndex, SliceIndex) -> Bool
-- validSplit p | traceShow p False = undefined  
validSplit (BotSlice, BotSlice) = True
validSplit p = validSplit' p

validSplit' :: (SliceIndex, SliceIndex) -> Bool
validSplit' (BotSlice, BotSlice) = True
validSplit' (TopSlice, BotSlice) = True
validSplit' (BotSlice, TopSlice) = True
validSplit' (SubSlice i slLL slLR, SubSlice j slRL slRR) | i == j = validSplit' (slLL, slRL) && validSplit' (slLR, slRR)
validSplit' _ = False

unionDisjointSlice :: (SliceIndex, SliceIndex) -> SliceIndex
unionDisjointSlice (sl, BotSlice) = sl
unionDisjointSlice (BotSlice, sl) = sl
unionDisjointSlice (SubSlice i slLL slLR, SubSlice j slRL slRR) 
  | i == j = case (unionDisjointSlice (slLL, slRL), unionDisjointSlice (slLR, slRR)) of
      (TopSlice, TopSlice) -> TopSlice
      (BotSlice, BotSlice) -> BotSlice
      (slL, slR) -> SubSlice i slL slR
  | otherwise = TopSlice 
unionDisjointSlice r = error $ "undefined here " ++ show r -- TODO

sliceSubst :: SliceIndex -> PaletteSubst -> SliceIndex
sliceSubst BotSlice _ = BotSlice
sliceSubst TopSlice _ = TopSlice
sliceSubst (SubSlice i TopSlice slR) (PaletteSubst ps) = let (TensorPalSub slL psL _ psR) = ps !! i in unionDisjointSlice (slL, sliceSubst slR psR)
sliceSubst (SubSlice i slL TopSlice) (PaletteSubst ps) = let (TensorPalSub _ psL slR psR) = ps !! i in unionDisjointSlice (sliceSubst slL psL, slR)
sliceSubst (SubSlice i slL slR) (PaletteSubst ps) = let (TensorPalSub _ psL _ psR) = ps !! i in unionDisjointSlice (sliceSubst slL psL, sliceSubst slR psR)

palExtend :: Palette -> Palette -> Palette
palExtend (Palette p1) (Palette p2) = Palette (p1 ++ p2)

palAddTensor :: Palette -> ColourIndex -> (Palette, ColourIndex, ColourIndex)
palAddTensor (Palette ps) TopColour = (Palette (new:ps), LeftSub 0 TopColour, RightSub 0 TopColour)
  where new = TensorPal (Palette []) (Palette [])
palAddTensor (Palette ps) (LeftSub i c) = 
  let (before,(TensorPal pl pr):after) = splitAt i ps 
      (new, r, b) = palAddTensor pl c
  in (Palette (before ++ [TensorPal new pr] ++ after), LeftSub i r, LeftSub i b)
palAddTensor (Palette ps) (RightSub i c) = 
  let (before,(TensorPal pl pr):after) = splitAt i ps 
      (new, r, b) = palAddTensor pr c
  in (Palette (before ++ [TensorPal pl new] ++ after), RightSub i r, RightSub i b)

palWkAt :: Int -> Palette -> {- Where the new one is-} ColourIndex -> {- The colour to be weakened-} ColourIndex -> ColourIndex
palWkAt amt (Palette ps) TopColour TopColour = TopColour
palWkAt amt (Palette ps) TopColour (LeftSub i c) = LeftSub (i+amt) c
palWkAt amt (Palette ps) TopColour (RightSub i c) = RightSub (i+amt) c
palWkAt amt (Palette ps) (LeftSub ni nc) (LeftSub i c)
  | ni == i = let (TensorPal pl pr) = ps !! i in 
                LeftSub ni (palWkAt amt pl nc c)
palWkAt amt (Palette ps) (LeftSub ni nc) c = c
palWkAt amt (Palette ps) (RightSub ni nc) (RightSub i c)
  | ni == i = let (TensorPal pl pr) = ps !! i in 
                RightSub ni (palWkAt amt pr nc c)
palWkAt amt (Palette ps) (RightSub ni nc) c = c

--------------------------------------------------
-- If we don't allow Top or Bot as a subslice:


-- data ColourIndex where -- DeBruijn indices for colours
--   TopColour :: ColourIndex
--   LeftOf :: Int -> ColourIndex 
--   RightOf :: Int -> ColourIndex
--   LeftSub :: Int -> ColourIndex -> ColourIndex
--   RightSub :: Int -> ColourIndex -> ColourIndex
--   deriving (Show, Eq)

-- data SliceIndex where 
--   BotSlice :: SliceIndex
--   TopSlice :: SliceIndex 
--   LeftAllSlice :: Int  -> SliceIndex
--   RightAllSlice :: Int -> SliceIndex
--   LeftSubSlice :: Int -> SliceIndex -> SliceIndex
--   RightSubSlice :: Int -> SliceIndex -> SliceIndex
--   LeftSubRightAllSlice :: Int -> SliceIndex -> SliceIndex 
--   LeftAllRightSubSlice :: Int -> SliceIndex -> SliceIndex 
--   BothSubSlice :: Int -> SliceIndex -> SliceIndex -> SliceIndex
--   deriving (Show, Eq)

-- instance Semigroup SliceIndex where
--   (<>) = unionSliceIndex

-- instance Monoid SliceIndex where
--   mempty = BotSlice

-- colourToSlice :: ColourIndex -> SliceIndex
-- colourToSlice TopColour       = TopSlice
-- colourToSlice (LeftOf idx)    = LeftAllSlice idx
-- colourToSlice (RightOf idx)   = RightAllSlice idx
-- colourToSlice (LeftSub i sl)  = LeftSubSlice i (colourToSlice sl)
-- colourToSlice (RightSub i sl) = RightSubSlice i (colourToSlice sl)

-- validSplit :: (SliceIndex, SliceIndex) -> Bool
-- validSplit (sl, sl') = validSplitNoSym (sl, sl') || validSplitNoSym (sl', sl)

-- validSplitNoSym :: (SliceIndex, SliceIndex) -> Bool
-- validSplitNoSym (BotSlice, BotSlice) = True
-- validSplitNoSym (TopSlice, BotSlice) = True -- TODO: Sort of, these should be unit instead of bot.
-- validSplitNoSym (LeftAllSlice i, RightAllSlice j) | i == j = True
-- validSplitNoSym (LeftSubSlice i sl, LeftSubRightAllSlice j sl') | i == j = validSplit (sl, sl')
-- validSplitNoSym (RightSubSlice i sl, LeftAllRightSubSlice j sl') | i == j = validSplit (sl, sl')
-- validSplitNoSym (BothSubSlice i slLL slLR, BothSubSlice j slRL slRR) | i == j = validSplit (slLL, slRL) && validSplit (slLR, slRR)

-- unionDisjointSlice :: (SliceIndex, SliceIndex) -> SliceIndex
-- unionDisjointSlice (BotSlice, BotSlice) = BotSlice
-- unionDisjointSlice (TopSlice, BotSlice) = TopSlice
-- unionDisjointSlice (BotSlice, TopSlice) = TopSlice
-- unionDisjointSlice (LeftSubSlice i sl1, LeftSubSlice j sl2) | i == j = LeftSubSlice i (unionDisjointSlice (sl1, sl2))
-- unionDisjointSlice (LeftSubSlice i sl1, LeftSubRightAllSlice j sl2) | i == j = LeftSubRightAllSlice i (unionDisjointSlice (sl1, sl2))
-- unionDisjointSlice (LeftSubSlice i sl1, BothSubSlice j sl2L sl2R) | i == j = LeftSubRightAllSlice i (unionDisjointSlice (sl1, sl2))
-- unionDisjointSlice (RightSubSlice i sl1, RightSubSlice j sl2) | i == j = RightSubSlice i (unionDisjointSlice (sl1, sl2))
-- unionDisjointSlice _ = undefined -- TODO

-- sliceSubst :: SliceIndex -> PaletteSubst -> SliceIndex
-- sliceSubst BotSlice _ = BotSlice
-- sliceSubst TopSlice _ = TopSlice
-- sliceSubst (LeftAllSlice i) (PaletteSubst ps) = let (TensorPalSub slL _ _ _) = ps !! i in slL
-- sliceSubst (RightAllSlice i) (PaletteSubst ps) = let (TensorPalSub _ _ slR _) = ps !! i in slR
-- sliceSubst (LeftSubSlice i sl) (PaletteSubst ps) = let (TensorPalSub _ psL _ _) = ps !! i in sliceSubst sl psL
-- sliceSubst (RightSubSlice i sl) (PaletteSubst ps) = let (TensorPalSub _ _ _ psR) = ps !! i in sliceSubst sl psR
-- sliceSubst (LeftSubRightAllSlice i sl) (PaletteSubst ps) = let (TensorPalSub _ psL slR _) = ps !! i in unionDisjointSlice (sliceSubst sl psL, slR)
-- sliceSubst (LeftAllRightSubSlice i sl) (PaletteSubst ps) = let (TensorPalSub slL _ _ psR) = ps !! i in unionDisjointSlice (slL, sliceSubst sl psR)
-- sliceSubst (BothSubSlice i slL slR) (PaletteSubst ps) = let (TensorPalSub _ psL _ psR) = ps !! i in unionDisjointSlice (sliceSubst slL psL, sliceSubst slR psR)

-- palElimTensor :: Palette -> ColourIndex -> (Palette, ColourIndex, ColourIndex)
-- palElimTensor = undefined

--------------------------------------------------
--- Level stuff  

-- data ColourLevel where -- DeBruijn levels for colours, a depth first labelling of the tree
--   BotColour   :: ColourLevel -- And the zero 'colour'
--   UpColour    :: Int -> ColourLevel
--   UpThenLeft  :: Int -> Int -> ColourLevel -> ColourLevel -- First is how far up the left spine to go, then the idx of which pal in the comma bunch
--   UpThenRight :: Int -> Int -> ColourLevel -> ColourLevel
--   deriving (Show, Eq)

-- colourIndexToLevel :: Palette -> ColourIndex -> ColourLevel
-- colourIndexToLevel pal TopColour = UpColour (depth pal)
--   where depth Start = 0
--         depth (Palette []) = error "invalid Palette"
--         depth (Palette (TensorPal a b : ps)) = 1 + depth a
-- colourIndexToLevel (Palette []) (LeftOf ix) = error "invalid ColourIndex"
-- colourIndexToLevel Start (LeftOf ix) = error "invalid ColourIndex"
-- colourIndexToLevel (Palette ps@(p:rest)) (LeftOf ix) 
--   | ix >= length ps = error "invalid ColourIndex"
--   | otherwise = undefined -- TODO
-- -- zzz todo: boring

-- data SliceLevel where 
--   BotSlice :: SliceLevel
--   UpSlice :: Int -> SliceLevel
--   UpThenLeftSubSlice  :: Int -> Int -> SliceLevel -> SliceLevel -- First is how far up the left spine to go, then the idx of which pal in the comma bunch
--   UpThenRightSubSlice :: Int -> Int -> SliceLevel -> SliceLevel
--   UpThenLeftSubRightAllSlice  :: Int -> Int -> SliceLevel -> SliceLevel 
--   UpThenLeftAllRightSubSlice :: Int -> Int -> SliceLevel -> SliceLevel
--   UpThenBothSlice  :: Int -> Int -> SliceLevel -> SliceLevel -> SliceLevel
--   deriving (Show, Eq)


-- instance Semigroup SliceLevel where
--   (<>) = undefined
-- instance Monoid SliceLevel where
--   mempty = undefined



