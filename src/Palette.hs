module Palette where

data PalettePiece where
  TensorPal :: Palette -> Palette -> PalettePiece
  -- UnitPal :: PalettePiece
  deriving (Show, Eq)

data Palette = Palette [PalettePiece]
  deriving (Show, Eq)

emptyPal :: Palette
emptyPal = Palette []

palSize :: Palette -> Int
palSize (Palette ps) = length ps

data SubstPiece where
  TensorPalSub :: SliceIndex -> PaletteSubst -> SliceIndex -> PaletteSubst -> SubstPiece
  -- UnitPalSub :: Unit -> SubstPiece 
  deriving (Show, Eq)
  
data PaletteSubst = PaletteSubst [SubstPiece]
  deriving (Show, Eq)

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

colWkAt :: Int -> Palette -> {- Where the new one is-} ColourIndex -> {- The colour to be weakened-} ColourIndex -> ColourIndex
colWkAt amt (Palette ps) TopColour TopColour = TopColour
colWkAt amt (Palette ps) TopColour (LeftSub i c) = LeftSub (i+amt) c
colWkAt amt (Palette ps) TopColour (RightSub i c) = RightSub (i+amt) c
colWkAt amt (Palette ps) (LeftSub ni nc) (LeftSub i c)
  | ni == i = let (TensorPal pl pr) = ps !! i in 
                LeftSub ni (colWkAt amt pl nc c)
colWkAt amt (Palette ps) (LeftSub ni nc) c = c
colWkAt amt (Palette ps) (RightSub ni nc) (RightSub i c)
  | ni == i = let (TensorPal pl pr) = ps !! i in 
                RightSub ni (colWkAt amt pr nc c)
colWkAt amt (Palette ps) (RightSub ni nc) c = c

sliceWkTop :: Int  -> {- The slice to be weakened -} SliceIndex -> SliceIndex
sliceWkTop amt TopSlice = TopSlice
sliceWkTop amt BotSlice = BotSlice
sliceWkTop amt (SubSlice i l r) = SubSlice (i + amt) l r

colExtHom :: ColourIndex -> ColourIndex
colExtHom col = LeftSub 0 col

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



