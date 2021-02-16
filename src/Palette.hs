module Palette where

data Palette where
  CommaPal :: Palette -> Palette -> Palette
  OnePal :: Palette
  OriginOnePal :: Palette
  TensorPal :: Palette -> Palette -> Palette
  UnitPal :: Palette
  deriving (Show, Eq)

cleverCommaPal :: Palette -> Palette -> Palette
-- Note: We don't want to cancel the origin one
cleverCommaPal OnePal p = p
cleverCommaPal p OnePal = p
cleverCommaPal p q = CommaPal p q

-- palSize :: Palette -> Int
-- palSize (Palette ps) = length ps

data ColourIx where -- DeBruijn indices for colours
  HereColIx :: ColourIx
  LeftCommaColIx :: ColourIx -> ColourIx
  RightCommaColIx :: ColourIx -> ColourIx
  LeftTensorColIx :: ColourIx -> ColourIx
  RightTensorColIx :: ColourIx -> ColourIx
  deriving (Show, Eq)

data SliceIx where
  HereSliceIx :: SliceIx
  BotSliceIx :: SliceIx
  LeftCommaSliceIx :: SliceIx -> SliceIx
  RightCommaSliceIx :: SliceIx -> SliceIx
  -- LeftTensorSliceIx ::  SliceIx -> SliceIx -- Instead implement these by TensorSliceIx BotSlice etc.
  -- RightTensorSliceIx :: SliceIx -> SliceIx
  TensorSliceIx :: SliceIx -> SliceIx -> SliceIx

  deriving (Show, Eq)

cleverTensor :: SliceIx -> SliceIx -> SliceIx
cleverTensor BotSliceIx s = s
cleverTensor s BotSliceIx = s
cleverTensor sl sr = TensorSliceIx sl sr

-- instance Semigroup SliceIx where
--   (<>) = curry unionDisjointSlice

-- instance Monoid SliceIx where
--   mempty = BotSlice

colourToSlice :: ColourIx -> SliceIx
colourToSlice HereColIx       = HereSliceIx
colourToSlice (LeftCommaColIx s) = LeftCommaSliceIx (colourToSlice s)
colourToSlice (RightCommaColIx s) = RightCommaSliceIx (colourToSlice s)
colourToSlice (LeftTensorColIx s)  = TensorSliceIx (colourToSlice s) BotSliceIx
colourToSlice (RightTensorColIx s) = TensorSliceIx BotSliceIx (colourToSlice s)

palRestrict :: Palette -> SliceIx -> Palette
palRestrict _ BotSliceIx = OnePal
palRestrict p HereSliceIx = p
palRestrict (CommaPal pl _) (LeftCommaSliceIx s) = palRestrict pl s
palRestrict (CommaPal _ pr) (RightCommaSliceIx s) = palRestrict pr s
palRestrict (TensorPal pl pr) (TensorSliceIx sl BotSliceIx) = palRestrict pl sl
palRestrict (TensorPal pl pr) (TensorSliceIx BotSliceIx sr) = palRestrict pr sr
palRestrict (TensorPal pl pr) (TensorSliceIx sl sr) = TensorPal (palRestrict pl sl) (palRestrict pr sr)

-- FIXME: It seems the Palette isn't necessary
-- The idea is, if `s2` is a slice of `palRestrict p s1`, then `sliceComp s1 s2` is a slice of `p`.
sliceComp :: SliceIx -> SliceIx -> SliceIx
sliceComp BotSliceIx s2 = BotSliceIx
sliceComp HereSliceIx s2 = s2
sliceComp (LeftCommaSliceIx s) s2 = LeftCommaSliceIx (sliceComp s s2)
sliceComp (RightCommaSliceIx s) s2 = RightCommaSliceIx (sliceComp s s2)
sliceComp (TensorSliceIx sl BotSliceIx) s2 = TensorSliceIx (sliceComp sl s2) BotSliceIx
sliceComp (TensorSliceIx BotSliceIx sr) s2 = TensorSliceIx BotSliceIx (sliceComp sr s2)
sliceComp (TensorSliceIx sl sr) (TensorSliceIx s2l s2r) = TensorSliceIx (sliceComp sl s2l) (sliceComp sr s2r)

colourRestrict :: ColourIx -> SliceIx -> Maybe ColourIx
-- colourRestrict c sl | traceShow (c, sl) False = undefined
colourRestrict c HereSliceIx = Just c
colourRestrict c BotSliceIx = Nothing
colourRestrict (LeftCommaColIx c) (LeftCommaSliceIx sl) = colourRestrict c sl
colourRestrict (RightCommaColIx c) (RightCommaSliceIx sl) = colourRestrict c sl
colourRestrict (LeftTensorColIx c) (TensorSliceIx sl BotSliceIx) = colourRestrict c sl
colourRestrict (LeftTensorColIx c) (TensorSliceIx BotSliceIx sr) = Nothing
colourRestrict (LeftTensorColIx c) (TensorSliceIx sl _) = LeftTensorColIx <$> colourRestrict c sl
colourRestrict (RightTensorColIx c) (TensorSliceIx sl BotSliceIx) = Nothing
colourRestrict (RightTensorColIx c) (TensorSliceIx BotSliceIx sr) = colourRestrict c sr
colourRestrict (RightTensorColIx c) (TensorSliceIx _ sr) = RightTensorColIx <$> colourRestrict c sr
colourRestrict _ _ = Nothing

-- FIXME: does this end up being necessary?
validSplit :: (SliceIx, SliceIx) -> Bool
-- validSplit p | traceShow p False = undefined
validSplit (BotSliceIx, BotSliceIx) = True
validSplit p = validSplit' p

validSplit' :: (SliceIx, SliceIx) -> Bool
validSplit' (BotSliceIx, BotSliceIx) = True
validSplit' (HereSliceIx, BotSliceIx) = True
validSplit' (BotSliceIx, HereSliceIx) = True
validSplit' (LeftCommaSliceIx s, LeftCommaSliceIx s') = validSplit (s, s')
validSplit' (RightCommaSliceIx s, RightCommaSliceIx s') = validSplit (s, s')
validSplit' (TensorSliceIx sl sr, TensorSliceIx sl' sr') = validSplit' (sl, sl') && validSplit' (sr, sr')
validSplit' _ = False

unionDisjointSlice :: (SliceIx, SliceIx) -> SliceIx
unionDisjointSlice (sl, BotSliceIx) = sl
unionDisjointSlice (BotSliceIx, sl) = sl
unionDisjointSlice (LeftCommaSliceIx s1, LeftCommaSliceIx s2) = LeftCommaSliceIx (unionDisjointSlice (s1, s2))
unionDisjointSlice (RightCommaSliceIx s1, RightCommaSliceIx s2) = RightCommaSliceIx (unionDisjointSlice (s1, s2))
unionDisjointSlice (TensorSliceIx s1l s1r, TensorSliceIx s2l s2r) = TensorSliceIx (unionDisjointSlice (s1l, s2l)) (unionDisjointSlice (s1r, s2r))
-- unionDisjointSlice (SubSlice i slLL slLR, SubSlice j slRL slRR)
--   | i == j = case (unionDisjointSlice (slLL, slRL), unionDisjointSlice (slLR, slRR)) of
--       (TopSlice, TopSlice) -> TopSlice
--       (BotSlice, BotSlice) -> BotSlice
--       (slL, slR) -> SubSlice i slL slR
--   | otherwise = TopSlice
unionDisjointSlice r = error $ "undefined here " ++ show r -- TODO

data UnitIx where
  HereUnitIx :: UnitIx
  LeftCommaUnitIx :: UnitIx -> UnitIx
  RightCommaUnitIx :: UnitIx -> UnitIx
  LeftTensorUnitIx :: UnitIx -> UnitIx
  RightTensorUnitIx :: UnitIx -> UnitIx

  deriving (Show, Eq)

data PaletteSubst where
  OnePalSub :: PaletteSubst
  CommaPalSub :: PaletteSubst -> PaletteSubst -> PaletteSubst
  UnitPalSub :: UnitIx -> PaletteSubst
  TensorPalSub :: SliceIx -> PaletteSubst -> SliceIx -> PaletteSubst -> PaletteSubst

  -- UnitPalSub :: Unit -> SubstPiece
  deriving (Show, Eq)

sliceSubst :: SliceIx -> PaletteSubst -> SliceIx
sliceSubst BotSliceIx _ = BotSliceIx
sliceSubst HereSliceIx _ = HereSliceIx
sliceSubst (LeftCommaSliceIx s) (CommaPalSub tl tr) = sliceSubst s tl
sliceSubst (RightCommaSliceIx s) (CommaPalSub tl tr) = sliceSubst s tr
sliceSubst (TensorSliceIx sl sr) (TensorPalSub doml tl domr tr) =
  let sl' = sliceSubst sl tl
      sr' = sliceSubst sr tr
  in unionDisjointSlice ((sliceComp doml sl'), (sliceComp domr sr'))
-- sliceSubst (SubSlice i TopSlice slR) (PaletteSubst ps) = let (TensorPalSub slL psL _ psR) = ps !! i in unionDisjointSlice (slL, sliceSubst slR psR)
-- sliceSubst (SubSlice i slL TopSlice) (PaletteSubst ps) = let (TensorPalSub _ psL slR psR) = ps !! i in unionDisjointSlice (sliceSubst slL psL, slR)
-- sliceSubst (SubSlice i slL slR) (PaletteSubst ps) = let (TensorPalSub _ psL _ psR) = ps !! i in unionDisjointSlice (sliceSubst slL psL, sliceSubst slR psR)

-- palExtend :: Palette -> Palette -> Palette
-- palExtend (Palette p1) (Palette p2) = Palette (p1 ++ p2)

-- palAddTensor :: Palette -> ColourIx -> (Palette, ColourIx, ColourIx)
-- palAddTensor (Palette ps) TopColour = (Palette (new:ps), LeftSub 0 TopColour, RightSub 0 TopColour)
--   where new = TensorPal (Palette []) (Palette [])
-- palAddTensor (Palette ps) (LeftSub i c) =
--   let (before,(TensorPal pl pr):after) = splitAt i ps
--       (new, r, b) = palAddTensor pl c
--   in (Palette (before ++ [TensorPal new pr] ++ after), LeftSub i r, LeftSub i b)
-- palAddTensor (Palette ps) (RightSub i c) =
--   let (before,(TensorPal pl pr):after) = splitAt i ps
--       (new, r, b) = palAddTensor pr c
--   in (Palette (before ++ [TensorPal pl new] ++ after), RightSub i r, RightSub i b)

-- colWkAt :: Int -> Palette -> {- Where the new one is-} ColourIx -> {- The colour to be weakened-} ColourIx -> ColourIx
-- colWkAt amt (Palette ps) TopColour TopColour = TopColour
-- colWkAt amt (Palette ps) TopColour (LeftSub i c) = LeftSub (i+amt) c
-- colWkAt amt (Palette ps) TopColour (RightSub i c) = RightSub (i+amt) c
-- colWkAt amt (Palette ps) (LeftSub ni nc) (LeftSub i c)
--   | ni == i = let (TensorPal pl pr) = ps !! i in
--                 LeftSub ni (colWkAt amt pl nc c)
-- colWkAt amt (Palette ps) (LeftSub ni nc) c = c
-- colWkAt amt (Palette ps) (RightSub ni nc) (RightSub i c)
--   | ni == i = let (TensorPal pl pr) = ps !! i in
--                 RightSub ni (colWkAt amt pr nc c)
-- colWkAt amt (Palette ps) (RightSub ni nc) c = c

-- sliceWkTop :: Int  -> {- The slice to be weakened -} SliceIx -> SliceIx
-- sliceWkTop amt TopSlice = TopSlice
-- sliceWkTop amt BotSlice = BotSlice
-- sliceWkTop amt (SubSlice i l r) = SubSlice (i + amt) l r

-- colExtHom :: ColourIx -> ColourIx
-- colExtHom col = LeftSub 0 col

--------------------------------------------------
--- Lvl stuff

-- data ColourLvl where -- DeBruijn levels for colours, a depth first labelling of the tree
--   BotColour   :: ColourLvl -- And the zero 'colour'
--   UpColour    :: Int -> ColourLvl
--   UpThenLeft  :: Int -> Int -> ColourLvl -> ColourLvl -- First is how far up the left spine to go, then the idx of which pal in the comma bunch
--   UpThenRight :: Int -> Int -> ColourLvl -> ColourLvl
--   deriving (Show, Eq)

-- colourIxToLvl :: Palette -> ColourIx -> ColourLvl
-- colourIxToLvl pal TopColour = UpColour (depth pal)
--   where depth Start = 0
--         depth (Palette []) = error "invalid Palette"
--         depth (Palette (TensorPal a b : ps)) = 1 + depth a
-- colourIxToLvl (Palette []) (LeftOf ix) = error "invalid ColourIx"
-- colourIxToLvl Start (LeftOf ix) = error "invalid ColourIx"
-- colourIxToLvl (Palette ps@(p:rest)) (LeftOf ix)
--   | ix >= length ps = error "invalid ColourIx"
--   | otherwise = undefined -- TODO
-- -- zzz todo: boring


data SliceLvl where
  UpSliceLvl :: SliceLvl -> SliceLvl

  BotSliceLvl :: SliceLvl
  HereSliceLvl :: SliceLvl

  LeftCommaSliceLvl :: SliceLvl -> SliceLvl
  RightCommaSliceLvl :: SliceLvl -> SliceLvl
  TensorSliceLvl :: SliceLvl -> SliceLvl -> SliceLvl
  deriving (Show, Eq)

unionDisjointSliceLvl :: SliceLvl -> SliceLvl -> SliceLvl
unionDisjointSliceLvl (UpSliceLvl l) (UpSliceLvl r) = UpSliceLvl (l `unionDisjointSliceLvl` r)
unionDisjointSliceLvl BotSliceLvl BotSliceLvl = BotSliceLvl
unionDisjointSliceLvl (LeftCommaSliceLvl l) (LeftCommaSliceLvl r) = LeftCommaSliceLvl (l `unionDisjointSliceLvl` r)
unionDisjointSliceLvl (RightCommaSliceLvl l) (RightCommaSliceLvl r) = RightCommaSliceLvl (l `unionDisjointSliceLvl` r)
unionDisjointSliceLvl (TensorSliceLvl ll lr) (TensorSliceLvl rl rr) = TensorSliceLvl (ll `unionTensorSide` rl) (lr `unionTensorSide` rr)

-- For use just in the above
unionTensorSide :: SliceLvl -> SliceLvl -> SliceLvl
unionTensorSide HereSliceLvl BotSliceLvl = HereSliceLvl
unionTensorSide BotSliceLvl HereSliceLvl = HereSliceLvl
unionTensorSide BotSliceLvl BotSliceLvl = error "Shouldn't happen"
unionTensorSide BotSliceLvl s = s
unionTensorSide s BotSliceLvl = s
unionTensorSide l r = l `unionDisjointSliceLvl` r

data UnitLvl where
  UpUnitLvl :: UnitLvl -> UnitLvl

  BotUnitLvl :: UnitLvl

  HereUnitLvl :: UnitLvl
  LeftCommaUnitLvl :: UnitLvl -> UnitLvl
  RightCommaUnitLvl :: UnitLvl -> UnitLvl
  LeftTensorUnitLvl :: UnitLvl -> UnitLvl
  RightTensorUnitLvl :: UnitLvl -> UnitLvl

  deriving (Show, Eq)

-- instance Semigroup SliceLvl where
--   (<>) = undefined
-- instance Monoid SliceLvl where
--   mempty = undefined



data SemPal where
  CommaSemPal :: SemPal -> SemPal -> SemPal
  OneSemPal :: SemPal
  OriginSemPal :: SemPal
  TensorSemPal :: SliceLvl -> SemPal -> SliceLvl ->  SemPal -> SemPal
  UnitSemPal :: UnitLvl -> SemPal
  deriving (Eq, Show)

cleverCommaSemPal :: SemPal -> SemPal -> SemPal
cleverCommaSemPal OneSemPal p = p
cleverCommaSemPal p OneSemPal = p
cleverCommaSemPal p q = CommaSemPal p q

semEnvTopSlice :: SemPal -> SliceLvl
semEnvTopSlice (CommaSemPal l _) = UpSliceLvl (semEnvTopSlice l)
semEnvTopSlice (TensorSemPal _ l _ _) = UpSliceLvl (semEnvTopSlice l)
semEnvTopSlice (OriginSemPal) = HereSliceLvl

lookupSlice :: SemPal -> SliceIx -> SliceLvl
lookupSlice pal HereSliceIx = semEnvTopSlice pal  -- Should only occur if HereSliceIx is representing the top slice
lookupSlice pal BotSliceIx = BotSliceLvl
lookupSlice (CommaSemPal pl pr) (LeftCommaSliceIx HereSliceIx) = error "Shouldn't happen"
lookupSlice (CommaSemPal pl pr) (LeftCommaSliceIx s) = lookupSlice pl s
lookupSlice (CommaSemPal pl pr) (RightCommaSliceIx HereSliceIx) = error "Shouldn't happen"
lookupSlice (CommaSemPal pl pr) (RightCommaSliceIx s) = lookupSlice pr s
lookupSlice (TensorSemPal sl pl sr pr) (TensorSliceIx HereSliceIx BotSliceIx) = sl
lookupSlice (TensorSemPal sl pl sr pr) (TensorSliceIx BotSliceIx HereSliceIx) = sr
lookupSlice (TensorSemPal sl pl sr pr) (TensorSliceIx HereSliceIx HereSliceIx) = sl `unionDisjointSliceLvl` sr
lookupSlice (TensorSemPal sl pl sr pr) (TensorSliceIx BotSliceIx BotSliceIx) = error "Shouldn't happen"
lookupSlice (TensorSemPal sl pl sr pr) (TensorSliceIx sl' BotSliceIx) = lookupSlice pl sl'
lookupSlice (TensorSemPal sl pl sr pr) (TensorSliceIx BotSliceIx sr') = lookupSlice pr sr'
lookupSlice (TensorSemPal sl pl sr pr) (TensorSliceIx sl' HereSliceIx) = lookupSlice pl sl' `unionDisjointSliceLvl` sr
lookupSlice (TensorSemPal sl pl sr pr) (TensorSliceIx HereSliceIx sr') = sl `unionDisjointSliceLvl` lookupSlice pr sr'
lookupSlice (TensorSemPal sl pl sr pr) (TensorSliceIx sl' sr') = lookupSlice pl sl' `unionDisjointSliceLvl` lookupSlice pr sr'

sliceIxToLvl :: Palette -> SliceIx -> SliceLvl
sliceIxToLvl = undefined

sliceLvlToIx :: Palette -> SliceLvl -> SliceIx
sliceLvlToIx = undefined
