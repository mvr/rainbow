module Palette where

data Palette where
  CommaPal :: Palette -> Palette -> Palette
  OnePal :: Palette
  OriginPal :: Palette
  TensorPal :: Palette -> Palette -> Palette
  UnitPal :: Palette
  deriving (Show, Eq)

-- cleverCommaPal :: Palette -> Palette -> Palette
-- -- Note: We don't want to cancel the origin one
-- cleverCommaPal OnePal p = p
-- cleverCommaPal p OnePal = p
-- cleverCommaPal p q = CommaPal p q

-- palSize :: Palette -> Int
-- palSize (Palette ps) = length ps

-- data ColI where -- DeBruijn indices for colours
--   TopColI :: ColI
--   LeftColI :: ColI -- The colour exactly here on the left of a tensor.
--   RightColI :: ColI
--   LeftCommaColI :: ColI -> ColI
--   RightCommaColI :: ColI -> ColI
--   LeftTensorColI :: ColI -> ColI
--   RightTensorColI :: ColI -> ColI
--   deriving (Show, Eq)

data Choice a = Yes | No | Sub a
  deriving (Show, Eq, Functor)

instance Semigroup a => Semigroup (Choice a) where
  Yes <> No = Yes
  No <> Yes = Yes
  No <> No = No
  (Sub a) <> No = Sub a
  No <> (Sub a) = Sub a
  (Sub a) <> (Sub b) = Sub (a <> b)

data SlI where
  TopSl :: SlI
  OneSl :: SlI
  SummonedUnitSl :: SlI
  -- LeftCommaSl :: SlI -> SlI
  -- RightCommaSl :: SlI -> SlI
  CommaSl :: Choice SlI -> Choice SlI -> SlI -- We have to use this rather than the previous, consider what happens when the palette is extended in a match statement
  TensorSl :: Choice SlI -> Choice SlI -> SlI
  deriving (Show, Eq)

-- cleverTensor :: SlI -> SlI -> SlI
-- cleverTensor BotSlI s = s
-- cleverTensor s BotSlI = s
-- cleverTensor sl sr = TensorSlI sl sr


-- This combining operation like the tensor internal to a
-- fixed palette.
instance Semigroup SlI where
  -- Cheating of course, we error if things don't line up.
  OneSl <> s = s
  s <> OneSl = s
  -- (LeftCommaSl l) <> (LeftCommaSl r) = LeftCommaSl (l <> r)
  -- (RightCommaSl l) <> (RightCommaSl r) = RightCommaSl (l <> r)
  (CommaSl (Sub l) No) <> (CommaSl (Sub r) No) = CommaSl (Sub $ l <> r) No
  (CommaSl No (Sub l)) <> (CommaSl No (Sub r)) = CommaSl No (Sub $ l <> r)
  (TensorSl ll lr) <> (TensorSl rl rr) = TensorSl (ll <> rl) (lr <> rr)

instance Monoid SlI where
  mempty = OneSl

-- colourToSlice :: ColI -> SlI
-- colourToSlice TopColI       = TopSl
-- colourToSlice LeftColI      = TensorSl Yes No
-- colourToSlice RightColI      = TensorSl No Yes
-- colourToSlice (LeftCommaColI s) = LeftCommaSl (colourToSlice s)
-- colourToSlice (RightCommaColI s) = RightCommaSl (colourToSlice s)
-- colourToSlice (LeftTensorColI s)  = TensorSl (Sub $ colourToSlice s) No
-- colourToSlice (RightTensorColI s) = TensorSl No (Sub $ colourToSlice s)

-- colourUsableIn :: ColI -> SlI -> Bool
-- colourUsableIn = undefined

-- FIXME: incomplete
weakenableTo :: SlI -> SlI -> Bool
weakenableTo OneSl _ = True
weakenableTo TopSl TopSl = True
weakenableTo TopSl _ = False
weakenableTo (TensorSl Yes Yes) TopSl = True
weakenableTo (TensorSl (Sub l) (Sub r)) TopSl = weakenableTo l TopSl && weakenableTo r TopSl
weakenableTo (TensorSl (Sub l) Yes) TopSl = weakenableTo l TopSl
weakenableTo (TensorSl Yes (Sub r)) TopSl = weakenableTo r TopSl
weakenableTo (TensorSl _ _) TopSl = False
weakenableTo (TensorSl l1 r1) (TensorSl l2 r2) = tchoice l1 l2 && tchoice r1 r2
  where tchoice Yes Yes = True
        tchoice No No = True
        tchoice (Sub s) Yes = weakenableTo s TopSl
        tchoice (Sub s1) (Sub s2) = weakenableTo s1 s2
        tchoice _ _ = False
weakenableTo (CommaSl l1 r1) (CommaSl l2 r2) = cchoice l1 l2 && cchoice r1 r2
  where cchoice Yes Yes = True
        cchoice No _ = True
        cchoice (Sub s) Yes = weakenableTo s TopSl
        cchoice (Sub s1) (Sub s2) = weakenableTo s1 s2
        cchoice _ _ = False
weakenableTo SummonedUnitSl SummonedUnitSl = True
weakenableTo l r = error $ "Unhandled " ++ show (l, r)

-- palRestrict :: Palette -> SlI -> Palette
-- palRestrict _ BotSlI = OriginPal
-- palRestrict p TopSlI = p
-- palRestrict (CommaPal pl _) (LeftCommaSlI s) = palRestrict pl s
-- palRestrict (CommaPal _ pr) (RightCommaSlI s) = palRestrict pr s
-- palRestrict (TensorPal pl pr) (TensorSlI Yes No) = pl
-- palRestrict (TensorPal pl pr) (TensorSlI No Yes) = pr
-- palRestrict (TensorPal pl pr) (TensorSlI (Sub sl) Yes) = TensorPal (palRestrict pl sl) pr
-- palRestrict (TensorPal pl pr) (TensorSlI Yes (Sub sr)) = TensorPal pl (palRestrict pr sr)
-- palRestrict (TensorPal pl pr) (TensorSlI (Sub sl) No) = palRestrict pl sl
-- palRestrict (TensorPal pl pr) (TensorSlI No (Sub sr)) = palRestrict pr sr
-- palRestrict (TensorPal pl pr) (TensorSlI (Sub sl) (Sub sr)) = TensorPal (palRestrict pl sl) (palRestrict pr sr)

-- -- The idea is, if `s2` is a slice of `palRestrict p s1`, then `sliceComp s1 s2` is a slice of `p`.
-- sliceComp :: SlI -> SlI -> SlI
-- sliceComp BotSlI s2 = BotSlI
-- sliceComp TopSlI s2 = s2
-- sliceComp (LeftCommaSlI s) s2 = LeftCommaSlI (sliceComp s s2)
-- sliceComp (RightCommaSlI s) s2 = RightCommaSlI (sliceComp s s2)
-- sliceComp (TensorSlI sl sr) (TensorSlI s2l s2r) = TensorSlI (choiceComp sl s2l) (choiceComp sr s2r)

-- choiceComp :: Choice SlI -> Choice SlI -> Choice SlI
-- choiceComp Yes No = No

-- colourRestrict :: ColI -> SlI -> Maybe ColI
-- -- colourRestrict c sl | traceShow (c, sl) False = undefined
-- colourRestrict c TopSlI = Just c
-- colourRestrict c BotSlI = Nothing
-- colourRestrict (LeftCommaColIx c) (LeftCommaSlI sl) = colourRestrict c sl
-- colourRestrict (RightCommaColIx c) (RightCommaSlI sl) = colourRestrict c sl
-- colourRestrict (LeftTensorColIx c) (TensorSlI sl BotSlI) = colourRestrict c sl
-- colourRestrict (LeftTensorColIx c) (TensorSlI BotSlI sr) = Nothing
-- colourRestrict (LeftTensorColIx c) (TensorSlI sl _) = LeftTensorColIx <$> colourRestrict c sl
-- colourRestrict (RightTensorColIx c) (TensorSlI sl BotSlI) = Nothing
-- colourRestrict (RightTensorColIx c) (TensorSlI BotSlI sr) = colourRestrict c sr
-- colourRestrict (RightTensorColIx c) (TensorSlI _ sr) = RightTensorColIx <$> colourRestrict c sr
-- colourRestrict _ _ = Nothing

-- FIXME: incomplete
validSplitOf :: SlI -> (SlI, SlI) -> Bool
validSplitOf OneSl (OneSl, OneSl) = True
validSplitOf TopSl (TensorSl Yes No, TensorSl No Yes) = True
validSplitOf TopSl (TensorSl No Yes, TensorSl Yes No) = True
validSplitOf (TensorSl l r) (TensorSl ll lr, TensorSl rl rr) = validTensorSplitOf l (ll, rl) && validTensorSplitOf r (lr, rr)
validSplitOf (CommaSl _ s) (CommaSl No l, CommaSl No r) = validCommaSplitOf s (l, r)
validSplitOf (CommaSl s _) (CommaSl l No, CommaSl r No) = validCommaSplitOf s (l, r)
validSplitOf s (l, r) = error $ "Unhandled " ++ show (s, (l, r))

validCommaSplitOf :: Choice SlI -> (Choice SlI, Choice SlI) -> Bool
validCommaSplitOf Yes (Sub l, Sub r) = validSplitOf TopSl (l, r)
validCommaSplitOf (Sub s) (Sub l, Sub r) = validSplitOf s (l, r)
validCommaSplitOf _ _ = False

validTensorSplitOf :: Choice SlI -> (Choice SlI, Choice SlI) -> Bool
validTensorSplitOf Yes (Yes, No) = True
validTensorSplitOf Yes (No, Yes) = True
validTensorSplitOf No (No, No) = True
validTensorSplitOf Yes (Sub l, Sub r) = validSplitOf TopSl (l, r)
validTensorSplitOf (Sub s) (Sub l, Sub r) = validSplitOf s (l, r)
validTensorSplitOf _ _ = False

data UnitI where
  HereUnitI :: UnitI
  LeftCommaUnitI :: UnitI -> UnitI
  RightCommaUnitI :: UnitI -> UnitI
  LeftTensorUnitI :: UnitI -> UnitI
  RightTensorUnitI :: UnitI -> UnitI

  deriving (Show, Eq)

data SlL = SlL Int SlI | SlEmpty
  deriving (Show, Eq)
data UnitL = UnitL Int UnitI
  deriving (Show, Eq)

-- data SlL where
--   UpSlL :: SlL -> SlL

--   BotSlL :: SlL
--   HereSlL :: SlL

--   LeftCommaSlL :: SlL -> SlL
--   RightCommaSlL :: SlL -> SlL
--   TensorSlL :: SlL -> SlL -> SlL
--   deriving (Show, Eq)

-- data UnitL where
--   UpUnitL :: UnitL -> UnitL

--   BotUnitL :: UnitL

--   HereUnitL :: UnitL
--   LeftCommaUnitL :: UnitL -> UnitL
--   RightCommaUnitL :: UnitL -> UnitL
--   LeftTensorUnitL :: UnitL -> UnitL
--   RightTensorUnitL :: UnitL -> UnitL

--   deriving (Show, Eq)

data SemPal where
  OriginSemPal :: SemPal
  OneSemPal :: SemPal
  CommaSemPal :: SemPal -> SemPal -> SemPal
  UnitSemPal :: UnitL -> SemPal
  TensorSemPal :: SlL -> SemPal -> SlL ->  SemPal -> SemPal
  deriving (Eq, Show)

palToSemPal :: Palette -> SemPal
palToSemPal = undefined

instance Semigroup SlL where
instance Monoid SlL where

-- cleverCommaSemPal :: SemPal -> SemPal -> SemPal
-- -- Note: We don't want to cancel the origin one
-- cleverCommaSemPal OneSemPal p = p
-- cleverCommaSemPal p OneSemPal = p
-- cleverCommaSemPal p q = CommaSemPal p q

semPalTopSlice :: SemPal -> SlL
semPalTopSlice pal = SlL (go pal) TopSl
  where go OriginSemPal = 0
        go (CommaSemPal l _) = 1 + go l
        go (TensorSemPal _ l _ _) = 1 + go l

lookupSlice :: SemPal -> SlI -> SlL
-- lookupSlice pal TopSlI = semEnvTopSlice pal
lookupSlice pal TopSl = semPalTopSlice pal
lookupSlice pal OneSl = SlL 0 OneSl
-- lookupSlice (CommaSemPal l _) (LeftCommaSl s) = lookupSlice l s
-- lookupSlice (CommaSemPal _ r) (RightCommaSl s) = lookupSlice r s
lookupSlice (CommaSemPal l _) (CommaSl (Sub s) No) = lookupSlice l s
lookupSlice (CommaSemPal _ r) (CommaSl No (Sub s)) = lookupSlice r s -- FIXME: Is this enough?
lookupSlice (TensorSemPal sl l sr r) (TensorSl l' r') = (lookupSliceChoice sl l l') <> (lookupSliceChoice sr r r')

lookupSliceChoice :: SlL -> SemPal -> Choice SlI -> SlL
lookupSliceChoice s pal Yes = s
lookupSliceChoice s pal No = SlEmpty
lookupSliceChoice _ pal (Sub s') = lookupSlice pal s'

sliceIxToLvl :: Palette -> SlI -> SlL
sliceIxToLvl = undefined

sliceLvlToIx :: Palette -> SlL -> SlI
sliceLvlToIx = undefined
