module Palette where

data Palette where
  CommaPal :: Palette -> Palette -> Palette
  OnePal :: Palette
  OriginPal :: Palette
  TensorPal :: Palette -> Palette -> Palette
  UnitPal :: Palette
  deriving (Show, Eq)

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

-- FIXME: incomplete
validSplitOf :: SlI -> (SlI, SlI) -> Bool
validSplitOf OneSl (OneSl, OneSl) = True
validSplitOf TopSl (TensorSl ll lr, TensorSl rl rr) = validTensorSplitOf Yes (ll, rl) && validTensorSplitOf Yes (lr, rr)
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
validTensorSplitOf (Sub s) (No, Sub r) = weakenableTo r s
validTensorSplitOf (Sub s) (Sub l, No) = weakenableTo l s
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

semPalDepth :: SemPal -> Int
semPalDepth OriginSemPal = 0
semPalDepth (CommaSemPal l _) = 1 + semPalDepth l
semPalDepth (TensorSemPal _ l _ _) = 1 + semPalDepth l

semPalTopSlice :: SemPal -> SlL
semPalTopSlice pal = SlL (semPalDepth pal) TopSl

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
