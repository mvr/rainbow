module Palette where

data Palette where
  CommaPal :: Palette -> Palette -> Palette
  OnePal :: Palette
  OriginPal :: Palette
  TensorPal :: Palette -> Palette -> Palette
  UnitPal :: Palette
  deriving (Show, Eq)

data Choice a = No | Sub a
  deriving (Show, Eq, Functor)

instance Semigroup a => Semigroup (Choice a) where
  No <> No = No
  (Sub a) <> No = Sub a
  No <> (Sub a) = Sub a
  (Sub a) <> (Sub b) = Sub (a <> b)

data SlI where
  IdSl :: SlI
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
cellTo :: SlI -> SlI -> Bool
cellTo _ OneSl = True
cellTo IdSl IdSl = True
cellTo _ IdSl = False
cellTo IdSl (TensorSl l r) = cellTo (TensorSl (Sub IdSl) (Sub IdSl)) (TensorSl l r)
cellTo (TensorSl l1 r1) (TensorSl l2 r2) = tchoice l1 l2 && tchoice r1 r2
  where tchoice No No = True
        tchoice (Sub s1) (Sub s2) = cellTo s1 s2
        tchoice _ _ = False
cellTo IdSl (CommaSl l1 r1) = cellTo (CommaSl (Sub IdSl) (Sub IdSl)) (CommaSl l1 r1)
cellTo (CommaSl l1 r1) (CommaSl l2 r2) = commaCellTo l1 l2 && commaCellTo r1 r2
cellTo SummonedUnitSl SummonedUnitSl = True
cellTo l r = error $ "Unhandled " ++ show (l, r)

commaCellTo :: Choice SlI -> Choice SlI -> Bool
commaCellTo _ No = True
commaCellTo (Sub s1) (Sub s2) = cellTo s1 s2
commaCellTo _ _ = False

validSplitOf :: SlI -> (SlI, SlI) -> Bool
validSplitOf s (l, r) = cellTo s (l <> r)

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

semPalIdSlice :: SemPal -> SlL
semPalIdSlice pal = SlL (semPalDepth pal) IdSl

lookupSlice :: SemPal -> SlI -> SlL
-- lookupSlice pal IdSlI = semEnvIdSlice pal
lookupSlice pal IdSl = semPalIdSlice pal
lookupSlice pal OneSl = SlL 0 OneSl
-- lookupSlice (CommaSemPal l _) (LeftCommaSl s) = lookupSlice l s
-- lookupSlice (CommaSemPal _ r) (RightCommaSl s) = lookupSlice r s
lookupSlice (CommaSemPal l _) (CommaSl (Sub s) No) = lookupSlice l s
lookupSlice (CommaSemPal _ r) (CommaSl No (Sub s)) = lookupSlice r s -- FIXME: Is this enough?
lookupSlice (TensorSemPal sl l sr r) (TensorSl l' r') = (lookupSliceChoice sl l l') <> (lookupSliceChoice sr r r')

lookupSliceChoice :: SlL -> SemPal -> Choice SlI -> SlL
lookupSliceChoice s pal No = SlEmpty
lookupSliceChoice _ pal (Sub s') = lookupSlice pal s'

sliceIxToLvl :: Palette -> SlI -> SlL
sliceIxToLvl = undefined

sliceLvlToIx :: Palette -> SlL -> SlI
sliceLvlToIx = undefined
