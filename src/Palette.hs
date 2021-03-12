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
  OneSl <> OneSl = OneSl
  -- FIXME: Cheating of course, we error if things don't line up.
  (CommaSl (Sub l) No) <> (CommaSl (Sub r) No) = CommaSl (Sub $ l <> r) No
  (CommaSl No (Sub l)) <> (CommaSl No (Sub r)) = CommaSl No (Sub $ l <> r)
  (TensorSl ll lr) <> (TensorSl rl rr) = TensorSl (ll <> rl) (lr <> rr)
  s <> SummonedUnitSl = s
  SummonedUnitSl <> s = s
  l <> r = error $ "Unhandled " ++ show (l, r)

slackSliceTensor :: SlI -> SlI -> SlI
slackSliceTensor OneSl s = s
slackSliceTensor s OneSl = s
slackSliceTensor s t = s <> t

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

validUnitOf :: SlI -> UnitI -> Bool
validUnitOf _ OneUnit = True
validUnitOf SummonedUnitSl SummonedUnit = True
validUnitOf IdSl HereUnit = True
validUnitOf (CommaSl No r) (LeftCommaUnit u) = False
validUnitOf (CommaSl (Sub l) r) (LeftCommaUnit u) = validUnitOf l u
validUnitOf (CommaSl l No) (RightCommaUnit u) = False
validUnitOf (CommaSl l (Sub r)) (RightCommaUnit u) = validUnitOf r u
validUnitOf (TensorSl l r) (TensorUnit u v) = tensorValidUnitOf l u && tensorValidUnitOf r v
validUnitOf s u = error $ "Unhandled " ++ show (s, u)

tensorValidUnitOf :: Choice SlI -> Choice UnitI -> Bool
tensorValidUnitOf No No = True
tensorValidUnitOf (Sub s) (Sub u) = validUnitOf s u
tensorValidUnitOf _ _ = False

data UnitI where
  SummonedUnit :: UnitI
  HereUnit :: UnitI
  OneUnit :: UnitI
  LeftCommaUnit :: UnitI -> UnitI
  RightCommaUnit :: UnitI -> UnitI
  TensorUnit :: Choice UnitI -> Choice UnitI -> UnitI
  deriving (Show, Eq)

instance Semigroup UnitI where
  OneUnit <> s = s
  s <> OneUnit = s
  (LeftCommaUnit l) <> (LeftCommaUnit r) = LeftCommaUnit (l <> r)
  (RightCommaUnit l) <> (RightCommaUnit r) = RightCommaUnit (l <> r)
  (TensorUnit ll lr) <> (TensorUnit rl rr) = TensorUnit (ll <> rl) (lr <> rr)

instance Monoid UnitI where
  mempty = OneUnit

-- What was this SlEmpty constructor for again?
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

instance Semigroup UnitL where
instance Monoid UnitL where

semPalDepth :: SemPal -> Int
semPalDepth OriginSemPal = 0
semPalDepth (CommaSemPal l _) = 1 + semPalDepth l
semPalDepth (TensorSemPal _ l _ _) = 1 + semPalDepth l

semPalIdSlice :: SemPal -> SlL
semPalIdSlice pal = SlL (semPalDepth pal) IdSl

lookupSlice :: SemPal -> SlI -> SlL
lookupSlice pal IdSl = semPalIdSlice pal
lookupSlice pal OneSl = SlL 0 OneSl
lookupSlice (CommaSemPal l _) (CommaSl (Sub s) No) = lookupSlice l s
lookupSlice (CommaSemPal _ r) (CommaSl No (Sub s)) = lookupSlice r s -- FIXME: Is this enough?
lookupSlice (TensorSemPal sl l sr r) (TensorSl l' r') = (lookupSliceChoice sl l l') <> (lookupSliceChoice sr r r')

lookupSliceChoice :: SlL -> SemPal -> Choice SlI -> SlL
lookupSliceChoice s pal No = SlEmpty
lookupSliceChoice s pal (Sub IdSl) = s
lookupSliceChoice _ pal (Sub s') = lookupSlice pal s'

lookupUnit :: SemPal -> UnitI -> UnitL
lookupUnit pal OneUnit = UnitL 0 OneUnit
lookupUnit (UnitSemPal u) HereUnit = u
lookupUnit (CommaSemPal l _) (LeftCommaUnit u) = lookupUnit l u
lookupUnit (CommaSemPal _ r) (RightCommaUnit u) = lookupUnit r u
lookupUnit (TensorSemPal _ l _ r) (TensorUnit (Sub l') (Sub r')) = lookupUnit l l' <> lookupUnit r r'
lookupUnit (TensorSemPal _ l _ r) (TensorUnit (Sub l') No) = lookupUnit l l'
lookupUnit (TensorSemPal _ l _ r) (TensorUnit No (Sub r')) = lookupUnit r r'

-- sliceIxToLvl :: Palette -> SlI -> SlL
-- sliceIxToLvl = undefined

-- sliceLvlToIx :: Palette -> SlL -> SlI
-- sliceLvlToIx = undefined
