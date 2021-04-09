module Palette where

import Control.Applicative (liftA2)

data Palette where
  CommaPal :: Palette -> Palette -> Palette
  OnePal :: Palette
  OriginPal :: Palette
  TensorPal :: Palette -> Palette -> Palette
  UnitPal :: Palette
  deriving (Show, Eq)

palDepth :: Palette -> Int
palDepth OriginPal = 0
palDepth OnePal = 0
palDepth (CommaPal l _) = 1 + palDepth l
palDepth (TensorPal l _) = 1 + palDepth l

palTopSlice :: Palette -> SlI
palTopSlice OnePal = IdSl
palTopSlice OriginPal = IdSl
palTopSlice (CommaPal l r) = CommaSl (Sub $ palTopSlice l) (Sub $ palTopSlice r)
palTopSlice (TensorPal l r) = TensorSl (Sub $ palTopSlice l) (Sub $ palTopSlice r)

palTopSliceLevel :: Palette -> SlL
palTopSliceLevel pal = SlL (palDepth pal) (palTopSlice pal)

-- This is just Maybe now...
data Choice a = No | Sub a
  deriving (Show, Eq, Functor)

instance Semigroup a => Semigroup (Choice a) where
  No <> No = No
  (Sub a) <> No = Sub a
  No <> (Sub a) = Sub a
  (Sub a) <> (Sub b) = Sub (a <> b)

instance Applicative Choice where
  pure = Sub

  (Sub f) <*> m = fmap f m
  No <*> _m = No

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

-- Used when guessing slices, but not in typechecking.
slackSliceTensor :: SlI -> SlI -> SlI
slackSliceTensor OneSl s = s
slackSliceTensor s OneSl = s
slackSliceTensor s t = s <> t

-- A comma version of the above
-- internalComma :: SlI -> SlI -> SlI
-- internalComma OneSl OneSl  = OneSl
-- internalComma (TensorSl (Sub l) No) (TensorSl (Sub r) No) = TensorSl (Sub $ l `internalComma` r) No
-- internalComma (TensorSl No (Sub l)) (TensorSl No (Sub r)) = TensorSl No (Sub $ l `internalComma` r)
-- internalComma (CommaSl ll lr) (CommaSl rl rr) = CommaSl (liftA2 internalComma ll rl) (liftA2 internalComma lr rr)

instance Monoid SlI where
  mempty = OneSl

-- FIXME: incomplete
cellTo :: SlI -> SlI -> Bool
cellTo _ OneSl = True
cellTo IdSl IdSl = True
cellTo (CommaSl l r) IdSl = cellTo (CommaSl l r) (CommaSl (Sub IdSl) (Sub IdSl))
cellTo (TensorSl l r) IdSl = cellTo (TensorSl l r) (TensorSl (Sub IdSl) (Sub IdSl))
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

-- FIXME: Should simplify?
sliceIndexToLevel :: Palette -> SlI -> SlL
sliceIndexToLevel pal s = SlL (palDepth pal) s

sliceLevelToIndex :: Palette -> SlL -> SlI
sliceLevelToIndex pal (SlL i s) = go pal (palDepth pal - i) s
  where go _ 0 s = s
        go (CommaPal l r) i s = CommaSl (Sub $ go l (i-1) s) No
        go (TensorPal l r) i s = TensorSl (Sub $ go l (i-1) s) No

-- sliceIndexNormalise :: Palette -> SlI -> SlI
-- sliceIndexNormalise pal (CommaSl (Sub s) (Sub t)) =
--   case (sliceIndexNormalise pal s, sliceIndexNormalise pal t) of
--     (IdSl, IdSl) -> IdSl
--     (s, t) -> CommaSl (Sub s) (Sub t)

-- sliceLevelNormalise :: Palette -> SlL -> SlL
-- sliceLevelNormalise pal (SlL i s) = go pal (palDepth pal - i) s
--   where go pal 0 s =

sliceEquivalent :: Palette -> SlL -> SlL -> Bool
sliceEquivalent _ l r = l == r

splitEquivalent :: Palette -> (SlL, SlL) -> (SlL, SlL) -> Bool
splitEquivalent pal (l1, r1) (l2, r2) = sliceEquivalent pal l1 l2 && sliceEquivalent pal r1 r2

data SemPal where
  OriginSemPal :: SemPal
  OneSemPal :: SemPal
  CommaSemPal :: SemPal -> SemPal -> SemPal
  UnitSemPal :: UnitL -> SemPal
  TensorSemPal :: SlL -> SemPal -> SlL ->  SemPal -> SemPal
  deriving (Eq, Show)

semPalToShape :: SemPal -> Palette
semPalToShape OriginSemPal = OnePal
semPalToShape OneSemPal = OnePal
semPalToShape (CommaSemPal p q) = CommaPal (semPalToShape p) (semPalToShape q)
semPalToShape (TensorSemPal _ p _ q) = TensorPal (semPalToShape p) (semPalToShape q)
semPalToShape (UnitSemPal u) = UnitPal

instance Semigroup SlL where
instance Monoid SlL where

instance Semigroup UnitL where
instance Monoid UnitL where

semPalDepth :: SemPal -> Int
semPalDepth OriginSemPal = 0
semPalDepth (CommaSemPal l _) = 1 + semPalDepth l
semPalDepth (TensorSemPal _ l _ _) = 1 + semPalDepth l



semPalTopRightSlice :: SemPal -> SlL
semPalTopRightSlice pal = SlL (semPalDepth pal) (TensorSl No (Sub IdSl))

slExtHom :: Palette -> SlL -> SlL
slExtHom = undefined

slExtMatch :: Palette -> SlL -> SlL
slExtMatch pal s = sliceIndexToLevel (CommaPal pal OnePal) $ CommaSl (Sub $ sliceLevelToIndex pal s) (Sub IdSl)

lookupSlice :: {- current slice -} SlL -> SemPal -> SlI -> SlL
lookupSlice d pal IdSl = d
lookupSlice d pal OneSl = SlL 0 OneSl
lookupSlice d (CommaSemPal l _) (CommaSl (Sub s) No) = lookupSlice d l s
lookupSlice d (CommaSemPal _ r) (CommaSl No (Sub s)) = lookupSlice d r s
lookupSlice d (CommaSemPal _ _) (CommaSl (Sub _) (Sub _)) = d -- We must be at the top level
lookupSlice d (TensorSemPal sl l sr r) (TensorSl (Sub l') (Sub r')) = (lookupSlice sl l l') <> (lookupSlice sr r r')
lookupSlice d (TensorSemPal sl l sr r) (TensorSl No (Sub r')) = lookupSlice sr r r'
lookupSlice d (TensorSemPal sl l sr r) (TensorSl (Sub l') No) = (lookupSlice sl l l')
lookupSlice d _ SummonedUnitSl = SlL 0 SummonedUnitSl

lookupUnit :: SemPal -> UnitI -> UnitL
lookupUnit pal OneUnit = UnitL 0 OneUnit
lookupUnit (UnitSemPal u) HereUnit = u
lookupUnit (CommaSemPal l _) (LeftCommaUnit u) = lookupUnit l u
lookupUnit (CommaSemPal _ r) (RightCommaUnit u) = lookupUnit r u
lookupUnit (TensorSemPal _ l _ r) (TensorUnit (Sub l') (Sub r')) = lookupUnit l l' <> lookupUnit r r'
lookupUnit (TensorSemPal _ l _ r) (TensorUnit (Sub l') No) = lookupUnit l l'
lookupUnit (TensorSemPal _ l _ r) (TensorUnit No (Sub r')) = lookupUnit r r'
lookupUnit _ SummonedUnit = UnitL 0 SummonedUnit
