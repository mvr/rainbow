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

data ColI where -- DeBruijn indices for colours
  TopColIx :: ColI
  LeftColIx :: ColI -- The colour exactly here on the left of a tensor.
  RightColIx :: ColI
  LeftCommaColIx :: ColI -> ColI
  RightCommaColIx :: ColI -> ColI
  LeftTensorColIx :: ColI -> ColI
  RightTensorColIx :: ColI -> ColI
  deriving (Show, Eq)

data Choice a = Yes | No | Sub a
  deriving (Show, Eq, Functor)

data SlI where
  TopSlI :: SlI
  BotSlI :: SlI
  LeftCommaSlI :: SlI -> SlI
  RightCommaSlI :: SlI -> SlI
  TensorSlI :: Choice SlI -> Choice SlI -> SlI

  deriving (Show, Eq)

-- cleverTensor :: SlI -> SlI -> SlI
-- cleverTensor BotSlI s = s
-- cleverTensor s BotSlI = s
-- cleverTensor sl sr = TensorSlI sl sr

-- instance Semigroup SlI where
--   (<>) = curry unionDisjointSlice

-- instance Monoid SlI where
--   mempty = BotSlice

colourToSlice :: ColI -> SlI
colourToSlice TopColIx       = TopSlI
colourToSlice LeftColIx      = TensorSlI Yes No
colourToSlice RightColIx      = TensorSlI No Yes
colourToSlice (LeftCommaColIx s) = LeftCommaSlI (colourToSlice s)
colourToSlice (RightCommaColIx s) = RightCommaSlI (colourToSlice s)
colourToSlice (LeftTensorColIx s)  = TensorSlI (Sub $ colourToSlice s) No
colourToSlice (RightTensorColIx s) = TensorSlI No (Sub $ colourToSlice s)

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

validSplitOf :: SlI -> (SlI, SlI) -> Bool
validSplitOf s (l, r) = undefined

data UnitIx where
  HereUnitIx :: UnitIx
  LeftCommaUnitIx :: UnitIx -> UnitIx
  RightCommaUnitIx :: UnitIx -> UnitIx
  LeftTensorUnitIx :: UnitIx -> UnitIx
  RightTensorUnitIx :: UnitIx -> UnitIx

  deriving (Show, Eq)

data SlL where
  UpSlL :: SlL -> SlL

  BotSlL :: SlL
  HereSlL :: SlL

  LeftCommaSlL :: SlL -> SlL
  RightCommaSlL :: SlL -> SlL
  TensorSlL :: SlL -> SlL -> SlL
  deriving (Show, Eq)

data UnitL where
  UpUnitL :: UnitL -> UnitL

  BotUnitL :: UnitL

  HereUnitL :: UnitL
  LeftCommaUnitL :: UnitL -> UnitL
  RightCommaUnitL :: UnitL -> UnitL
  LeftTensorUnitL :: UnitL -> UnitL
  RightTensorUnitL :: UnitL -> UnitL

  deriving (Show, Eq)

data SemPal where
  CommaSemPal :: SemPal -> SemPal -> SemPal
  OneSemPal :: SemPal
  OriginSemPal :: SemPal
  TensorSemPal :: SlL -> SemPal -> SlL ->  SemPal -> SemPal
  UnitSemPal :: UnitL -> SemPal
  deriving (Eq, Show)

-- cleverCommaSemPal :: SemPal -> SemPal -> SemPal
-- -- Note: We don't want to cancel the origin one
-- cleverCommaSemPal OneSemPal p = p
-- cleverCommaSemPal p OneSemPal = p
-- cleverCommaSemPal p q = CommaSemPal p q

semEnvTopSlice :: SemPal -> SlL
semEnvTopSlice (CommaSemPal l _) = UpSlL (semEnvTopSlice l)

lookupSlice :: SemPal -> SlI -> SlL
lookupSlice pal TopSlI = semEnvTopSlice pal

sliceIxToLvl :: Palette -> SlI -> SlL
sliceIxToLvl = undefined

sliceLvlToIx :: Palette -> SlL -> SlI
sliceLvlToIx = undefined
