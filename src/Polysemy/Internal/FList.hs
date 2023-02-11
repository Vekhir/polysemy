{-# LANGUAGE BangPatterns, MagicHash, UnboxedSums #-}
module Polysemy.Internal.FList where

import Data.Foldable
import Data.Primitive.Array
import Data.Primitive.SmallArray
import GHC.Exts (Int(..), Int#, SmallArray#, Array#)

data SmallVector a = SmallVector {
    array :: {-# UNPACK #-} !(SmallArray a),
    svStart :: {-# UNPACK #-} !Int,
    svLen :: {-# UNPACK #-} !Int
  }

instance Functor SmallVector where
  fmap f = imapSV (\_ -> f)
  {-# INLINE fmap #-}

-- newtype MultiVector' a = MultiVector' (# (# SmallArray# a | Array# a #), Int#, Int# #)

-- data MultiVector a = MultiVector (# (# #) | a | MultiVector' a #)

-- lenMV :: MultiVector a -> Int
-- lenMV (MultiVector (# _ || #)) = 0
-- lenMV (MultiVector (# | _ | #)) = 1
-- lenMV (MultiVector (# || MultiVector' (# _, _, i #) #)) = Int# i

-- infixr 5 `consMV`
-- consSV :: a -> SmallVector a -> SmallVector a
-- consSV a (MultiVector (# _ || #)) = MultiVector (# | a | #)
-- consSV a (MultiVector (# | b | #)) =
--   let
--     !(SmallArray arr) = createSmallArray 2 b $ \sm -> writeSmallArray 0 a
--   in
--     MultiVector (# || MultiVector' (# arr, 0#, 2# #) #)
-- consSV a (MultiVector (# || MultiVector' (# arr, 0) #)) =
-- MultiVector (# | | #)
-- consSV a (SmallVector arr arrS arrL) =
--   let
--     arrL' = arrL + 1
--     arr' = createSmallArray arrL' a $ \sm ->
--       copySmallArray sm 1 arr arrS arrL
--   in
--     SmallVector arr' 0 arrL'
-- {-# INLINE consSV #-}

-- generateSV :: Int -> (Int -> a) -> SmallVector a
-- generateSV n f =
--   let
--     arr = createSmallArray n (errorWithoutStackTrace "impossible")
--       \ma -> forM_ [0..n-1] $ \i -> writeSmallArray ma i $! f i
--   in
--     SmallVector arr 0 n
-- {-# INLINE generateSV #-}

-- updateSV :: Int -> a -> SmallVector a -> SmallVector a
-- updateSV i a (SmallVector arr arrS arrL) =
--   let
--     arr' = runSmallArray $ do
--       mv <- thawSmallArray arr arrS arrL
--       writeSmallArray mv i a
--       return mv
--   in
--     SmallVector arr' 0 arrL
-- {-# INLINE updateSV #-}

-- indexSV :: SmallVector a -> Int -> a
-- indexSV (SmallVector arr arrS _) i = indexSmallArray arr (arrS + i)
-- {-# INLINE indexSV #-}

-- emptySV :: SmallVector a
-- emptySV = SmallVector emptySmallArray 0 0
-- {-# INLINE emptySV #-}

-- concatSV :: SmallVector a -> SmallVector a -> SmallVector a
-- concatSV (SmallVector arrL arrSL arrLL) (SmallVector arrR arrSR arrLR) =
--   let
--     arrL' = arrLL + arrLR
--     arr = createSmallArray arrL' (errorWithoutStackTrace "impossible") $ \ma -> do
--       copySmallArray ma 0 arrL arrSL arrLL
--       copySmallArray ma arrLL arrR arrSR arrLR
--   in
--     SmallVector arr 0 arrL'
-- {-# INLINE concatSV #-}

-- splitSV :: Int -> SmallVector a -> (SmallVector a, SmallVector a)
-- splitSV i (SmallVector arr arrS arrL) =
--   let
--     !arrL' = arrL - i
--     !arrS' = arrS + i
--   in
--     (SmallVector arr arrS i, SmallVector arr arrS' arrL')
-- {-# INLINE splitSV #-}

-- takeSV :: Int -> SmallVector a -> SmallVector a
-- takeSV i (SmallVector arr arrS _) = SmallVector arr arrS i
-- {-# INLINE takeSV #-}

-- dropSV :: Int -> SmallVector a -> SmallVector a
-- dropSV i (SmallVector arr arrS arrL) = SmallVector arr (arrS + i) (arrL - i)
-- {-# INLINE dropSV #-}

-- dropEndSV :: Int -> SmallVector a -> SmallVector a
-- dropEndSV i (SmallVector arr arrS arrL) = SmallVector arr arrS (arrL - i)
-- {-# INLINE dropEndSV #-}

-- data SmallVector' a = SmNone | One a | Many {-# UNPACK #-} !(SmallVector a)

infixr 5 `consSV`
consSV :: a -> SmallVector a -> SmallVector a
consSV a (SmallVector arr arrS arrL) =
  let
    arrL' = arrL + 1
    arr' = createSmallArray arrL' a $ \sm ->
      copySmallArray sm 1 arr arrS arrL
  in
    SmallVector arr' 0 arrL'
-- {-# INLINE consSV #-}

unconsSV :: SmallVector a -> (a, SmallVector a)
unconsSV (SmallVector arr arrS arrL) =
  let
    !x = indexSmallArray arr arrS
    !sv = SmallVector arr (arrS + 1) (arrL - 1)
  in
    (x, sv)
-- {-# INLINE unconsSV #-}

generateSV :: Int -> (Int -> a) -> SmallVector a
generateSV n f =
  let
    arr = createSmallArray n (errorWithoutStackTrace "impossible")
      \ma -> for_ [0..n-1] $ \i -> writeSmallArray ma i $! f i
  in
    SmallVector arr 0 n
-- {-# INLINE generateSV #-}

updateSV :: Int -> a -> SmallVector a -> SmallVector a
updateSV i a (SmallVector arr arrS arrL) =
  let
    arr' = runSmallArray $ do
      mv <- thawSmallArray arr arrS arrL
      writeSmallArray mv i a
      return mv
  in
    SmallVector arr' 0 arrL
-- {-# INLINE updateSV #-}

indexSV :: SmallVector a -> Int -> a
indexSV (SmallVector arr arrS _) i = indexSmallArray arr (arrS + i)
-- {-# INLINE indexSV #-}

emptySV :: SmallVector a
emptySV = SmallVector emptySmallArray 0 0
-- {-# INLINE emptySV #-}

concatSV :: SmallVector a -> SmallVector a -> SmallVector a
concatSV (SmallVector arrL arrSL arrLL) (SmallVector arrR arrSR arrLR) =
  let
    arrL' = arrLL + arrLR
    arr = createSmallArray arrL' (errorWithoutStackTrace "impossible") $ \ma -> do
      copySmallArray ma 0 arrL arrSL arrLL
      copySmallArray ma arrLL arrR arrSR arrLR
  in
    SmallVector arr 0 arrL'
-- {-# INLINE concatSV #-}

splitSV :: Int -> SmallVector a -> (SmallVector a, SmallVector a)
splitSV i (SmallVector arr arrS arrL) =
  let
    !arrL' = arrL - i
    !arrS' = arrS + i
  in
    (SmallVector arr arrS i, SmallVector arr arrS' arrL')
-- {-# INLINE splitSV #-}

takeSV :: Int -> SmallVector a -> SmallVector a
takeSV i (SmallVector arr arrS _) = SmallVector arr arrS i
-- {-# INLINE takeSV #-}

dropSV :: Int -> SmallVector a -> SmallVector a
dropSV i (SmallVector arr arrS arrL) = SmallVector arr (arrS + i) (arrL - i)
-- {-# INLINE dropSV #-}

dropEndSV :: Int -> SmallVector a -> SmallVector a
dropEndSV i (SmallVector arr arrS arrL) = SmallVector arr arrS (arrL - i)
-- {-# INLINE dropEndSV #-}

imapSV :: (Int -> a -> b) -> SmallVector a -> SmallVector b
imapSV f (SmallVector arr arrS arrL) =
    let
      arr' = createSmallArray arrL (errorWithoutStackTrace "impossible") $ \ma ->
        for_ [0..arrL-1] $ \i -> do
          writeSmallArray ma i $! f i $! indexSmallArray arr (arrS + i)
    in
      SmallVector arr' 0 arrL
-- {-# INLINE imapSV #-}

data FList a = FList {
    flistOps :: {-# UNPACK #-} !Int,
    flistLen :: {-# UNPACK #-} !Int,
    flistF :: Int -> a
  }

instance Functor FList where
  fmap g (FList ops n f) = FList ops n (g . f)
  {-# INLINE fmap #-}

memoizeFList :: FList a -> FList a
memoizeFList (FList _ n f) =
  if
    n > 256
  then
    let !v = createArray n (errorWithoutStackTrace "impossible") $ \ma ->
          for_ [0..n-1] $ \i -> writeArray ma i $! f i
    in FList 0 n (indexArray v)
  else
    let !v = createSmallArray n (errorWithoutStackTrace "impossible") $ \ma ->
          for_ [0..n-1] $ \i -> writeSmallArray ma i $! f i
    in FList 0 n (indexSmallArray v)
-- {-# INLINE memoizeFList #-}

memoizeFListCond :: FList a -> FList a
memoizeFListCond fl@(FList ops n _)
  | ops > 20 && (2 * ops > 3 * n + 15 || ops > 1000) = memoizeFList fl
  | otherwise = fl
-- {-# INLINE memoizeFListCond #-}

infixr 5 `consFL`
consFL :: a -> FList a -> FList a
consFL h (FList ops n f) = FList (ops + 1) (n + 1) \case
  0 -> h
  i -> f (i - 1)
-- {-# INLINE consFL #-}

headFL :: FList a -> a
headFL (FList _ _ f) = f 0
-- {-# INLINE headFL #-}

unconsFL :: FList a -> (a, FList a)
unconsFL (FList ops n f) =
  let
    !x = f 0
    !fl = memoizeFListCond $ FList (ops + 1) (n - 1) (f . (+1))
  in
    (x, fl)
-- {-# INLINE unconsFL #-}

infixr 5 `concatFL`
concatFL :: FList a -> FList a -> FList a
concatFL (FList opsl n f) (FList opsr m g) =
  memoizeFListCond $ FList (max opsl opsr + 1) (n + m) \i ->
    if i < n then f i else g (i - n)
-- {-# INLINE concatFL #-}

indexFL :: FList a -> Int -> a
indexFL (FList _ _ f) i = f i
-- {-# INLINE indexFL #-}

emptyFL :: FList a
emptyFL = FList 0 0 (\_ -> errorWithoutStackTrace "end of FList")
-- {-# INLINE emptyFL #-}

updateFL :: Int -> a -> FList a -> FList a
updateFL i a (FList ops n f) = memoizeFListCond $ FList (ops + 1) n \i' ->
  if i' == i then a else f i'
-- {-# INLINE updateFL #-}

imapFL :: (Int -> a -> b) -> FList a -> FList b
imapFL g (FList ops n f) = FList ops n \i -> g i (f i)
-- {-# INLINE imapFL #-}

splitFL :: Int -> FList a -> (FList a, FList a)
splitFL i (FList ops n f) =
  let
    !l = FList (max 0 (ops - (n - i))) i f
    !r = memoizeFListCond $ FList (ops + 1) (n - i) (f . (+ i))
  in
    (l, r)
-- {-# INLINE splitFL #-}

takeFL :: Int -> FList a -> FList a
takeFL i (FList ops n f) = FList (max 0 (ops - (n - i))) i f
-- {-# INLINE takeFL #-}

dropFL :: Int -> FList a -> FList a
dropFL i (FList ops n f) = memoizeFListCond $ FList (ops + 1) (n - i) (f . (+ i))
-- {-# INLINE dropFL #-}

dropEndFL :: Int -> FList a -> FList a
dropEndFL i (FList ops n f) = FList (max 0 (ops - i)) (n - i) f
-- {-# INLINE dropEndFL #-}

data Hybrid a = Hybrid {-# UNPACK #-} !(SmallVector a) {-# UNPACK #-} !(FList a)

fromFList :: FList a -> Hybrid a
fromFList = Hybrid emptySV
-- {-# INLINE fromFList #-}

fromSmallVector :: SmallVector a -> Hybrid a
fromSmallVector sv = Hybrid sv emptyFL
-- {-# INLINE fromSmallVector #-}

collapseHY :: Hybrid a -> FList a
collapseHY (Hybrid (SmallVector _ _ 0) fl) = fl
collapseHY (Hybrid (SmallVector arr arrS arrL) (FList ops n f)) =
  FList (ops + 1) (arrL + n) \i ->
    if i < arrL then
      indexSmallArray arr (arrS + i)
    else
      f (i - arrL)
-- {-# INLINE collapseHY #-}

collapseHY' :: Hybrid a -> SmallVector a
collapseHY' (Hybrid sv (FList _ 0 _)) = sv
collapseHY' (Hybrid (SmallVector arr arrS arrL) (FList _ n f)) =
  let
    arrL' = arrL + n
    arr' = createSmallArray arrL' (errorWithoutStackTrace "impossible") $ \ma ->
      do
        copySmallArray ma 0 arr arrS arrL
        for_ [0..n-1] $ \i ->
          writeSmallArray ma (arrL + i) $! f i
  in
    SmallVector arr' 0 arrL'
-- {-# INLINE collapseHY' #-}


infixr 5 `consHY`
consHY :: a -> Hybrid a -> Hybrid a
consHY a (Hybrid sv fl) = Hybrid (consSV a sv) fl
-- {-# INLINE consHY #-}

instance Functor Hybrid where
  fmap f = fromFList . fmap f . collapseHY
  {-# INLINE fmap #-}

imapHY :: (Int -> a -> b) -> Hybrid a -> Hybrid b
imapHY f = fromFList . imapFL f . collapseHY
-- {-# INLINE imapHY #-}

indexHY :: Hybrid a -> Int -> a
indexHY (Hybrid (SmallVector arr arrS arrL) (FList _ _ f)) i
  | i < arrL  = indexSmallArray arr (arrS + i)
  | otherwise = f (i - arrL)
-- {-# INLINE indexHY #-}

unconsHY :: Hybrid a -> (a, Hybrid a)
unconsHY (Hybrid (SmallVector _ _ 0) fl) =
  let
    !(x, y) = unconsFL fl
    !h = fromFList y
  in
    (x, h)
unconsHY (Hybrid (SmallVector arr arrS 1) fl) =
  let
    !x = indexSmallArray arr arrS
  in
    (x, fromFList fl)
unconsHY (Hybrid (SmallVector arr arrS arrL) fl) =
  let
    !x = indexSmallArray arr arrS
    !hy = Hybrid (SmallVector arr (arrS + 1) (arrL - 1)) fl
  in
    (x, hy)
-- {-# INLINE unconsHY #-}

infixr 5 `concatHY`
concatHY :: Hybrid a -> Hybrid a -> Hybrid a
concatHY (Hybrid sv (FList _ 0 _)) (Hybrid sv' fl')
  = Hybrid (concatSV sv sv') fl'
concatHY (Hybrid sv fl) hyR
  = Hybrid sv (concatFL fl (collapseHY hyR))
-- {-# INLINE concatHY #-}

updateHY :: Int -> a -> Hybrid a -> Hybrid a
updateHY i a (Hybrid sv@(SmallVector _ _ arrL) fl)
  | i < arrL  = Hybrid (updateSV i a sv) fl
  | otherwise = Hybrid sv (updateFL (i - arrL) a fl)
-- {-# INLINE updateHY #-}

splitHY :: Int -> Hybrid a -> (Hybrid a, Hybrid a)
splitHY i (Hybrid sv@(SmallVector _ _ arrL) fl) = case compare i arrL of
  EQ -> (Hybrid sv emptyFL, Hybrid emptySV fl)
  LT ->
    let
      !(l, r) = splitSV i sv
    in
      (Hybrid l emptyFL, Hybrid r fl)
  GT ->
    let
      !(l, r) = splitFL (i - arrL) fl
    in
      (Hybrid sv l, Hybrid emptySV r)
-- {-# INLINE splitHY #-}

takeHY :: Int -> Hybrid a -> Hybrid a
takeHY i (Hybrid sv@(SmallVector _ _ arrL) fl) = case compare i arrL of
  EQ -> Hybrid sv emptyFL
  LT -> Hybrid (takeSV i sv) emptyFL
  GT -> Hybrid sv (takeFL (i - arrL) fl)
-- {-# INLINE takeHY #-}

dropHY :: Int -> Hybrid a -> Hybrid a
dropHY i (Hybrid sv@(SmallVector _ _ arrL) fl) = case compare i arrL of
  EQ -> Hybrid emptySV fl
  LT -> Hybrid (dropSV i sv) fl
  GT -> Hybrid emptySV (dropFL (i - arrL) fl)
-- {-# INLINE dropHY #-}

dropEndHY :: Int -> Hybrid a -> Hybrid a
dropEndHY i (Hybrid sv fl@(FList _ n _)) = case compare i n of
  EQ -> Hybrid sv emptyFL
  LT -> Hybrid sv (dropEndFL i fl)
  GT -> Hybrid (dropEndSV (i - n) sv) emptyFL
-- {-# INLINE dropEndHY #-}

generateHY :: Int -> (Int -> a) -> Hybrid a
generateHY n f = Hybrid (generateSV n f) emptyFL
-- {-# INLINE generateHY #-}

emptyHY :: Hybrid a
emptyHY = Hybrid emptySV emptyFL
-- {-# INLINE emptyHY #-}
