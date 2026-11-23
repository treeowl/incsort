{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language ScopedTypeVariables #-}

-- for debugging
{-# language StandaloneDeriving #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{- OPTIONS_GHC -ddump-simpl #-}
module Basic (incSort) where

import Data.Sequence.Internal
  ( Seq (..)
  , FingerTree (..)
  , Node (..)
  , Digit (..)
  , Sized (..)
  , Elem (..)
  )
import qualified Data.Sequence as S
import System.Random
import Data.Sequence (index, splitAt)
import Prelude hiding (splitAt)
--import Debug.Trace
import Control.Exception (assert)
import Data.Foldable (foldr')
import qualified Data.List as L
import qualified Data.Foldable as F
import GHC.Exts (inline)

-- A tree of chunks annotated by total length. Every element in a chunk is
-- less than or equal to every element in the following chunks.
type Parted a = FingerTree (Chunk a)

data Chunk a = Chunk !Sortedness !(Seq a)
  deriving (Show)

data Sortedness = Unsorted | Sorted
  deriving (Show)

instance Sized (Chunk a) where
  size (Chunk _ s) = length s

-- Partition a sequence around a particular value, maintaining the ordering of
-- equal values.
partitionSeq :: Ord a => a -> Seq a -> StrictTriple (Seq a) (Seq a) (Seq a)
partitionSeq pivot input =
  case foldr' go (TripleS [] [] []) input of
    TripleS less same more -> TripleS (S.fromList less) (S.fromList same) (S.fromList more)
  where
    go a (TripleS less same more) = case compare a pivot of
      LT -> TripleS (a : less) same more
      EQ -> TripleS less (a : same) more
      GT -> TripleS less same (a : more)

incSort :: Ord a => StdGen -> Seq a -> Seq a
incSort !_g (Seq EmptyT) = S.empty
incSort !_g s@(Seq (Single _)) = s
incSort g s = Seq $ doSort (length s) 1 unpackSingleton g (Single (Chunk Unsorted s))
  where
    unpackSingleton _g (Single (Chunk _ (Seq (Single x)))) = x
    unpackSingleton _ _ = error "Parted is not a singleton at the leaf"

doSort :: forall a b. Ord a => Int -> Int -> (StdGen -> Parted a -> b) -> StdGen -> Parted a -> FingerTree b
-- This is awful. It would be nicer to use some sort of appropriate functor, I imagine.
doSort n !mSize m = case n of
    0 -> emptyTree
    1 -> \g p -> Single (m g p)
    2 -> deepA 1 one emptyTree 1 one
    3 -> deepA 2 two emptyTree 1 one
    4 -> deepA 2 two emptyTree 2 two
    5 -> deepA 3 three emptyTree 2 two
    6 -> deepA 3 three emptyTree 3 three
    _ -> case n `quotRem` 3 of
           (q,0) -> deepA 3 three (doSort (q - 2) mSize' n3) 3 three
           (q,1) -> deepA 2 two (doSort (q - 1) mSize' n3) 2 two
           (q,_) -> deepA 3 three (doSort (q - 1) mSize' n3) 2 two
      where !mSize' = 3 * mSize
            n3 g p = Node3 mSize' (m g1 left) (m g2 mid) (m g3 right)
              where
                (g1, g2, g3, left, mid, right) =
                  case divideParted g mSize p of { TripleS left rest g' ->
                  case divideParted g' mSize rest of { TripleS mid right g'' ->
                  case splitGen g'' of { (g1, g''') ->
                  case splitGen g''' of { (g2, g3) ->
                     (g1, g2, g3, left, mid, right) }}}}
  where
    deepA :: Int -> (StdGen -> Parted a -> Digit b) -> (StdGen -> Parted a -> FingerTree (Node b)) -> Int -> (StdGen -> Parted a -> Digit b) -> StdGen -> Parted a -> FingerTree b
    deepA prl prg mg sfl sfg g p =
      let (g1, g2, g3, left, mid, right) = deepSplitty prl sfl g p
      in Deep (n * mSize) (prg g1 left) (mg g2 mid) (sfg g3 right)

    -- If we inline this into deepA (which would be a much more natural way to
    -- write it), then deepA doesn't inline, which is mildly unfortunate.
    {-# NOINLINE deepSplitty #-}
    deepSplitty :: Int -> Int -> StdGen -> Parted a -> (StdGen, StdGen, StdGen, Parted a, Parted a, Parted a)
    deepSplitty prl sfl g p =
      case divideParted g (prl * mSize) p of { TripleS left rest g' ->
      case divideParted g' (mSize * (n - prl - sfl)) rest of { TripleS mid right g'' ->
      case splitGen g'' of { (g1, g''') ->
      case splitGen g''' of { (g2, g3) -> (g1, g2, g3, left, mid, right)
      }}}}

    one :: StdGen -> Parted a -> Digit b
    one g p = One (m g p)

    -- Apply the child builders outside the lazy split binding. This lets lookup
    -- read a child's cached size without forcing its input partition.
    two :: StdGen -> Parted a -> Digit b
    two g p = Two (m g1 p1) (m g2 p2)
      where
        (g1, g2, p1, p2) =
          case divideParted g mSize p of { (TripleS p1 p2 g') ->
          case splitGen g' of { (g1, g2) ->
            (g1, g2, p1, p2) }}

    three :: StdGen -> Parted a -> Digit b
    three g p = Three (m g1 p1) (m g2 p2) (m g3 p3)
      where
        (g1, g2, g3, p1, p2, p3) =
          case divideParted g mSize p of { TripleS p1 p' g' ->
          case divideParted g' mSize p' of { TripleS p2 p3 g'' ->
          case splitGen g'' of { (g1, g''') ->
          case splitGen g''' of { (g2, g3) ->
            (g1, g2, g3, p1, p2, p3) }}}}

    emptyTree _g _p = EmptyT


-- TODO: choose sample size cutoffs much more carefully. I suspect we'll want
-- to go up to 7-element samples at some size, and *possibly* even larger ones.
-- My intuition: the larger the sequence, the more expensive it is to choose a
-- "bad" pivot.
choosePivot :: Ord a => StdGen -> Seq a -> StrictPair a StdGen
choosePivot g s
  | length s < 100
  = case uniformR (0, length s - 1) g
      of
        (i, g') -> (s `index` i) :*: g'
  | length s < 1000
  = case uniformListR 3 (0, length s - 1) g
      of
        (candindices, g') -> (L.sort (fmap (s `index`) candindices) !! 1) :*: g'
  | otherwise
  = case uniformListR 5 (0, length s - 1) g
      of
        (candindices, g') -> (L.sort (fmap (s `index`) candindices) !! 2) :*: g'

infixr 5 <<|
infixl 5 |>>
(<<|) :: Chunk a -> Parted a -> Parted a
Chunk _ (Seq EmptyT) <<| p = p
s <<| p = s `consTree` p

(|>>) :: Parted a -> Chunk a -> Parted a
p |>> Chunk _ (Seq EmptyT) = p
p |>> s = p `snocTree` s

divideParted :: Ord a => StdGen -> Int -> Parted a -> StrictTriple (Parted a) (Parted a) StdGen
divideParted g !_i EmptyT = TripleS EmptyT EmptyT g
divideParted g i p = assert (i >= 0) $
  case splitTreeN i p of
    Split before during after
      | i == size before
      -> assert (size before + size (during `consTree` after) == size p) $
         assert (size before == i) $
         TripleS before (during `consTree` after) g
      | let i' = i - size before
      ->
        let
          res = divideParted' g i' before during after
          good (TripleS l r _) = size l == i && i + size r == size p
        in assert (good res) res

instance (Show a, b ~ Chunk a) => Show (FingerTree b) where
  -- This mapping is completely illegitimate, but it's okay because the Show instance
  -- doesn't care about size annotations.
  showsPrec i t = showsPrec i (Seq (fmap Elem t))


divideParted' :: Ord a => StdGen -> Int -> Parted a -> Chunk a -> Parted a -> StrictTriple (Parted a) (Parted a) StdGen
divideParted' g 0 before during after = TripleS before (during <<| after) g
divideParted' g i before during@(Chunk sortedness s) after
  | i == length s = TripleS (before |>> during) after g
  | Sorted <- sortedness = case splitAt i s of
      (left, right) -> TripleS (before |>> Chunk Sorted left) (Chunk Sorted right <<| after) g
  | otherwise = case choosePivot g s of
      pivot :*: g' -> case partitionSeq pivot s of
        TripleS less same more
          | i < length less
          -> divideParted' g' i before (Chunk Unsorted less) (Chunk Sorted same <<| Chunk Unsorted more <<| after)
          | let i' = i - length less
          , i' < length same
          -> divideParted' g' i' (before |>> Chunk Unsorted less) (Chunk Sorted same) (Chunk Unsorted more <<| after)
          | let i' = i - length less - length same
          -> divideParted' g' i' (before |>> Chunk Unsorted less |>> Chunk Sorted same) (Chunk Unsorted more) after


-- CAUTION: Split should only be used for *data* like Node or Seq, not for
-- Elem. Otherwise, it will force things illegitimately.
data Split a = Split !(FingerTree a) !a !(FingerTree a)
data StrictPair a b = !a :*: !b
  deriving (Show)

infixr 1 :*:

deriving instance (Show a, b ~ Chunk a) => Show (Split b)

data StrictTriple a b c = TripleS !a !b !c
  deriving (Show)

forceSpineTree :: FingerTree a -> ()
forceSpineTree (Deep _n _pr m _sf) = forceSpineTree m
forceSpineTree _ = ()

forceSpine :: Seq a -> ()
forceSpine (Seq t) = forceSpineTree t

class Valid a where
    valid :: a -> Bool
       
instance Valid (Elem a) where
    valid _ = True
       
instance Valid (Seq a) where
    valid (Seq xs) = valid xs
       
instance (Sized a, Valid a) => Valid (FingerTree a) where
    valid EmptyT = True
    valid (Single x) = valid x
    valid (Deep s pr m sf) =
        s == size pr + size m + size sf && valid pr && valid m && valid sf
       
instance (Sized a, Valid a) => Valid (Node a) where
    valid node = size node == sum (fmap size node) && all valid node
       
instance Valid a => Valid (Digit a) where
    valid = all valid 



-- WARNING: This function forces the item being split around. Normally, it should
-- not be used to split around an Elem.
{-# SPECIALIZE splitTreeN :: Int -> FingerTree (Node a) -> Split (Node a) #-}
{-# SPECIALIZE splitTreeN :: Int -> FingerTree (Chunk a) -> Split (Chunk a) #-}
splitTreeN :: Sized a => Int -> FingerTree a -> Split a
splitTreeN !_i EmptyT = error "splitTreeN of empty tree"
splitTreeN _i (Single x) = Split EmptyT x EmptyT
splitTreeN i (Deep s pr m sf)
  | i < spr     = splitPrefixN i s pr m sf
  | i < spm     = case splitTreeN im m of
            Split ml xs mr -> splitMiddleN (im - size ml) s spr pr ml xs mr sf
  | otherwise   = splitSuffixN (i - spm) s pr m sf  where
    spr     = size pr
    spm     = spr + size m
    im      = i - spr

{-# SPECIALIZE
   splitMiddleN ::  Int -> Int -> Int
             -> Digit (Node a) -> FingerTree (Node (Node a)) -> Node (Node a) -> FingerTree (Node (Node a)) -> Digit (Node a)
             -> Split (Node a) #-}
splitMiddleN :: Sized a => Int -> Int -> Int
             -> Digit a -> FingerTree (Node a) -> Node a -> FingerTree (Node a) -> Digit a
             -> Split a
splitMiddleN i s spr pr ml (Node2 _ a b) mr sf
  | i < sa      = Split (pullR sprml pr ml) a (Deep (s - sprmla) (One b) mr sf)
  | otherwise   = Split (Deep sprmla pr ml (One a)) b (pullL (s - sprmla - size b) mr sf)
  where
    sa      = size a
    sprml   = spr + size ml
    sprmla  = sa + sprml
splitMiddleN i s spr pr ml (Node3 _ a b c) mr sf
  | i < sa      = Split (pullR sprml pr ml) a (Deep (s - sprmla) (Two b c) mr sf)
  | i < sab     = Split (Deep sprmla pr ml (One a)) b (Deep (s - sprmlab) (One c) mr sf)
  | otherwise   = Split (Deep sprmlab pr ml (Two a b)) c (pullL (s - sprmlab - size c) mr sf)
  where
    sa      = size a
    sab     = sa + size b
    sprml   = spr + size ml
    sprmla  = sa + sprml
    sprmlab = sprmla + size b

{-# SPECIALIZE
  splitPrefixN :: Int -> Int -> Digit (Node a) -> FingerTree (Node (Node a)) -> Digit (Node a) ->
     Split (Node a) #-}
splitPrefixN :: Sized a =>  Int -> Int -> Digit a -> FingerTree (Node a) -> Digit a ->
                    Split a
splitPrefixN !_i !s (One a) m sf = Split EmptyT a (pullL (s - size a) m sf)
splitPrefixN i s (Two a b) m sf
  | i < sa      = Split EmptyT a (Deep (s - sa) (One b) m sf)
  | otherwise   = Split (Single a) b (pullL (s - sa - size b) m sf)
  where
    sa      = size a
splitPrefixN i s (Three a b c) m sf
  | i < sa      = Split EmptyT a (Deep (s - sa) (Two b c) m sf)
  | i < sab     = Split (Single a) b (Deep (s - sab) (One c) m sf)
  | otherwise   = Split (Deep sab (One a) EmptyT (One b)) c (pullL (s - sab - size c) m sf)
  where
    sa      = size a
    sab     = sa + size b
splitPrefixN i s (Four a b c d) m sf
  | i < sa      = Split EmptyT a $ Deep (s - sa) (Three b c d) m sf
  | i < sab     = Split (Single a) b $ Deep (s - sab) (Two c d) m sf
  | i < sabc    = Split (Deep sab (One a) EmptyT (One b)) c $ Deep (s - sabc) (One d) m sf
  | otherwise   = Split (Deep sabc (Two a b) EmptyT (One c)) d $ pullL (s - sabc - size d) m sf
  where
    sa      = size a
    sab     = sa + size b
    sabc    = sab + size c

{-# SPECIALIZE
  splitSuffixN :: Int -> Int -> Digit (Node a) -> FingerTree (Node (Node a)) -> Digit (Node a) ->
     Split (Node a) #-}
splitSuffixN :: Sized a => Int -> Int -> Digit a -> FingerTree (Node a) -> Digit a ->
   Split a
splitSuffixN !_i !s pr m (One a) = Split (pullR (s - size a) pr m) a EmptyT
splitSuffixN i s pr m (Two a b)
  | i < sa      = Split (pullR (s - sa - size b) pr m) a (Single b)
  | otherwise   = Split (Deep (s - size b) pr m (One a)) b EmptyT
  where
    sa      = size a
splitSuffixN i s pr m (Three a b c)
  | i < sa      = Split (pullR (s - sab - size c) pr m) a (deep (One b) EmptyT (One c))
  | i < sab     = Split (Deep (s - size b - size c) pr m (One a)) b (Single c)
  | otherwise   = Split (Deep (s - size c) pr m (Two a b)) c EmptyT
  where
    sa      = size a
    sab     = sa + size b
splitSuffixN i s pr m (Four a b c d)
  | i < sa      = Split (pullR (s - sa - sbcd) pr m) a (Deep sbcd (Two b c) EmptyT (One d))
  | i < sab     = Split (Deep (s - sbcd) pr m (One a)) b (Deep scd (One c) EmptyT (One d))
  | i < sabc    = Split (Deep (s - scd) pr m (Two a b)) c (Single d)
  | otherwise   = Split (Deep (s - sd) pr m (Three a b c)) d EmptyT
  where
    sa      = size a
    sab     = sa + size b
    sabc    = sab + size c
    sd      = size d
    scd     = size c + sd
    sbcd    = size b + scd




nodeToDigit :: Node a -> Digit a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c

-- | Given the size of a digit and the digit itself, efficiently converts
-- it to a FingerTree.
digitToTree' :: Int -> Digit a -> FingerTree a
digitToTree' n (Four a b c d) = Deep n (Two a b) EmptyT (Two c d)
digitToTree' n (Three a b c) = Deep n (Two a b) EmptyT (One c)
digitToTree' n (Two a b) = Deep n (One a) EmptyT (One b)
digitToTree' !_n (One a) = Single a

{-# INLINE pullL #-}
pullL :: Int -> FingerTree (Node a) -> Digit a -> FingerTree a
pullL s m sf = case viewLTree m of
    EmptyLTree          -> digitToTree' s sf
    ConsLTree pr m'     -> Deep s (nodeToDigit pr) m' sf

{-# INLINE pullR #-}
pullR :: Int -> Digit a -> FingerTree (Node a) -> FingerTree a
pullR s pr m = case viewRTree m of
    EmptyRTree          -> digitToTree' s pr
    SnocRTree m' sf     -> Deep s pr m' (nodeToDigit sf)

data ViewLTree a = ConsLTree a (FingerTree a) | EmptyLTree
data ViewRTree a = SnocRTree (FingerTree a) a | EmptyRTree

{-# SPECIALIZE viewLTree :: FingerTree (Elem a) -> ViewLTree (Elem a) #-}
{-# SPECIALIZE viewLTree :: FingerTree (Node a) -> ViewLTree (Node a) #-}
viewLTree       :: Sized a => FingerTree a -> ViewLTree a
viewLTree EmptyT                = EmptyLTree
viewLTree (Single a)            = ConsLTree a EmptyT
viewLTree (Deep s (One a) m sf) = ConsLTree a (pullL (s - size a) m sf)
viewLTree (Deep s (Two a b) m sf) =
    ConsLTree a (Deep (s - size a) (One b) m sf)
viewLTree (Deep s (Three a b c) m sf) =
    ConsLTree a (Deep (s - size a) (Two b c) m sf)
viewLTree (Deep s (Four a b c d) m sf) =
    ConsLTree a (Deep (s - size a) (Three b c d) m sf)

{-# SPECIALIZE viewRTree :: FingerTree (Elem a) -> ViewRTree (Elem a) #-}
{-# SPECIALIZE viewRTree :: FingerTree (Node a) -> ViewRTree (Node a) #-}
viewRTree       :: Sized a => FingerTree a -> ViewRTree a
viewRTree EmptyT                = EmptyRTree
viewRTree (Single z)            = SnocRTree EmptyT z
viewRTree (Deep s pr m (One z)) = SnocRTree (pullR (s - size z) pr m) z
viewRTree (Deep s pr m (Two y z)) =
    SnocRTree (Deep (s - size z) pr m (One y)) z
viewRTree (Deep s pr m (Three x y z)) =
    SnocRTree (Deep (s - size z) pr m (Two x y)) z
viewRTree (Deep s pr m (Four w x y z)) =
    SnocRTree (Deep (s - size z) pr m (Three w x y)) z

{-# INLINE deep #-}
deep            :: Sized a => Digit a -> FingerTree (Node a) -> Digit a -> FingerTree a
deep pr m sf    =  Deep (size pr + size m + size sf) pr m sf

{-# INLINE node3 #-}
node3           :: Sized a => a -> a -> a -> Node a
node3 a b c     =  Node3 (size a + size b + size c) a b c

infixr 5 `consTree`
infixl 5 `snocTree`
{-# SPECIALIZE consTree :: Elem a -> FingerTree (Elem a) -> FingerTree (Elem a) #-}
{-# SPECIALIZE consTree :: Node a -> FingerTree (Node a) -> FingerTree (Node a) #-}
consTree        :: Sized a => a -> FingerTree a -> FingerTree a
consTree a EmptyT       = Single a
consTree a (Single b)   = deep (One a) EmptyT (One b)
-- As described in the paper, we force the middle of a tree
-- *before* consing onto it; this preserves the amortized
-- bounds but prevents repeated consing from building up
-- gigantic suspensions.
consTree a (Deep s (Four b c d e) m sf) = m `seq`
    Deep (size a + s) (Two a b) (node3 c d e `consTree` m) sf
consTree a (Deep s (Three b c d) m sf) =
    Deep (size a + s) (Four a b c d) m sf
consTree a (Deep s (Two b c) m sf) =
    Deep (size a + s) (Three a b c) m sf
consTree a (Deep s (One b) m sf) =
    Deep (size a + s) (Two a b) m sf

{-# SPECIALIZE snocTree :: FingerTree (Elem a) -> Elem a -> FingerTree (Elem a) #-}
{-# SPECIALIZE snocTree :: FingerTree (Node a) -> Node a -> FingerTree (Node a) #-}
snocTree        :: Sized a => FingerTree a -> a -> FingerTree a
snocTree EmptyT a       =  Single a
snocTree (Single a) b   =  deep (One a) EmptyT (One b)
-- See note on `seq` in `consTree`.
snocTree (Deep s pr m (Four a b c d)) e = m `seq`
    Deep (s + size e) pr (m `snocTree` node3 a b c) (Two d e)
snocTree (Deep s pr m (Three a b c)) d =
    Deep (s + size d) pr m (Four a b c d)
snocTree (Deep s pr m (Two a b)) c =
    Deep (s + size c) pr m (Three a b c)
snocTree (Deep s pr m (One a)) b =
    Deep (s + size b) pr m (Two a b)
