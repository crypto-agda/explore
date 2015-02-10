{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module FoldMapProperties where

import Prelude hiding (sum,product,all,any)
import Control.Arrow ((&&&))
import Data.Monoid
import Data.Foldable (Foldable,foldMap)

type Nat = Integer

(==>) :: Bool -> Bool -> Bool
p ==> q = not p || q

newtype MonoidHom m n =
  MonoidHom { hom :: m -> n }

monoidHomMemptyLaw :: (Monoid m, Monoid n, Eq n) => MonoidHom m n -> Bool
monoidHomMemptyLaw (MonoidHom h) = h mempty == mempty

monoidHomMappendLaw :: (Monoid m, Monoid n, Eq n) => MonoidHom m n -> m -> m -> Bool
monoidHomMappendLaw (MonoidHom h) x y = h (x <> y) == h x <> h y

sum :: (Foldable t, Num n) => (a -> n) -> t a -> n
sum f = getSum . foldMap (Sum . f)

product :: (Foldable t, Num n) => (a -> n) -> t a -> n
product f = getProduct . foldMap (Product . f)

all :: Foldable t => (a -> Bool) -> t a -> Bool
all f = getAll . foldMap (All . f)

any :: Foldable t => (a -> Bool) -> t a -> Bool
any f = getAny . foldMap (Any . f)

-- Theorem 1
distHom_prop :: (Monoid m, Monoid n, Foldable t, Eq n) => MonoidHom m n -> (a -> m) -> t a -> Bool
distHom_prop (MonoidHom h) f t = h (foldMap f t) == foldMap (h . f) t

-- Corollary 1
sumLin_prop :: (Foldable t, Eq a, Num a) => t b -> a -> (b -> a) -> Bool
sumLin_prop t k f = k * sum f t == sum (\x -> k * f x) t

class (Ord m, Monoid m) => MonotonicMon m

monotonicMonLaw :: MonotonicMon m => m -> m -> m -> m -> Bool
monotonicMonLaw x x' y y' = (x <= x' && y <= y') ==> (x <> y <= x' <> y')

-- Theorem 2
foldMapMono_prop :: (Foldable t, Ord (a -> m), Eq m, MonotonicMon m) => t a -> (a -> m) -> (a -> m) -> Bool
foldMapMono_prop t f g = (f <= g) ==> (foldMap f t <= foldMap g t)

-- Theorem 3
foldMapHom_prop :: (Foldable t, Monoid m, Eq m) => t a -> (a -> m) -> (a -> m) -> Bool
foldMapHom_prop t f g = foldMap (f <> g) t == foldMap f t <> foldMap g t

-- Theorem 4
foldMapProd_prop :: (Foldable t, Monoid m, Monoid n, Eq m, Eq n) => t a -> (a -> m) -> (a -> n) -> Bool
foldMapProd_prop t f g = foldMap (f &&& g) t == (foldMap f t , foldMap g t)

-- Theorem 5
foldMapEndo_prop :: (Foldable t, Monoid m, Eq m) => t a -> (a -> m) -> m -> Bool
foldMapEndo_prop t f z = foldMap f t <> z == appEndo (foldMap (Endo . (<>) . f) t) z

-- Corollary 2
foldMapEndo'_prop :: (Foldable t, Monoid m, Eq m) => t a -> (a -> m) -> Bool
foldMapEndo'_prop t f = foldMap f t == appEndo (foldMap (Endo . (<>) . f) t) mempty

data Tree a = Empty | Leaf a | Fork (Tree a) (Tree a)
  deriving (Eq)

instance Foldable Tree where
  foldMap _ Empty      = mempty
  foldMap f (Leaf x)   = f x
  foldMap f (Fork l r) = foldMap f l <> foldMap f r

-- This monoid is cheating
instance Monoid (Tree a) where
  mempty = Empty
  mappend = Fork

toTree :: Foldable t => t a -> Tree a
toTree = foldMap Leaf

-- Theorem 6
foldMapTree_prop :: (Foldable t, Monoid m, Eq m) => t a -> (a -> m) -> Bool
foldMapTree_prop t f = foldMap f t == foldMap f (toTree t)

class Foldable t => AdequateSig t
-- The law in the paper requires dependent types

-- Theorem 7
foldMapAll_prop :: AdequateSig t => t a -> (a -> Bool) -> a -> Bool
foldMapAll_prop t f x = all f t ==> f x

{-
prodSum_prop :: 
prodSum_prop t u
product (\x -> sum (\y -> f x y) u) t == sum (\g -> product (\x -> f x (g x)) t)
-}

sum (f . p) t == sum f t
