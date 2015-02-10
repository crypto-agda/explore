{-# LANGUAGE RankNTypes #-}
module FoldMapProperties where

import Data.Monoid
import Data.Foldable
import Control.Applicative

type Nat = Integer

newtype MonoidHom m n =
  MonoidHom { hom :: m -> n }

monoidHomMempty :: (Monoid m, Monoid n, Eq n) => MonoidHom m n -> Bool
monoidHomMempty (MonoidHom h) = h mempty == mempty

monoidHomMappend :: (Monoid m, Monoid n, Eq n) => MonoidHom m n -> m -> m -> Bool
monoidHomMappend (MonoidHom h) x y = h (x <> y) == h x <> h y

distHomProp :: (Monoid m, Monoid n, Foldable t, Eq n) => MonoidHom m n -> (a -> m) -> t a -> Bool
distHomProp (MonoidHom h) f t = h (foldMap f t) == foldMap (h . f) t

newtype Explore a =
  Explore { runExplore :: forall m. Monoid m => (a -> m) -> m }

type Explore' a = forall m. m -> (m -> m -> m) -> (a -> m) -> m

toExplore :: Foldable t => t a -> Explore a
toExplore ta = Explore $ flip foldMap ta

emptyExplore :: Explore a
emptyExplore = Explore $ const mempty

mergeExplore :: Explore a -> Explore a -> Explore a
mergeExplore (Explore e0) (Explore e1) = Explore $ \f -> e0 f <> e1 f

pointExplore :: a -> Explore a
pointExplore x = Explore $ ($ x)

class Explorable a where
  explore :: forall m. Monoid m => (a -> m) -> m

instance (Explorable a, Explorable b) => Explorable (a, b) where
  explore f = explore $ \x -> explore $ \y -> f (x , y)

instance (Explorable a, Explorable b) => Explorable (Either a b) where
  explore f = explore (f . Left) <> explore (f . Right)

instance Explorable () where
  explore f = f ()

instance Explorable Bool where
  explore f = f False <> f True

instance Functor Explore where
  fmap f (Explore e) = Explore $ \g -> e $ g . f

instance Applicative Explore where
  pure = pointExplore
  Explore e0 <*> Explore e1 = Explore $ \f -> e0 $ \g -> e1 $ f . g

instance Monad Explore where
  return = pointExplore
  Explore e0 >>= k = Explore $ \f -> e0 $ \x -> runExplore (k x) f

sum :: Explorable a => (a -> Nat) -> Nat
sum f = getSum (explore (Sum . f))
