{-# LANGUAGE Rank2Types, DefaultSignatures #-}
import Prelude hiding (sum)
import Data.Monoid
import Data.Void
import Control.Applicative
import Control.Monad.Cont

newtype Explore a =
  Explore { unExplore :: forall m. Monoid m => Cont m a }

runExplore :: Monoid m => Explore a -> (a -> m) -> m
runExplore = runCont . unExplore

mkExplore :: (forall m. Monoid m => (a -> m) -> m) -> Explore a
mkExplore f = Explore $ cont f

instance Functor Explore where
  fmap f e = mkExplore $ \g -> runExplore e (g . f)

instance Applicative Explore where
  pure x    = Explore $ pure x
  mf <*> mx = Explore $ unExplore mf <*> unExplore mx

instance Monad Explore where
  return  = pure
  m >>= f = Explore $ unExplore m >>= unExplore . f

instance Alternative Explore where
  empty     = mkExplore mempty
  mx <|> my = mkExplore (runExplore mx `mappend` runExplore my)

instance MonadPlus Explore where
  mzero = empty
  mplus = (<|>)

(<.|.>)  :: Alternative f => f a -> f b -> f (Either a b)
x <.|.> y = Left <$> x <|> Right <$> y

boolToNum :: Num n => Bool -> n
boolToNum False = 0
boolToNum True  = 1

class Summable a where
  sum :: Num n => (a -> n) -> n

  default sum :: (Explorable a, Num n) => (a -> n) -> n
  sum f = getSum $ explore (Sum . f)

  count :: Num n => (a -> Bool) -> n
  count f = sum (boolToNum . f)

class Summable a => Explorable a where
  exploration :: Explore a
  exploration = mkExplore explore

  explore :: Monoid m => (a -> m) -> m
  explore = runExplore exploration

  exploreWith :: Monoid m => (m -> r) -> (r -> m) -> (a -> r) -> r
  exploreWith proj inj f = proj $ explore (inj . f)

  product :: Num n => (a -> n) -> n
  product = exploreWith getProduct Product

  withEndo :: Monoid m => (a -> m) -> m
  withEndo f = exploreWith appEndo Endo (\x -> (f x <>)) mempty

  fAll :: (Applicative f, Monoid (f a)) => f a
  fAll = explore pure

  listAll :: [a]
  listAll = fAll

  -- refactor
  diffAll :: (Applicative f, Monoid (f a)) => f a
  diffAll = withEndo pure

  -- refactor
  diffListAll :: [a]
  diffListAll = diffAll

  findFirst :: (a -> Maybe b) -> Maybe b
  findFirst = exploreWith getFirst First

  findLast :: (a -> Maybe b) -> Maybe b
  findLast = exploreWith getLast Last

  any :: (a -> Bool) -> Bool
  any = exploreWith getAny Any

  all :: (a -> Bool) -> Bool
  all = exploreWith getAll All

{-
newtype EndoExploration a = EndoExploration { getEndoExploration :: a }

instance Explorable a => Explorable (EndoExploration a) where
  explore f = ...
instance Explorable a => Summable (EndoExploration a)

-}

filter :: (a -> Bool) -> Explore a -> Explore a
filter p e = mkExplore $ \f -> runExplore e $ \x -> if p x then f x else mempty

{-
GHCI> runExplore (Main.filter (uncurry (==)) exploration) pure :: [(Bool,Bool)]
[(False,False),(True,True)]
-}

instance Explorable Void where exploration = empty
instance Summable   Void

instance Explorable () where exploration = pure ()
instance Summable   ()

instance Explorable Bool where exploration = pure False <|> pure True
instance Summable   Bool

instance (Explorable a, Explorable b) => Explorable (a, b) where
  exploration = liftM2 (,) exploration exploration

instance (Summable a, Summable b) => Summable (a, b) where
  sum = runCont $ liftM2 (,) (cont sum) (cont sum)

instance (Explorable a, Explorable b) => Explorable (Either a b) where
  exploration = exploration <.|.> exploration

instance (Summable a, Summable b) => Summable (Either a b) where
  sum f = sum (f . Left) + sum (f . Right)

instance Explorable a => Explorable (Maybe a) where
  exploration = pure Nothing <|> Just <$> exploration

instance Summable a => Summable (Maybe a) where
  sum f = f Nothing + sum (f . Just)

-- This instance only make sense for non-strict explorations
instance Explorable a => Explorable [a] where
  explore f = f [] <> explore (\(x,xs) -> f (x:xs))

-- Apart from non-strict Num instance this will be undefined
instance Summable a => Summable [a] where
  sum f = f [] + sum (\(x,xs) -> f (x:xs))

count_uniq_prop :: (Eq a, Explorable a) => a -> Bool
count_uniq_prop x = count (==x) == 1

-- {-
--data H = H
--h :: a
--h = h
--import Debug.Trace
--tr f s = trace (f s) s
-- -}
-- -}
-- -}
-- -}
-- -}
