{-|

Module      : Behaviour
Description : General definitions related to modelling higher-order behaviors
as (mixed variance) functors

This module defines the `MixFunctor` type class and instances for behaviors 
in a higher-order setting. It includes:

- `MixFunctor` type class for mixed variance functors
- Relevant instance declarations 

This module abstracts over the structure of behavioral functors and is used
in both HO-GSOS and Separated HO-GSOS specifications.

-}

module Behaviour where

import Control.Arrow ((&&&)) -- To form product morphisms.

-- The class of mixed-variance functors in Haskell (alternatively, Profunctor type class could be used).
class MixFunctor f where
  mvmap :: (a -> b) -> (c -> d) -> f b c -> f a d
  mvmap g h = mx_first g . mx_second h

  mx_second :: (b -> c) -> f a b -> f a c
  mx_second = mvmap id  

  mx_first :: (a -> b) -> f b c -> f a c
  mx_first g = mvmap g id

-- A handy instance of behavior (mixed variance) functor: B(X,Y) = Y + Y^X.
data Beh x y = Eval (x -> y) | Red y

-- Effectless "separated" behaviour functor (Sec. 2.1., didactic purpose only)
data SepBeh d x y = BehV (d x y) | BehC y

-- (Effectful) "separated" behaviour functor, Def. 3.1
data SepBehT t d x y = BehVT (d x y) | BehCT (t y)

-- Instantiating Beh as a mixed-variance functor.
instance MixFunctor Beh where
  mvmap :: (a -> b) -> (c -> d) -> Beh b c -> Beh a d
  mvmap f g (Red y)  = Red (g y)
  mvmap f g (Eval h) = Eval (g . h . f) 

-- The arrow as a behavior mixed-variance functor.
instance MixFunctor (->) where
  mvmap :: (a -> b) -> (c -> d) -> (b -> c) -> a -> d
  mvmap f g h = g . h . f

-- Instantiating separated effectless behaviour type constructor as a mixed-variance functor.
instance (MixFunctor d) => MixFunctor (SepBeh d) where
  mvmap :: (a -> b) -> (c -> e) -> SepBeh d b c -> SepBeh d a e
  mvmap f g (BehV u) = BehV $ mvmap f g u
  mvmap f g (BehC u) = BehC $ g u

-- Instantiating separated effectful behaviour type constructor as a mixed-variance functor.
instance (Functor t, MixFunctor d) => MixFunctor (SepBehT t d) where
  mvmap :: (a -> b) -> (c -> e) -> SepBehT t d b c -> SepBehT t d a e
  mvmap f g (BehVT u) = BehVT $ mvmap f g u
  mvmap f g (BehCT u) = BehCT $ fmap g u

