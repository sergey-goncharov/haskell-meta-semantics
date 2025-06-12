{-|
Module      : Behaviour
Description : Definitions related to defining (mixed-variance) functors for behaviours
and examples

This module defines the `MixFunctor` type class and instances for modeling
behaviors in a higher-order setting. It includes:

- `MixFunctor` type class for mixed-variance functors
- The `Beh` data type for deterministic behavior
- Relevant instance declarations 

This module abstracts over the structure of behavioral functors and is used
in both HoGSOS and Separated HoGSOS specifications.
-}

module Behaviour where

import Control.Arrow ((&&&)) -- For arrows to a product object.

-- The behavior functor in the paper:

-- The class of mixed-variance functors in Haskell.
class MixFunctor f where
  mvmap :: (a -> b) -> (c -> d) -> f b c -> f a d
  mvmap g h = mx_first g . mx_second h

  mx_second :: (b -> c) -> f a b -> f a c
  mx_second = mvmap id  

  mx_first :: (a -> b) -> f b c -> f a c
  mx_first g = mvmap g id

-- A handy instance of behavior (mixed-variance) functor: B(X,Y) = Y + Y^X.
data Beh x y = Eval (x -> y) | Red y

-- Instantiating Beh as a mixed-variance functor.
instance MixFunctor Beh where
  mvmap :: (a -> b) -> (c -> d) -> Beh b c -> Beh a d
  mvmap f g (Red y)  = Red (g y)
  mvmap f g (Eval h) = Eval (g . h . f) 

-- Separated non-deterministic xCL behavior: **TODO** where?

-- The arrow as a behavior mixed-variance functor.
instance MixFunctor (->) where
  mvmap :: (a -> b) -> (c -> d) -> (b -> c) -> a -> d
  mvmap f g h = g . h . f


