{-|

Module      : Behaviour
Description : General definitions related to modelling higher-order behaviors
as (mixed-variance) functors

This module defines the `MixFunctor` type class and instances for 
behaviors in a higher-order setting. It includes:

- `MixFunctor` type class for mixed-variance functors
- Relevant instance declarations 

This module abstracts over the structure of behavioral functors and is used
in both HO-GSOS and Separated HO-GSOS specifications.

-}

module Behaviour where

import Control.Arrow ((&&&)) -- For arrows to a product object.

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

-- The arrow as a behavior mixed-variance functor.
instance MixFunctor (->) where
  mvmap :: (a -> b) -> (c -> d) -> (b -> c) -> a -> d
  mvmap f g h = g . h . f


