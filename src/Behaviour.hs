module Behaviour where

import Control.Arrow ((&&&)) -- For arrows to a product object.

-- The behaviour functor in the paper:

-- The class of mixed-variance functors in Haskell.
class MixFunctor f where
  mvmap :: (a -> b) -> (c -> d) -> f b c -> f a d
  mvmap g h = mx_first g . mx_second h

  mx_second :: (b -> c) -> f a b -> f a c
  mx_second = mvmap id  

  mx_first :: (a -> b) -> f b c -> f a c
  mx_first g = mvmap g id

-- A handy instance of behaviour (mixed-variance) functor: B(X,Y)=Y+Y^X.
data Beh x y = Eval (x -> y) | Red y

-- Instantiating Beh as a mixed-variance functor.
instance MixFunctor Beh where
  mvmap :: (a -> b) -> (c -> d) -> Beh b c -> Beh a d
  mvmap f g (Red y)  = Red (g y)
  mvmap f g (Eval h) = Eval (g . h . f) 

-- Separated non-deterministic xCL behaviour:

-- The arrow as a behaviour mixed-variance functor.
instance MixFunctor (->) where
  mvmap :: (a -> b) -> (c -> d) -> (b -> c) -> a -> d
  mvmap f g h = g . h . f


