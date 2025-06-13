{-|

Module      : Syntax
Description : General definitions for modelling syntax

This module defines general concepts for modelling syntax via functors and (free) monads.

It includes:

- The free monad construction over syntax functors
- Initial algebra of terms as a special case of the free monad construction
- Relevant instance declarations 

These definitions serve as the basis for specifying operational semantics (in `HOGSOS`, `Separable`, etc.)
and for constructing and evaluating example terms and benchmarks.

-}

module Syntax where

import Data.Bifunctor (Bifunctor(bimap))
import Data.Void (Void)
import Control.Monad (ap)
import Control.Arrow ((&&&))

newtype Mrg s x = Mrg (s x x) -- Merge functor (To define Sigma from Sigma').

data Free s x -- The free object on a functor s.
  = Res x 
  | Cont (s (Free s x)) 
  deriving (Functor)

type Initial s = Free s Void -- The least fixpoint of Sigma*, i.e., muSigma.

sigOp :: s (Free (Mrg s) x) (Free (Mrg s) x) -> Free (Mrg s) x
sigOp = Cont . Mrg -- Abbreviation for the frequently used composition of type constructors.

instance Functor s => Applicative (Free s) where
  pure :: Functor s => a -> Free s a
  pure = Res
  (<*>) :: Functor s => Free s (a -> b) -> Free s a -> Free s b
  (<*>) = ap

instance Functor s => Monad (Free s) where
  (>>=) :: Functor s => Free s a -> (a -> Free s b) -> Free s b
  Res a >>= f = f a
  Cont x >>= f = Cont $ fmap (>>= f) x

instance Bifunctor s => Functor (Mrg s) where
  fmap :: Bifunctor s => (a -> b) -> Mrg s a -> Mrg s b
  fmap f (Mrg x) = Mrg (bimap f f x)

