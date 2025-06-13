{-|

Module      : Syntax
Description : General definitions for modelling syntax

This module defines general concepts for modelling syntax via functors and free monads.

It includes:

- The free monad construction over syntax functors
- Initial algebra of terms as a special case of the free monad construction
- Pretty-printing and equality instances for terms

These definitions serve as the basis for specifying operational semantics (in `HOGSOS`, `Separable`, etc.)
and for constructing and evaluating example terms and benchmarks.

-}

module Syntax where

import Data.Bifunctor (Bifunctor(bimap))
import Data.Void (Void)
import Control.Monad (ap)
import Control.Arrow ((&&&))

-- | Syntax for xCL (extended combinatory logic).
data XCL' x y 
  = S 
  | K 
  | I 
  | S' x 
  | K' x 
  | S'' x x 
  | Comp x y 

-- | Value part of the xCL syntax.
data XCLV x 
  = Sv 
  | Kv 
  | Iv 
  | S'v x 
  | K'v x 
  | S''v x x 
  deriving (Functor)

-- | Computation part of the xCL syntax.
data XCLC x y 
  = Compc x y 

instance Functor (XCLC x) where
  fmap :: (a -> b) -> XCLC x a -> XCLC x b
  fmap f (Compc x y) = Compc x (f y)

instance Bifunctor XCLC where
  bimap :: (a -> b) -> (c -> d) -> XCLC a c -> XCLC b d
  bimap f g (Compc x y) = Compc (f x) (g y)

newtype Mrg s x = Mrg (s x x) -- Merge functor (To define Sigma from Sigma').

type XCL = Mrg XCL' -- XCL as a functor (an instance of Sigma in the paper).

instance Functor (XCL' x) where
  fmap :: (a -> b) -> XCL' x a -> XCL' x b 
  fmap f S = S
  fmap f K = K
  fmap f I = I
  fmap f (S' x) = S' x
  fmap f (K' x) = K' x
  fmap f (S'' x y) = S'' x y
  fmap f (Comp x y) = Comp x (f y)

instance Bifunctor XCL' where
  bimap :: (a -> b) -> (c -> d) -> XCL' a c -> XCL' b d
  bimap f g S = S
  bimap f g K = K
  bimap f g I = I
  bimap f g (S' x) = S' (f x)
  bimap f g (K' x) = K' (f x)
  bimap f g (S'' x y) = S'' (f x) (f y)
  bimap f g (Comp x y) = Comp (f x) (g y)

data Free s x -- The free object on a functor s.
  = Res x 
  | Cont (s (Free s x)) 
  deriving (Functor)

type Initial s = Free s Void -- The least fixpoint of Sigma*, i.e., muSigma.

sigOp :: s (Free (Mrg s) x) (Free (Mrg s) x) -> Free (Mrg s) x
sigOp = Cont . Mrg -- Abbreviation for the frequently used composition of type constructors.

instance Show (Initial XCL) where
  show :: Initial XCL -> String
  show (Cont (Mrg S)) = "S"
  show (Cont (Mrg (S' t))) = "(S'" ++ show t ++ ")"
  show (Cont (Mrg (S'' s t))) = "(S''" ++ show s ++ ", " ++ show t ++ ")"
  show (Cont (Mrg K)) = "K"
  show (Cont (Mrg (K' t))) = "(K'" ++ show t ++ ")"
  show (Cont (Mrg I)) = "I"
  show (Cont (Mrg (Comp t s))) = "(" ++ show t ++ " * " ++ show s ++ ")"

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

-- Non-deterministic xCL

data NDxCLV x 
  = NS 
  | NK 
  | NI 
  | NS' x 
  | NK' x 
  | NS'' x x 
  | VPar x x
  deriving (Functor)

data NDxCLC x y 
  = NComp x y 
  | DSum y y 
  | Par x x

instance Functor (NDxCLC x) where
  fmap :: (a -> b) -> NDxCLC x a -> NDxCLC x b
  fmap f (NComp x y) = NComp x (f y)
  fmap f (DSum y1 y2) = DSum (f y1) (f y2)
  fmap _ (Par x1 x2) = Par x1 x2

instance Bifunctor NDxCLC where
  bimap :: (a -> b) -> (c -> d) -> NDxCLC a c -> NDxCLC b d
  bimap f g (NComp x y) = NComp (f x) (g y)
  bimap f g (DSum x y)  = DSum (g x) (g y)
  bimap f _ (Par x y)   = Par (f x) (f y)
