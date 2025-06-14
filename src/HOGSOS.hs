{-|

Module      : HOGSOS
Description : Higher-order GSOS (HO-GSOS) specification format 

This module defines the HOGSOS type class and a generic definition of the operational model gamma.

It includes:

- The `HOGSOS` type class for specifying small-step operational semantics, including 
the operational model gamma for executing the operational semantics

This module provides the general framework for specifying and interpreting
higher-order operational semantics, as discussed in the paper.

-}

module HOGSOS where

import Data.Bifunctor ( Bifunctor(first) )
import Control.Arrow ((&&&)) -- To form product morphisms.
import Syntax 
import Behaviour

-- HO-GSOS law (Sec 2.3, Display (3))
class (Bifunctor s, MixFunctor b) => HOGSOS s b where
  rho :: s (x, b x y) x -> b x (Free (Mrg s) (Either x y))

  -- Operational model (Sec 2.3, Display (4))
  gamma :: Initial (Mrg s) -> b (Initial (Mrg s)) (Initial (Mrg s))
  gamma (Cont (Mrg t)) = mx_second (>>= nabla) $ rho $ first (id &&& gamma) t
    where nabla = either id id

