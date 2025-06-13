{-|
Module      : BigStep
Description : Big-step operational semantics and its derivation from separated HO-GSOS

This module defines a type class for abstract big-step semantics ``BSSOS``, 
its monadic variant ``BSSOST`` and a derivations of big-step semantics from a 
separated higher-order GSOS through instance declaration.
      
It includes:

- The `BSSOS` and `BSSOST` type classes for big-step semantics (with and without monads)
- Derivations of big-step rules from HO-GSOS specifications
- Test functions for evaluating big-step semantics on example terms

This module provides a definition of big-step semantics as a type class and 
and a translation from small-step to big-step semantics thorugh an instance declaration.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures, PolyKinds, TypeApplications #-}

module BigStep where

import Data.Kind
import Data.Proxy ( Proxy(Proxy) )
import Data.Bifunctor ( Bifunctor(bimap, first, second) )
import Control.Monad (join, (<=<))
import Control.Arrow ((&&&))
import Syntax (XCL, sigOp, Free (Cont, Res), NDxCLC(..), NDxCLV(..), Initial, Mrg (Mrg))
import Behaviour ( MixFunctor(mx_second) )
import Separable (SepSig, SepSig'(SigV, SigC), SepHOGSOST(rhoVT, rhoCVT, chi), InitialV, InitialC, SepHOGSOS (rhoV, rhoCV) )


-- Definitions related to Big-step SOS:

-- Abstract Big-step SOS without monad.
class (Functor sv, Bifunctor sc) => BSSOS d sv sc where
  xi :: sc (sv x) x -> Free (SepSig sv sc) x

  zetahat :: Initial (SepSig sv sc) -> InitialV sv sc
  zetahat (Cont (Mrg (SigV v))) =  v
  zetahat (Cont (Mrg (SigC c))) = zetahat @d $ join $ xi @d $ first (zetahat @d) c

  -- The operational model.
  zeta :: InitialC sv sc -> InitialV sv sc
  zeta = zetahat @d . sigOp . SigC

-- Deriving big-step specification from a separated HO-GSOS law.
instance (Bifunctor sc, Functor sv, SepHOGSOS sv sc d) => BSSOS (d :: Type -> Type -> Type) sv sc where
  xi :: sc (sv x) x -> Free (SepSig sv sc) x
  xi t =
    rhoCV (bimap ((sigOp . SigV &&& mx_second @d join . rhoV) . fmap return)
                 return t) >>= nabla
    where nabla = either id id

-- Abstract Big-step SOS with monad.
class (Functor sv, Bifunctor sc, Monad t) => BSSOST a sv sc t where
  xiT :: sc (sv x) x -> t (Free (SepSig sv sc) x)
  bs_chi :: sc (t x) y -> t (sc x y)

  zetahatT :: Initial (SepSig sv sc) -> t (InitialV sv sc)
  zetahatT (Cont (Mrg (SigV v))) = return v
  zetahatT (Cont (Mrg (SigC c))) = (bs_chi @a @sv $ first (zetahatT @a) c)
    >>= xiT @a >>= zetahatT @a . join

  zetaT :: InitialC sv sc -> t (InitialV sv sc)
  zetaT = zetahatT @a . sigOp . SigC

-- Deriving big-step specification from a separated HO-GSOS law with monad.
instance (Bifunctor sc, Functor sv, Monad t, SepHOGSOST sv sc d t) => BSSOST d sv sc t where
  xiT :: SepHOGSOST sv sc d t => sc (sv x) x -> t (Free (SepSig sv sc) x)
  xiT = fmap (>>= nabla) . rhoCVT . 
        bimap (sigOp . SigV . fmap return &&& (return . mx_second @d join . rhoVT @_ @_ @_ @t . fmap return)) return
          where nabla = either id id
  bs_chi :: SepHOGSOST sv sc d t => sc (t x) y -> t (sc x y)
  bs_chi = chi @sv @sc @d @t

-- The test function for the operational model of xi for non-deterministic xCL.
tryEvalZT :: Initial (SepSig NDxCLV NDxCLC) -> [InitialV NDxCLV NDxCLC]
tryEvalZT = zetahatT @(->) @NDxCLV @NDxCLC @[]

