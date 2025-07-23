{-|

Module      : BigStep
Description : Abstract notion of Big-step operational semantics

This module defines a type class for abstract big-step semantics ``BSSOS``, 
its effectful variant ``BSSOST`` and derivations of big-step semantics from a 
separated higher-order GSOS through instance declaration.
      
It includes:

- The `BSSOS` and `BSSOST` type classes for big-step semantics (effectful and effectless)
- Derivations of big-step semantics from small-step semantics in separated HO-GSOS format
through instance declarations.

This module provides a definition of big-step semantics as a type class and 
and a translation from small-step to big-step through an instance declaration.

-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures, PolyKinds, TypeApplications #-}

module BigStep where

import Data.Kind
import Data.Proxy ( Proxy(Proxy) )
import Data.Bifunctor ( Bifunctor(bimap, first, second) )

import Control.Monad (join, (<=<))
import Control.Arrow ((&&&))

import Syntax
import Behaviour ( MixFunctor(mx_second) )
import Separable (SepSig, SepSig'(SigV, SigC), SepHOGSOST(rhoVT, rhoCVT, chi), InitialV, InitialC, SepHOGSOS (rhoV, rhoCV) )

-- | Effectless abstract Big-step SOS (Sec 2.1., didactic purpose only)
class (Functor sv, Bifunctor sc) => BSSOS d sv sc where
  xi :: sc (sv x) x -> Free (SepSig sv sc) x

  zetahat :: Initial (SepSig sv sc) -> InitialV sv sc
  zetahat (Cont (Mrg (SigV v))) =  v
  zetahat (Cont (Mrg (SigC c))) = zetahat @d $ join $ xi @d $ first (zetahat @d) c

  -- Big-step operational model.
  zeta :: InitialC sv sc -> InitialV sv sc
  zeta = zetahat @d . sigOp . SigC

-- | Deriving big-step specification from a separated HO-GSOS law.
instance (Bifunctor sc, Functor sv, SepHOGSOS sv sc d) => BSSOS (d :: Type -> Type -> Type) sv sc where
  xi :: sc (sv x) x -> Free (SepSig sv sc) x
  xi t =
    rhoCV (bimap ((sigOp . SigV &&& mx_second @d join . rhoV) . fmap return) return t) >>= nabla
    where nabla = either id id

-- | Abstract Big-step SOS with (effectful), Def. 4.1
class (Functor sv, Bifunctor sc, Monad t) => BSSOST a sv sc t where
  xiT :: sc (sv x) x -> t (Free (SepSig sv sc) x)
  bs_chi :: sc (t x) y -> t (sc x y)

  -- | Operational model (Display (19))
  zetahatT :: Initial (SepSig sv sc) -> t (InitialV sv sc)
  zetahatT (Cont (Mrg (SigV v))) = return v
  zetahatT (Cont (Mrg (SigC c))) = (bs_chi @a @sv $ first (zetahatT @a) c) >>= xiT @a >>= zetahatT @a . join

  zetaT :: InitialC sv sc -> t (InitialV sv sc)
  zetaT = zetahatT @a . sigOp . SigC

-- | Deriving big-step specification from a separated HO-GSOS law with monad, Display (17)
instance (Bifunctor sc, Functor sv, Monad t, SepHOGSOST sv sc d t) => BSSOST d sv sc t where
  xiT :: SepHOGSOST sv sc d t => sc (sv x) x -> t (Free (SepSig sv sc) x)
  xiT = fmap (>>= nabla) . rhoCVT . 
        bimap (sigOp . SigV . fmap return &&& (mx_second @d join . rhoVT @_ @_ @_ @t . fmap return)) return
          where nabla = either id id
          
  bs_chi :: SepHOGSOST sv sc d t => sc (t x) y -> t (sc x y)
  bs_chi = chi @sv @sc @d @t

