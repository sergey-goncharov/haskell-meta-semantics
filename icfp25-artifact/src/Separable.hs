{-|
Module      : Separable
Description : Separated HO-GSOS and operational semantics for non-deterministic calculi

This module defines the separated syntax and behavior functors, and implements
the Separated HO-GSOS specification format. It includes:

- Definitions of separated syntax functors (Σ_v and Σ_c)
- Mixed-variance behavior functors (with and without monads)
- Operational semantics via `gammaV`, `gammaC`, and multi-step transitions `beta`, `hatbeta`
- Instances for non-deterministic xCL and its operational rules

This module provides a refinement of HO-GSOS based on separation between computation and values 
for syntax and behavior.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}

module Separable where

import Data.Proxy (Proxy(Proxy))
import Data.Bifunctor (Bifunctor(bimap, first, second))
import Control.Arrow ((&&&))
import Control.Monad (join)
import Syntax 
import Behaviour (MixFunctor(..), Beh (Eval, Red))
import HOGSOS (HOGSOS(..), gamma)

-- Definitions related to separated HO-GSOS laws:
-- We have also defined the Beta function (the multi-step transition) in the paper as a function of the class of separated HO-GSOS laws.

-- Separated syntax functor (the bifunctor Sigma').
data SepSig' sv sc x y = SigV (sv y) | SigC (sc x y)
type SepSig sv sc = Mrg (SepSig' sv sc) -- Separated syntax functor (Sigma).

-- muSigma_v in the paper.
type InitialV sv sc = sv (Initial (SepSig sv sc))

-- muSigma_c in the paper.
type InitialC sv sc = sc (Initial (SepSig sv sc)) (Initial (SepSig sv sc))

instance (Functor sv, Bifunctor sc, Functor (sc b)) => Functor (SepSig' sv sc b) where
  fmap :: (a -> c) -> SepSig' sv sc b a -> SepSig' sv sc b c 
  fmap f (SigV t) = SigV $ fmap f t
  fmap f (SigC t) = SigC $ fmap f t

-- Instantiating Sigma_v Pi_2 + Sigma_c as a bifunctor.
instance (Functor sv, Bifunctor sc) => Bifunctor (SepSig' sv sc) where
  bimap :: (a -> b) -> (c -> d) -> SepSig' sv sc a c -> SepSig' sv sc b d
  bimap f g (SigV t) = SigV $ fmap g t
  bimap f g (SigC t) = SigC $ bimap f g t

-- Separated behaviour functor without effects.
data SepBeh d x y = BehV (d x y) | BehC y
-- Separated behaviour functor with the effect monad t.
-- newtype SepBehT t d x y = SepBehT (t (SepBeh d x y))
data SepBehT t d x y = BehVT (t (d x y)) | BehCT (t y)

-- Instantiating separated behaviour bifunctor without effects as a mixed-variance functor.
instance (MixFunctor d) => MixFunctor (SepBeh d) where
  mvmap :: (a -> b) -> (c -> e) -> SepBeh d b c -> SepBeh d a e
  mvmap f g (BehV u) = BehV $ mvmap f g u
  mvmap f g (BehC u) = BehC $ g u

-- Instantiating separated behaviour with the effect monad t as a mixed-variance functor.
instance (Functor t, MixFunctor d) => MixFunctor (SepBehT t d) where
  mvmap :: (a -> b) -> (c -> e) -> SepBehT t d b c -> SepBehT t d a e
  -- mvmap f g (SepBehT u) = SepBehT $ fmap (mvmap f g) u
  mvmap f g (BehVT u) = BehVT $ fmap (mvmap f g) u
  mvmap f g (BehCT u) = BehCT $ fmap g u

-- Separable HO-GSOS: version without a monad
class (MixFunctor d, Functor sv, Bifunctor sc) => SepHOGSOS sv sc d where
  rhoV :: sv x -> d x (Free (SepSig sv sc) x)
  rhoC :: sc (x, SepBeh d x y) x -> Free (SepSig sv sc) (Either x y)

  rhoCV :: sc (x, d x y) x -> Free (SepSig sv sc) (Either x y)
  rhoCV = rhoC . first (second BehV)

  -- Operational model for rhoV
  gammaV :: InitialV sv sc -> d (Initial (SepSig sv sc)) (Initial (SepSig sv sc))
  gammaV t = mvmap id join $ rhoV t

  -- Operational model for rhoC
  gammaC :: Proxy d -> InitialC sv sc -> Initial (SepSig sv sc)
  gammaC (p :: Proxy d) t = (rhoC @_ @_ @d $ first (id &&& gamma') t) >>= nabla
    where nabla = either id id; gamma' (Cont (Mrg (SigV v))) = BehV $ gammaV v; gamma' (Cont (Mrg (SigC c))) = BehC $ gammaC p c 

  -- Multi-step transition for rhoC.
  beta :: (Functor sv, Bifunctor sc, MixFunctor d, SepHOGSOS sv sc d)
    => Proxy d -> InitialC sv sc -> InitialV sv sc
  beta (p :: Proxy d) t = case gammaC p t of
    Cont (Mrg (SigV t)) -> t
    Cont (Mrg (SigC t)) -> beta p t

  -- Multi-step transition for rhoC (variant).
  hatbeta :: (Functor sv, Bifunctor sc, MixFunctor d, SepHOGSOS sv sc d)
    => Proxy d -> Initial (SepSig sv sc) -> InitialV sv sc
  hatbeta (p :: Proxy d) (Cont (Mrg (SigV v))) = v
  hatbeta (p :: Proxy d) (Cont (Mrg (SigC c))) = hatbeta p (gammaC p c)


-- Instantiating separated laws as HO-GSOS laws.
instance (SepHOGSOS sv sc d) => HOGSOS (SepSig' sv sc) (SepBeh d) where
  rho :: SepSig' sv sc (x, SepBeh d x y) x -> SepBeh d x (Free (SepSig sv sc) (Either x y))
  rho (SigV v) = BehV $ mvmap id (fmap Left) (rhoV v)
  rho (SigC c) = BehC $ rhoC c

-- Separable HO-GSOS: version with a monad.
class (Functor sv, Bifunctor sc, MixFunctor d, Monad t) => SepHOGSOST sv sc d t where
  rhoVT :: sv x -> d x (Free (SepSig sv sc) x)
  rhoCT :: sc (x, SepBehT t d x y) x -> t (Free (SepSig sv sc) (Either x y))
  chi :: sc (t x) y -> t (sc x y)

  rhoCVT :: sc (x, t (d x y)) x -> t (Free (SepSig sv sc) (Either x y))
  rhoCVT = rhoCT . first (second BehVT)

  -- Operational model for rhoVT
  gammaVT :: InitialV sv sc -> d (Initial (SepSig sv sc)) (Initial (SepSig sv sc))
  gammaVT = mvmap id join . rhoVT @_ @_ @d @t

  -- Operational model for rhoCT
  gammaCT :: Proxy d -> InitialC sv sc -> t (Initial (SepSig sv sc))
  gammaCT (p :: Proxy d) = fmap (>>= nabla) . rhoCT @_ @_ @d . first (id &&& gamma)
    where nabla = either id id

  -- Multi-step transition for rhoC.
  betaT :: Proxy d -> InitialC sv sc -> t (InitialV sv sc)
  betaT (p :: Proxy d) t = gammaCT p t >>= \t -> case t of
    Cont (Mrg (SigV t)) -> return t
    Cont (Mrg (SigC t)) -> betaT p t

  betahatT :: Proxy d -> Initial (SepSig sv sc) -> t (InitialV sv sc)
  betahatT (p :: Proxy d) (Cont (Mrg (SigV v))) = return v
  betahatT (p :: Proxy d) (Cont (Mrg (SigC c))) = betaT p c

-- Instantiating separated laws with a monad as HO-GSOS laws.
instance (SepHOGSOST sv sc d t) => HOGSOS (SepSig' sv sc) (SepBehT t d) where
  rho :: SepSig' sv sc (x, SepBehT t d x y) x -> SepBehT t d x (Free (SepSig sv sc) (Either x y))
  rho (SigV v) = BehVT $ return $ mx_second (fmap Left) (rhoVT @_ @_ @d @t v)
  rho (SigC c) = BehCT $ rhoCT c
