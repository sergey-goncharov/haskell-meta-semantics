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
import Syntax (NDxCLC(..), NDxCLV(..), XCLC(..), XCLV(..), Initial, Free(..), Mrg(..), sigOp)
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

-- Instantiating the operational semantics of non-deterministic xCL as a separated HO-GSOS law with monad.
instance SepHOGSOS XCLV XCLC (->) where
  rhoV :: XCLV x -> x -> Free (SepSig XCLV XCLC) x
  rhoV Sv = sigOp . SigV . S'v . Res
  rhoV Kv = sigOp . SigV . K'v . Res
  rhoV Iv = Res
  rhoV (S'v t) = sigOp . SigV . S''v (Res t) . Res
  rhoV (K'v t) = const (Res t)
  rhoV (S''v t s) = \u -> sigOp $ SigC $ Compc (sigOp $ SigC $ Compc (Res t) (Res u)) (sigOp $ SigC $ Compc (Res s) (Res u))
 
  rhoC :: XCLC (x, SepBeh (->) x y) x -> Free (SepSig XCLV XCLC) (Either x y)
  rhoC (Compc (_, BehC s) u) = sigOp (SigC $ Compc (Res $ Right s) (Res $ Left u))
  rhoC (Compc (_, BehV f) u) = Res (Right $ f u) 

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

-- Non-deterministic xCL as an example:

-- Instantiating the operational semantics of non-deterministic xCL as a separated HO-GSOS law with monad.
instance SepHOGSOST NDxCLV NDxCLC (->) [] where
  rhoVT :: NDxCLV x -> x -> Free (SepSig NDxCLV NDxCLC) x
  rhoVT NS = sigOp . SigV . NS' . Res
  rhoVT NK = sigOp . SigV . NK' . Res
  rhoVT NI = Res
  rhoVT (NS' t) = sigOp . SigV . NS'' (Res t) . Res
  rhoVT (NK' t) = const (Res t)
  rhoVT (NS'' t s) = \u -> sigOp $ SigC $ NComp (sigOp $ SigC $ NComp (Res t) (Res u)) (sigOp $ SigC $ NComp (Res s) (Res u))
  rhoVT (VPar t s) = \u -> sigOp $ SigC $ Par (sigOp $ SigC $ NComp (Res t) (Res u)) (sigOp $ SigC $ NComp (Res s) (Res u))


  rhoCT :: NDxCLC (x, SepBehT [] (->) x y) x -> [Free (SepSig NDxCLV NDxCLC) (Either x y)]
  rhoCT (NComp (s, BehCT (s' : l)) t) = sigOp (SigC $ NComp (Res $ Right s') (Res $ Left t)) : rhoCT @_ @_ @(->) (NComp (s, BehCT l) t)
  rhoCT (NComp (s, BehVT (f : l)) t)  = Res (Right $ f t) : rhoCT (NComp (s, BehVT l) t)
  rhoCT (NComp (s, BehCT [] ) t) = []
  rhoCT (NComp (s, BehVT [] ) t) = []

  rhoCT (DSum s t) = [Res $ Left s, Res $ Left t]
 
  rhoCT (Par (s, BehCT (s' : k)) (t, BehCT (t' : l))) = [sigOp $ SigC $ Par (Res $ Right s') (Res $ Right t')] 
    ++ rhoCT @_ @_ @(->) (Par (s, BehCT (s' : k)) (t, BehCT l)) 
    ++ rhoCT @_ @_ @(->) (Par (s, BehCT k) (t, BehCT (t' :  l)))

  rhoCT (Par (s, BehVT (f : k)) (t, BehCT (t' : l)))  = [sigOp $ SigC $ Par (Res $ Left s) (Res $ Right t')] 
    ++ rhoCT @_ @_ @(->) (Par (s, BehVT (f : k)) (t, BehCT l)) 
    ++ rhoCT @_ @_ @(->) (Par (s, BehVT k) (t, BehCT (t' : l)))

  rhoCT (Par (s, BehCT (s' : k)) (t, BehVT (g : l)))  = [sigOp $ SigC $ Par (Res $ Right s') (Res $ Left t)] 
    ++ rhoCT @_ @_ @(->) (Par (s, BehCT (s' : k)) (t, BehVT l)) 
    ++ rhoCT @_ @_ @(->) (Par (s, BehCT k) (t, BehVT (g : l)))

  rhoCT (Par (s, BehVT (f : k)) (t, BehVT (g : l)))  = [sigOp $ SigV $ VPar (Res $ Left s) (Res $ Left t)]

  rhoCT (Par (s, BehCT []) _) = []
  rhoCT (Par (s, BehVT []) _) = []
  rhoCT (Par _ (t, BehCT [])) = []
  rhoCT (Par _ (t, BehVT [])) = []


  chi :: NDxCLC [x] y -> [NDxCLC x y]
  chi (NComp (x : xs) y) = NComp x y : chi @NDxCLV @NDxCLC @(->) @[] (NComp xs y)
  chi (NComp [] y) = []
  chi (DSum x y) = [DSum x y]
  chi (Par (s : k) (t : l)) = [Par s t] ++ chi @NDxCLV @NDxCLC @(->) @[] (Par (s : k) l) ++ chi @NDxCLV @NDxCLC @(->) @[] (Par k (t : l))
  chi (Par [] l) = []
  chi (Par k []) = []

-- Instantiating the syntax of non-deterministic xCL for the Show and Eq functors (mentioned in the section 6.3).
instance Show (Initial (SepSig NDxCLV NDxCLC)) where
  show :: Initial (SepSig NDxCLV NDxCLC) -> String
  show (Cont (Mrg (SigV NS))) = "S"
  show (Cont (Mrg (SigV (NS' t)))) = "S'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV (NS'' s t)))) = "S''(" ++ show s ++ ", " ++ show t ++ ")"
  show (Cont (Mrg (SigV NK))) = "K"
  show (Cont (Mrg ((SigV (NK' t))))) = "K'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV NI))) = "I"
  show (Cont (Mrg (SigV (VPar s t)))) = "(" ++ show s ++ " |-| " ++ show t ++ ")"
  show (Cont (Mrg (SigC (NComp t s)))) = "(" ++ show t ++ " * " ++ show s ++ ")"
  show (Cont (Mrg (SigC (DSum t s)))) = "(" ++ show t ++ " + " ++ show s ++ ")"
  show (Cont (Mrg (SigC (Par t s)))) = "(" ++ show t ++ " || " ++ show s ++ ")"

instance Eq (Initial (SepSig NDxCLV NDxCLC)) where
  (==) :: Initial (SepSig NDxCLV NDxCLC) -> Initial (SepSig NDxCLV NDxCLC) -> Bool
  Cont (Mrg (SigV NS)) == Cont (Mrg (SigV NS)) = True
  Cont (Mrg (SigV (NS' t))) == Cont (Mrg (SigV (NS' s))) = t==s
  Cont (Mrg (SigV (NS'' s t))) == Cont (Mrg (SigV (NS'' s' t'))) = (s == s') && (t == t')
  Cont (Mrg (SigV NK)) == Cont (Mrg (SigV NK)) = True
  Cont (Mrg ((SigV (NK' t)))) == Cont (Mrg ((SigV (NK' s)))) = t == s
  Cont (Mrg (SigV NI)) == Cont (Mrg (SigV NI)) = True
  Cont (Mrg (SigV (VPar s t))) == Cont (Mrg (SigV (VPar s' t'))) = (s == s') && (t == t')
  Cont (Mrg (SigC (NComp t s))) == Cont (Mrg (SigC (NComp t' s'))) = (t==t') && (s==s')
  Cont (Mrg (SigC (Par t s))) == Cont (Mrg (SigC (Par t' s'))) = (t==t') && (s==s')
  _ == _ = False


instance Show (InitialV NDxCLV NDxCLC) where
  show NS = "S"
  show (NS' t) = "S'(" ++ show t ++ ")"
  show (NS'' s t) = "S''(" ++ show s ++ ", " ++ show t ++ ")"
  show NK = "K"
  show (NK' t) = "K'(" ++ show t ++ ")"
  show NI = "I"
  show (VPar s t) = "(" ++ show t ++ " |-| " ++ show s ++ ")"

instance Eq (InitialV NDxCLV NDxCLC) where
  (==) :: InitialV NDxCLV NDxCLC -> InitialV NDxCLV NDxCLC -> Bool
  NS == NS = True
  (NS' t) == (NS' t') = t == t'
  (NS'' s t) == (NS'' s' t') = (s==s') && (t==t')
  NK == NK = True
  (NK' t) == (NK' t') = t==t'
  NI == NI = True
  (VPar s t) == (VPar s' t') = (s==s') && (t==t')
  _ == _ = False

instance Show (InitialC NDxCLV NDxCLC) where
  show (NComp t s) = "(" ++ show t ++ " * " ++ show s ++ ")"
  show (DSum t s) = "(" ++ show t ++ " + " ++ show s ++ ")"
  show (Par t s) = "(" ++ show t ++ " || " ++ show s ++ ")"

instance Eq (InitialC NDxCLV NDxCLC) where
  NComp t s == NComp t' s' = (t == t') && (s==s')
  DSum t s  == DSum t' s'  = (t == t') && (s==s')  
  Par t s == Par t' s' = (t == t') && (s==s')

-- The test function for the operational model of rhoVT for non-deterministic xCL.
tryEvalVT :: InitialV NDxCLV NDxCLC -> Initial (SepSig NDxCLV NDxCLC) -> Initial (SepSig NDxCLV NDxCLC)
tryEvalVT = gammaVT @_ @_ @_ @[]

-- The test function for the operational model of rhoCT for non-deterministic xCL.
tryEvalCT :: InitialC NDxCLV NDxCLC -> [Initial (SepSig NDxCLV NDxCLC)]
tryEvalCT = gammaCT @NDxCLV @NDxCLC @(->) @[] Proxy

-- The test function for the multi-step transtition function Beta for non-deterministic xCL.
tryEvalBT :: Initial (SepSig NDxCLV NDxCLC) -> [InitialV NDxCLV NDxCLC]
tryEvalBT = betahatT @NDxCLV @NDxCLC @(->) @[] Proxy

