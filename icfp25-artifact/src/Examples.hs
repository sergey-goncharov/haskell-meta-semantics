{-|
Module      : Examples
Description : Instantiations of operational semantics for testing

This module provides concrete instantiations of the abstract syntax and semantics to xCL and 
its variants, 

It includes:

- Example languages such as ArtV/ArtC, NDxCL, CBVxCL, and parallel variants
- Instances of `SepHOGSOS` for each language
- Pretty-printing and equality instances for terms
- Evaluation functions for testing operational semantics

These examples are used in benchmarks and serve to demonstrate the expressiveness
and correctness of the specification formats.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
module Examples where

import Data.Proxy ( Proxy(Proxy) )
import Data.Bifunctor ( Bifunctor(bimap, first, second) )
import Control.Monad (join, (<=<))
import Control.Arrow ((&&&))
import Syntax
import Separable
import BigStep ( BSSOS(zeta) )

------------------------------------------------------------------------------
-- Syntax functor, and the instantiation of the language from Example 2.1, 
-- along with some functions defined to be used in the presentation in Benchmark.hs.

newtype ArtV x = G x 
  deriving (Functor)

data ArtC x y 
  = F x 
  | Omega

instance Bifunctor ArtC where
  bimap :: (a -> b) -> (c -> d) -> ArtC a c -> ArtC b d
  bimap f _ (F x) = F (f x)
  bimap _ _ Omega = Omega

instance SepHOGSOS ArtV ArtC (->) where
  rhoV :: ArtV x -> x -> Free (SepSig ArtV ArtC) x
  rhoV (G x) = sigOp . SigC . F . Res

  rhoC :: ArtC (x, SepBeh (->) x y) x -> Free (SepSig ArtV ArtC) (Either x y)
  rhoC (F (x , BehC y)) = sigOp $ SigV $ G $ Res $ Right y
  rhoC (F (x , _)) = Res $ Left x
  rhoC Omega = sigOp $ SigC Omega

instance Show (Initial (SepSig ArtV ArtC)) where
  show :: Initial (SepSig ArtV ArtC) -> String
  show (Cont (Mrg (SigC (F x)))) = "f(" ++ show x ++ ")"
  show (Cont (Mrg (SigC Omega))) = "omega"
  show (Cont (Mrg (SigV (G x)))) = "g(" ++ show x ++ ")"

instance Eq (Initial (SepSig ArtV ArtC)) where
  (==) :: Initial (SepSig ArtV ArtC) -> Initial (SepSig ArtV ArtC) -> Bool
  Cont (Mrg (SigC (F x))) == Cont (Mrg (SigC (F y))) = x == y
  Cont (Mrg (SigC Omega)) == Cont (Mrg (SigC Omega)) = True
  Cont (Mrg (SigV (G x))) == Cont (Mrg (SigV (G y))) = x == y
  _ == _ = False

instance Show (InitialV ArtV ArtC) where
  show :: InitialV ArtV ArtC -> String
  show (G x) = "g(" ++ show x ++ ")"

instance Eq (InitialV ArtV ArtC) where
  (==) :: InitialV ArtV ArtC -> InitialV ArtV ArtC -> Bool
  (G x) == (G y) = x == y

instance Show (InitialC ArtV ArtC) where
  show :: InitialC ArtV ArtC -> String
  show (F x) = "f(" ++ show x ++ ")"
  show Omega = "omega"

instance Eq (InitialC ArtV ArtC) where
  (==) :: InitialC ArtV ArtC -> InitialC ArtV ArtC -> Bool
  F x == F y = x == y
  Omega == Omega = True
  _ == _ = False

tryEvalBArt :: InitialC ArtV ArtC -> InitialV ArtV ArtC
tryEvalBArt = beta @ArtV @ArtC @(->) Proxy 

tryEvalZArt :: InitialC ArtV ArtC -> InitialV ArtV ArtC
tryEvalZArt = zeta @(->) @ArtV @ArtC 

------------------------------------------------------------------------------
-- Syntax and behaviour functors, and the instantiation of the first version of 
-- xCL with the parallel composition from section 6.3.
data VxCLParal x 
  = SParal 
  | KParal 
  | IParal 
  | SParal' x 
  | KParal' x 
  | SParal'' x x 
  | VParal' x x
  deriving (Functor)

data CxCLParal x y 
  = CompParal x y 
  | Paral' x x

instance Bifunctor CxCLParal where
  bimap :: (a -> b) -> (c -> d) -> CxCLParal a c -> CxCLParal b d
  bimap f g (CompParal x y) = CompParal (f x) (g y)
  bimap f g (Paral' x x') = Paral' (f x) (f x')

instance Show (Initial (SepSig VxCLParal CxCLParal)) where
  show :: Initial (SepSig VxCLParal CxCLParal) -> String
  show (Cont (Mrg (SigV SParal))) = "S"
  show (Cont (Mrg (SigV (SParal' t)))) = "S'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV (SParal'' s t)))) = "S''(" ++ show s ++ "," ++ show t ++ ")"
  show (Cont (Mrg (SigV KParal))) = "K"
  show (Cont (Mrg ((SigV (KParal' t))))) = "K'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV IParal))) = "I"
  show (Cont (Mrg (SigV (VParal' s t)))) = "(" ++ show s ++ "|V|" ++ show t ++ ")"
  show (Cont (Mrg (SigC (CompParal t s)))) = "(" ++ show t ++ "." ++ show s ++ ")"
  show (Cont (Mrg (SigC (Paral' t s)))) = "(" ++ show t ++ "||" ++ show s ++ ")"

instance Eq (Initial (SepSig VxCLParal CxCLParal)) where
  (==) :: Initial (SepSig VxCLParal CxCLParal) -> Initial (SepSig VxCLParal CxCLParal) -> Bool
  Cont (Mrg (SigV SParal)) == Cont (Mrg (SigV SParal)) = True
  Cont (Mrg (SigV (SParal' t))) == Cont (Mrg (SigV (SParal' s))) = t == s
  Cont (Mrg (SigV (SParal'' s t))) == Cont (Mrg (SigV (SParal'' s' t'))) = (s == s') && (t == t')
  Cont (Mrg (SigV KParal)) == Cont (Mrg (SigV KParal)) = True
  Cont (Mrg (SigV (KParal' t))) == Cont (Mrg ((SigV (KParal' s)))) = t == s
  Cont (Mrg (SigV IParal)) == Cont (Mrg (SigV IParal)) = True
  Cont (Mrg (SigV (VParal' t s))) == Cont (Mrg (SigV (VParal' t' s'))) = (t == t') && (s == s')
  Cont (Mrg (SigC (CompParal t s))) == Cont (Mrg (SigC (CompParal t' s'))) = (t == t') && (s == s')
  Cont (Mrg (SigC (Paral' t s))) == Cont (Mrg (SigC (Paral' t' s'))) = (t == t') && (s == s')
  _ == _ = False

instance Show (InitialV VxCLParal CxCLParal) where
  show :: InitialV VxCLParal CxCLParal -> String
  show SParal = "S"
  show (SParal' t) = "S'(" ++ show t ++ ")"
  show (SParal'' s t) = "S''(" ++ show s ++ "," ++ show t ++ ")"
  show KParal = "K"
  show (KParal' t) = "K'(" ++ show t ++ ")"
  show IParal = "I"
  show (VParal' s t) = "(" ++ show s ++ "|V|" ++ show t ++ ")"

instance Eq (InitialV VxCLParal CxCLParal) where
  (==) :: InitialV VxCLParal CxCLParal -> InitialV VxCLParal CxCLParal -> Bool
  SParal == SParal = True
  (SParal' t) == (SParal' t') = t == t'
  (SParal'' s t) == (SParal'' s' t') = (s == s') && (t == t')
  KParal == KParal = True
  (KParal' t) == (KParal' t') = t == t'
  IParal == IParal = True
  (VParal' s t) == (VParal' s' t') = (s == s') && (t == t')
  _ == _ = False

instance Show (InitialC VxCLParal CxCLParal) where
  show :: InitialC VxCLParal CxCLParal -> String
  show (CompParal t s) = "(" ++ show t ++ "." ++ show s ++ ")"
  show (Paral' t s) = "(" ++ show t ++ "||" ++ show s ++ ")"

instance Eq (InitialC VxCLParal CxCLParal) where
  (==) :: InitialC VxCLParal CxCLParal -> InitialC VxCLParal CxCLParal -> Bool
  (CompParal t s) == (CompParal t' s') = (t == t') && (s == s')
  (Paral' t s) == (Paral' t' s') = (t == t') && (s == s')

instance SepHOGSOS VxCLParal CxCLParal (->) where
  rhoV :: VxCLParal x -> x -> Free (SepSig VxCLParal CxCLParal) x
  rhoV SParal = sigOp . SigV . SParal' . Res
  rhoV KParal = sigOp . SigV . KParal' . Res
  rhoV IParal = Res

  rhoV (SParal' s) = sigOp . SigV . SParal'' (Res s) . Res
  rhoV (KParal' s) = \_ -> Res s

  rhoV (SParal'' s u) = \t -> sigOp $ SigC $ CompParal (sigOp $ SigC $ CompParal (Res s) (Res t)) (sigOp $ SigC $ CompParal (Res u) (Res t))
  rhoV (VParal' s u)   = \t -> sigOp $ SigC $ Paral' (sigOp $ SigC $ CompParal (Res s) (Res t)) (sigOp $ SigC $ CompParal (Res u) (Res t))

  rhoC :: CxCLParal (x, SepBeh (->) x y) x -> Free (SepSig VxCLParal CxCLParal) (Either x y)
  rhoC (CompParal (t , BehC t') s) = sigOp $ SigC $ CompParal (Res $ Right t') (Res $ Left s)
  rhoC (CompParal (t , BehV f) s)  = Res $ Right $ f s

  rhoC (Paral' (t , BehC t') (s , BehC s')) = sigOp $ SigC $ Paral' (Res $ Right t') (Res $ Right s')
  rhoC (Paral' (t , BehV f) (s , BehC s'))  = sigOp $ SigC $ Paral' (Res $ Left t) (Res $ Right s')
  rhoC (Paral' (t , BehC t') (s , BehV g))  = sigOp $ SigC $ Paral' (Res $ Right t') (Res $ Left s)
  rhoC (Paral' (t , BehV f) (s , BehV g))   = sigOp $ SigV $ VParal' (Res $ Left t) (Res $ Left s)

tryEvalBParal :: InitialC VxCLParal CxCLParal -> InitialV VxCLParal CxCLParal
tryEvalBParal = beta @VxCLParal @CxCLParal @(->) Proxy

tryEvalZParal :: InitialC VxCLParal CxCLParal -> InitialV VxCLParal CxCLParal
tryEvalZParal = zeta @(->) @VxCLParal @CxCLParal

------------------------------------------------------------------------------
-- Syntax and behaviour functors, and the instantiation of the first version of 
-- call-by-value xCL in Section 6.4
data CBVxCLV1 x 
  = Scbv1 
  | Kcbv1 
  | Icbv1 
  | Scbv1' x 
  | Kcbv1' x 
  | Scbv1'' x x
  deriving (Functor)

data CBVxCLC1 x y 
  = Compcbv1 x x

instance Bifunctor CBVxCLC1 where
  bimap :: (a -> b) -> (c -> d) -> CBVxCLC1 a c -> CBVxCLC1 b d
  bimap f g (Compcbv1 x y) = Compcbv1 (f x) (f y)

instance Show (Initial (SepSig CBVxCLV1 CBVxCLC1)) where
  show :: Initial (SepSig CBVxCLV1 CBVxCLC1) -> String
  show (Cont (Mrg (SigV Scbv1))) = "S"
  show (Cont (Mrg (SigV (Scbv1' t)))) = "S'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV (Scbv1'' s t)))) = "S''(" ++ show s ++ "," ++ show t ++ ")"
  show (Cont (Mrg (SigV Kcbv1))) = "K"
  show (Cont (Mrg (SigV (Kcbv1' t)))) = "K'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV Icbv1))) = "I"
  show (Cont (Mrg (SigC (Compcbv1 t s)))) = "(" ++ show t ++ " . " ++ show s ++ ")"

instance Eq (Initial (SepSig CBVxCLV1 CBVxCLC1)) where
  (==) :: Initial (SepSig CBVxCLV1 CBVxCLC1) -> Initial (SepSig CBVxCLV1 CBVxCLC1) -> Bool
  Cont (Mrg (SigV Scbv1)) == Cont (Mrg (SigV Scbv1)) = True
  Cont (Mrg (SigV (Scbv1' t))) == Cont (Mrg (SigV (Scbv1' s))) = t == s
  Cont (Mrg (SigV (Scbv1'' s t))) == Cont (Mrg (SigV (Scbv1'' s' t'))) = (s == s') && (t == t')
  Cont (Mrg (SigV Kcbv1)) == Cont (Mrg (SigV Kcbv1)) = True
  Cont (Mrg (SigV (Kcbv1' t))) == Cont (Mrg (SigV (Kcbv1' s))) = t == s
  Cont (Mrg (SigV Icbv1)) == Cont (Mrg (SigV Icbv1)) = True
  Cont (Mrg (SigC (Compcbv1 t s))) == Cont (Mrg (SigC (Compcbv1 t' s'))) = (t == t') && (s == s')
  _ == _ = False

instance Show (InitialV CBVxCLV1 CBVxCLC1) where
  show :: InitialV CBVxCLV1 CBVxCLC1 -> String
  show Scbv1 = "S"
  show (Scbv1' t) = "S'(" ++ show t ++ ")"
  show (Scbv1'' s t) = "S''(" ++ show s ++ "," ++ show t ++ ")"
  show Kcbv1 = "K"
  show (Kcbv1' t) = "K'(" ++ show t ++ ")"
  show Icbv1 = "I"

instance Eq (InitialV CBVxCLV1 CBVxCLC1) where
  (==) :: InitialV CBVxCLV1 CBVxCLC1 -> InitialV CBVxCLV1 CBVxCLC1 -> Bool
  Scbv1 == Scbv1 = True
  (Scbv1' t) == (Scbv1' t') = t == t'
  (Scbv1'' s t) == (Scbv1'' s' t') = (s == s') && (t == t')
  Kcbv1 == Kcbv1 = True
  (Kcbv1' t) == (Kcbv1' t') = t == t'
  Icbv1 == Icbv1 = True
  _ == _ = False

instance Show (InitialC CBVxCLV1 CBVxCLC1) where
  show :: InitialC CBVxCLV1 CBVxCLC1 -> String
  show (Compcbv1 t s) = "(" ++ show t ++ " . " ++ show s ++ ")"

instance Eq (InitialC CBVxCLV1 CBVxCLC1) where
  (==) :: InitialC CBVxCLV1 CBVxCLC1 -> InitialC CBVxCLV1 CBVxCLC1 -> Bool
  (Compcbv1 t s) == (Compcbv1 t' s') = (t == t') && (s == s')

instance SepHOGSOS CBVxCLV1 CBVxCLC1 (->) where
  rhoV :: CBVxCLV1 x -> x -> Free (SepSig CBVxCLV1 CBVxCLC1) x
  rhoV Scbv1 = sigOp . SigV . Scbv1' . Res
  rhoV Kcbv1 = sigOp . SigV . Kcbv1' . Res
  rhoV Icbv1 = Res

  rhoV (Scbv1' s) = sigOp . SigV . Scbv1'' (Res s) . Res
  rhoV (Kcbv1' s) = \_ -> Res s

  rhoV (Scbv1'' s u) = \t -> sigOp $ SigC $ Compcbv1 (sigOp $ SigC $ Compcbv1 (Res s) (Res t)) (sigOp $ SigC $ Compcbv1 (Res u) (Res t))

  rhoC :: CBVxCLC1 (x, SepBeh (->) x y) x -> Free (SepSig CBVxCLV1 CBVxCLC1) (Either x y)
  rhoC (Compcbv1 (t , BehC t') (s , BehC _)) = sigOp $ SigC $ Compcbv1 (Res $ Right t') (Res $ Left s)
  rhoC (Compcbv1 (t , BehV _) (s , BehC s')) = sigOp $ SigC $ Compcbv1 (Res $ Left t) (Res $ Right s')
  rhoC (Compcbv1 (t , BehV f) (s , BehV _))  = Res $ Right (f s)
  rhoC (Compcbv1 (t , BehC t') (s , BehV _)) = sigOp $ SigC $ Compcbv1 (Res $ Right t') (Res $ Left s)

tryEvalBCBW :: InitialC CBVxCLV1 CBVxCLC1 -> InitialV CBVxCLV1 CBVxCLC1
tryEvalBCBW = beta @CBVxCLV1 @CBVxCLC1 @(->) Proxy 

tryEvalZCBW :: InitialC CBVxCLV1 CBVxCLC1 -> InitialV CBVxCLV1 CBVxCLC1
tryEvalZCBW = zeta @(->) @CBVxCLV1 @CBVxCLC1 

------------------------------------------------------------------------------
-- Second version of call-by-value xCL
data CBVxCLV2 x 
  = Scbv2 
  | Kcbv2 
  | Icbv2 
  | Scbv2' x 
  | Kcbv2' x 
  | Scbv2'' x x
  deriving (Functor)

data CBVxCLC2 x y 
  = Compcbv2 x x

instance Bifunctor CBVxCLC2 where
  bimap :: (a -> b) -> (c -> d) -> CBVxCLC2 a c -> CBVxCLC2 b d
  bimap f g (Compcbv2 x y) = Compcbv2 (f x) (f y)

instance Show (Initial (SepSig CBVxCLV2 CBVxCLC2)) where
  show :: Initial (SepSig CBVxCLV2 CBVxCLC2) -> String
  show (Cont (Mrg (SigV Scbv2))) = "S"
  show (Cont (Mrg (SigV (Scbv2' t)))) = "S'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV (Scbv2'' s t)))) = "S''(" ++ show s ++ "," ++ show t ++ ")"
  show (Cont (Mrg (SigV Kcbv2))) = "K"
  show (Cont (Mrg (SigV (Kcbv2' t)))) = "K'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV Icbv2))) = "I"
  show (Cont (Mrg (SigC (Compcbv2 t s)))) = "(" ++ show t ++ " . " ++ show s ++ ")"

instance Eq (Initial (SepSig CBVxCLV2 CBVxCLC2)) where
  (==) :: Initial (SepSig CBVxCLV2 CBVxCLC2) -> Initial (SepSig CBVxCLV2 CBVxCLC2) -> Bool
  Cont (Mrg (SigV Scbv2)) == Cont (Mrg (SigV Scbv2)) = True
  Cont (Mrg (SigV (Scbv2' t))) == Cont (Mrg (SigV (Scbv2' s))) = t == s
  Cont (Mrg (SigV (Scbv2'' s t))) == Cont (Mrg (SigV (Scbv2'' s' t'))) = (s == s') && (t == t')
  Cont (Mrg (SigV Kcbv2)) == Cont (Mrg (SigV Kcbv2)) = True
  Cont (Mrg (SigV (Kcbv2' t))) == Cont (Mrg ((SigV (Kcbv2' s)))) = t == s
  Cont (Mrg (SigV Icbv2)) == Cont (Mrg (SigV Icbv2)) = True
  Cont (Mrg (SigC (Compcbv2 t s))) == Cont (Mrg (SigC (Compcbv2 t' s'))) = (t == t') && (s == s')
  _ == _ = False

instance Show (InitialV CBVxCLV2 CBVxCLC2) where
  show :: InitialV CBVxCLV2 CBVxCLC2 -> String
  show Scbv2 = "S"
  show (Scbv2' t) = "S'(" ++ show t ++ ")"
  show (Scbv2'' s t) = "S''(" ++ show s ++ "," ++ show t ++ ")"
  show Kcbv2 = "K"
  show (Kcbv2' t) = "K'(" ++ show t ++ ")"
  show Icbv2 = "I"

instance Eq (InitialV CBVxCLV2 CBVxCLC2) where
  (==) :: InitialV CBVxCLV2 CBVxCLC2 -> InitialV CBVxCLV2 CBVxCLC2 -> Bool
  Scbv2 == Scbv2 = True
  (Scbv2' t) == (Scbv2' t') = t == t'
  (Scbv2'' s t) == (Scbv2'' s' t') = (s == s') && (t == t')
  Kcbv2 == Kcbv2 = True
  (Kcbv2' t) == (Kcbv2' t') = t == t'
  Icbv2 == Icbv2 = True
  _ == _ = False

instance Show (InitialC CBVxCLV2 CBVxCLC2) where
  show :: InitialC CBVxCLV2 CBVxCLC2 -> String
  show (Compcbv2 t s) = "(" ++ show t ++ "." ++ show s ++ ")"

instance Eq (InitialC CBVxCLV2 CBVxCLC2) where
  (==) :: InitialC CBVxCLV2 CBVxCLC2 -> InitialC CBVxCLV2 CBVxCLC2 -> Bool
  (Compcbv2 t s) == (Compcbv2 t' s') = (t == t') && (s == s')

instance SepHOGSOS CBVxCLV2 CBVxCLC2 (->) where
  rhoV :: CBVxCLV2 x -> x -> Free (SepSig CBVxCLV2 CBVxCLC2) x
  rhoV Scbv2 = sigOp . SigV . Scbv2' . Res
  rhoV Kcbv2 = sigOp . SigV . Kcbv2' . Res
  rhoV Icbv2 = Res

  rhoV (Scbv2' s) = sigOp . SigV . Scbv2'' (Res s) . Res
  rhoV (Kcbv2' s) = \_ -> Res s

  rhoV (Scbv2'' s u) = \t -> sigOp $ SigC $ Compcbv2 (sigOp $ SigC $ Compcbv2 (Res s) (Res t)) (sigOp $ SigC $ Compcbv2 (Res u) (Res t))

  rhoC :: CBVxCLC2 (x, SepBeh (->) x y) x -> Free (SepSig CBVxCLV2 CBVxCLC2) (Either x y)
  rhoC (Compcbv2 (t , BehC t') (s , BehC s')) = sigOp $ SigC $ Compcbv2 (Res $ Right t') (Res $ Right s')
  rhoC (Compcbv2 (t , BehV _) (s , BehC s'))  = sigOp $ SigC $ Compcbv2 (Res $ Left t) (Res $ Right s')
  rhoC (Compcbv2 (t , BehC t') (s , BehV _))  = sigOp $ SigC $ Compcbv2 (Res $ Right t') (Res $ Left s)
  rhoC (Compcbv2 (t , BehV f) (s , _)) = Res $ Right (f s)

tryEvalBCBU :: InitialC CBVxCLV2 CBVxCLC2 -> InitialV CBVxCLV2 CBVxCLC2
tryEvalBCBU = beta @CBVxCLV2 @CBVxCLC2 @(->) Proxy

tryEvalZCBU :: InitialC CBVxCLV2 CBVxCLC2 -> InitialV CBVxCLV2 CBVxCLC2
tryEvalZCBU = zeta @(->) @CBVxCLV2 @CBVxCLC2

------------------------------------------------------------------------------
-- Third version of call-by-value xCL
data CBVxCLV3 x 
  = Scbv3 
  | Kcbv3 
  | Icbv3 
  | Scbv3' x 
  | Kcbv3' x 
  | Scbv3'' x x
  deriving (Functor)

data CBVxCLC3 x y 
  = Compcbv3 x y 
  | TCompcbv3 x y 
  | RCompcbv3 y x

instance Bifunctor CBVxCLC3 where
  bimap :: (a -> b) -> (c -> d) -> CBVxCLC3 a c -> CBVxCLC3 b d
  bimap f g (Compcbv3 x y) = Compcbv3 (f x) (g y)
  bimap f g (TCompcbv3 x y) = TCompcbv3 (f x) (g y)
  bimap f g (RCompcbv3 x y) = RCompcbv3 (g x) (f y)

instance Show (Initial (SepSig CBVxCLV3 CBVxCLC3)) where
  show :: Initial (SepSig CBVxCLV3 CBVxCLC3) -> String
  show (Cont (Mrg (SigV Scbv3))) = "S"
  show (Cont (Mrg (SigV (Scbv3' t)))) = "S'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV (Scbv3'' s t)))) = "S''(" ++ show s ++ "," ++ show t ++ ")"
  show (Cont (Mrg (SigV Kcbv3))) = "K"
  show (Cont (Mrg ((SigV (Kcbv3' t))))) = "K'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV Icbv3))) = "I"
  show (Cont (Mrg (SigC (Compcbv3 t s)))) = "(" ++ show t ++ "." ++ show s ++ ")"
  show (Cont (Mrg (SigC (TCompcbv3 t s)))) = "(" ++ show t ++ ".'" ++ show s ++ ")"
  show (Cont (Mrg (SigC (RCompcbv3 t s)))) = "(" ++ show t ++ ".''" ++ show s ++ ")"

instance Eq (Initial (SepSig CBVxCLV3 CBVxCLC3)) where
  (==) :: Initial (SepSig CBVxCLV3 CBVxCLC3) -> Initial (SepSig CBVxCLV3 CBVxCLC3) -> Bool
  Cont (Mrg (SigV Scbv3)) == Cont (Mrg (SigV Scbv3)) = True
  Cont (Mrg (SigV (Scbv3' t))) == Cont (Mrg (SigV (Scbv3' s))) = t == s
  Cont (Mrg (SigV (Scbv3'' s t))) == Cont (Mrg (SigV (Scbv3'' s' t'))) = (s == s') && (t == t')
  Cont (Mrg (SigV Kcbv3)) == Cont (Mrg (SigV Kcbv3)) = True
  Cont (Mrg (SigV (Kcbv3' t))) == Cont (Mrg ((SigV (Kcbv3' s)))) = t == s
  Cont (Mrg (SigV Icbv3)) == Cont (Mrg (SigV Icbv3)) = True
  Cont (Mrg (SigC (Compcbv3 t s))) == Cont (Mrg (SigC (Compcbv3 t' s'))) = (t == t') && (s == s')
  Cont (Mrg (SigC (TCompcbv3 t s))) == Cont (Mrg (SigC (TCompcbv3 t' s'))) = (t == t') && (s == s')
  Cont (Mrg (SigC (RCompcbv3 t s))) == Cont (Mrg (SigC (RCompcbv3 t' s'))) = (t == t') && (s == s')
  _ == _ = False

instance Show (InitialV CBVxCLV3 CBVxCLC3) where
  show :: InitialV CBVxCLV3 CBVxCLC3 -> String
  show Scbv3 = "S"
  show (Scbv3' t) = "S'(" ++ show t ++ ")"
  show (Scbv3'' s t) = "S''(" ++ show s ++ "," ++ show t ++ ")"
  show Kcbv3 = "K"
  show (Kcbv3' t) = "K'(" ++ show t ++ ")"
  show Icbv3 = "I"

instance Eq (InitialV CBVxCLV3 CBVxCLC3) where
  (==) :: InitialV CBVxCLV3 CBVxCLC3 -> InitialV CBVxCLV3 CBVxCLC3 -> Bool
  Scbv3 == Scbv3 = True
  (Scbv3' t) == (Scbv3' t') = t == t'
  (Scbv3'' s t) == (Scbv3'' s' t') = (s == s') && (t == t')
  Kcbv3 == Kcbv3 = True
  (Kcbv3' t) == (Kcbv3' t') = t == t'
  Icbv3 == Icbv3 = True
  _ == _ = False

instance Show (InitialC CBVxCLV3 CBVxCLC3) where
  show :: InitialC CBVxCLV3 CBVxCLC3 -> String
  show (Compcbv3 t s)  = "(" ++ show t ++ "." ++ show s ++ ")"
  show (TCompcbv3 t s) = "(" ++ show t ++ ".'" ++ show s ++ ")"
  show (RCompcbv3 t s) = "(" ++ show t ++ ".''" ++ show s ++ ")"

instance Eq (InitialC CBVxCLV3 CBVxCLC3) where
  (==) :: InitialC CBVxCLV3 CBVxCLC3 -> InitialC CBVxCLV3 CBVxCLC3 -> Bool
  Compcbv3 t s  == Compcbv3 t' s'  = (t == t') && (s == s')
  RCompcbv3 t s == RCompcbv3 t' s' = (t == t') && (s == s')
  TCompcbv3 t s == TCompcbv3 t' s' = (t == t') && (s == s')

instance SepHOGSOS CBVxCLV3 CBVxCLC3 (->) where
  rhoV :: CBVxCLV3 x -> x -> Free (SepSig CBVxCLV3 CBVxCLC3) x
  rhoV Scbv3 = sigOp . SigV . Scbv3' . Res
  rhoV Kcbv3 = sigOp . SigV . Kcbv3' . Res
  rhoV Icbv3 = Res

  rhoV (Scbv3' s) = sigOp . SigV . Scbv3'' (Res s) . Res
  rhoV (Kcbv3' s) = \t -> Res s

  rhoV (Scbv3'' s u) = \t -> sigOp $ SigC $ Compcbv3 (sigOp $ SigC $ Compcbv3 (Res s) (Res t)) (sigOp $ SigC $ Compcbv3 (Res u) (Res t))

  rhoC :: CBVxCLC3 (x, SepBeh (->) x y) x -> Free (SepSig CBVxCLV3 CBVxCLC3) (Either x y)
  rhoC (Compcbv3 (t , BehC t') s) = sigOp $ SigC $ Compcbv3 (Res $ Right t') (Res $ Left s)
  rhoC (Compcbv3 (t , _) s) = sigOp $ SigC $ RCompcbv3 (Res $ Left t) (Res $ Left s)

  rhoC (RCompcbv3 t (s , BehC s')) = sigOp $ SigC $ RCompcbv3 (Res $ Left t) (Res $ Right s')
  rhoC (RCompcbv3 t (s , _)) = sigOp $ SigC $ TCompcbv3 (Res $ Left t) (Res $ Left s)

  rhoC (TCompcbv3 (t , BehC t') s) = sigOp $ SigC $ TCompcbv3 (Res $ Right t') (Res $ Left s)
  rhoC (TCompcbv3 (t , BehV f) s) = Res $ Right (f s)

tryEvalBCBV :: InitialC CBVxCLV3 CBVxCLC3 -> InitialV CBVxCLV3 CBVxCLC3
tryEvalBCBV = beta @CBVxCLV3 @CBVxCLC3 @(->) Proxy

tryEvalZCBV :: InitialC CBVxCLV3 CBVxCLC3 -> InitialV CBVxCLV3 CBVxCLC3
tryEvalZCBV = zeta @(->) @CBVxCLV3 @CBVxCLC3