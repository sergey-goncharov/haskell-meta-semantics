{-|

Module      : Examples
Description : Examples of languages and operational semantics in separated HO-GSOS format

This module provides concrete instantiations of the abstract syntax and semantics to xCL and 
its variants. It includes:

- Example languages such as ArtV/ArtC, NDxCL, CBVxCL, and variants wil parallel composition
- Instances of `SepHOGSOS` for each language
- Pretty-printing and equality instances for terms
- Evaluation functions for testing operational semantics

These examples are used in benchmarks (``Benchmarks.hs``) and serve to demonstrate the expressiveness
of the separated HO-GSOS framework and to test the translation from small-step to big-step semantics.

-}

{-# LANGUAGE AllowAmbiguousTypes #-}
module Examples where

import Data.Proxy ( Proxy(Proxy) )
import Data.Bifunctor ( Bifunctor(bimap, first, second) )

import Control.Monad (join, (<=<))
import Control.Arrow ((&&&))

import Syntax
import Behaviour (MixFunctor(..), Beh (Eval, Red), SepBehT, SepBeh, SepBehT(..), SepBeh(..))
import HOGSOS
import Separable
import BigStep 

-------------------------------------------------------------------------------
-- SECTION 1: ArtV/ArtC Example Language (Exp. 2.1)
-------------------------------------------------------------------------------

newtype ArtV x = G x 
  deriving (Functor)

data ArtC x y = F x | Omega

instance Functor (ArtC a) where
  fmap :: (b -> c) -> ArtC a b -> ArtC a c
  fmap f (F x) = F x
  fmap _ Omega = Omega

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
  show (Cont (Mrg (SigC Omega))) = "Ω"
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

-- Test function for ArtV/ArtC

tryEvalBArt :: InitialC ArtV ArtC -> InitialV ArtV ArtC
tryEvalBArt = beta @ArtV @ArtC @(->) Proxy 

tryEvalZArt :: InitialC ArtV ArtC -> InitialV ArtV ArtC
tryEvalZArt = zeta @(->) @ArtV @ArtC 

-------------------------------------------------------------------------------
-- SECTION 2: xCL (Extended Combinatory Logic)
-------------------------------------------------------------------------------

-- | Syntax for xCL (Display (1)).
data XCL' x y 
  = S 
  | K 
  | I 
  | S' x 
  | K' x 
  | S'' x x 
  | Comp x y 

type XCL = Mrg XCL' -- XCL as a functor (an instance of Sigma in the paper).

-- | Value part of the xCL syntax (Exp. 3.3).
data XCLV x 
  = Sv 
  | Kv 
  | Iv 
  | S'v x 
  | K'v x 
  | S''v x x 
  deriving (Functor)

-- | Computation part of the xCL syntax (Exp. 3.3).
data XCLC x y = Compc x y 

instance Functor (XCLC x) where
  fmap :: (a -> b) -> XCLC x a -> XCLC x b
  fmap f (Compc x y) = Compc x (f y)

instance Bifunctor XCLC where
  bimap :: (a -> b) -> (c -> d) -> XCLC a c -> XCLC b d
  bimap f g (Compc x y) = Compc (f x) (g y)

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

-- HO-GSOS instance for xCL (Sec 2.1., didactic purpose only)
instance HOGSOS XCL' Beh where
  rho :: XCL' (x, Beh x y) x -> Beh x (Free XCL (Either x y))
  rho S = Eval $ sigOp . S' . Res . Left
  rho K = Eval $ sigOp . K' . Res . Left
  rho I = Eval $ Res . Left
  rho (S' (s, _)) = Eval $ \t -> sigOp $ S'' (Res $ Left s) (Res $ Left t)
  rho (K' (s, _)) = Eval $ const $ Res $ Left s
  rho (S'' (s, _) (u, _)) = Eval $ \t -> sigOp $ Comp (sigOp $ Comp (Res $ Left s) (Res $ Left t)) 
                                                      (sigOp $ Comp (Res $ Left u) (Res $ Left t))
  rho (Comp (_, Red s) u) = Red $ sigOp $ Comp (Res $ Right s) (Res $ Left u)
  rho (Comp (_, Eval f) u) = Red $ Res (Right $ f u)

-- Test function for xCL
tryEval :: Initial XCL -> Initial XCL -> Either (Initial XCL) (Initial XCL)
tryEval t s = case gamma t of
  Eval f -> Left $ f s
  Red x  -> Right x

instance Show (Initial XCL) where
  show :: Initial XCL -> String
  show (Cont (Mrg S)) = "S"
  show (Cont (Mrg (S' t))) = "(S'" ++ show t ++ ")"
  show (Cont (Mrg (S'' s t))) = "(S''" ++ show s ++ ", " ++ show t ++ ")"
  show (Cont (Mrg K)) = "K"
  show (Cont (Mrg (K' t))) = "(K'" ++ show t ++ ")"
  show (Cont (Mrg I)) = "I"
  show (Cont (Mrg (Comp t s))) = "(" ++ show t ++ " ⋅ " ++ show s ++ ")"
  
-- SepHOGSOS instance for xCL (Exp. 3.3)
instance SepHOGSOS XCLV XCLC (->) where
  rhoV :: XCLV x -> x -> Free (SepSig XCLV XCLC) x
  rhoV Sv = sigOp . SigV . S'v . Res
  rhoV Kv = sigOp . SigV . K'v . Res
  rhoV Iv = Res
  rhoV (S'v t) = sigOp . SigV . S''v (Res t) . Res
  rhoV (K'v t) = const (Res t)
  rhoV (S''v t s) = \u -> sigOp $ SigC $ Compc (sigOp $ SigC $ Compc (Res t) (Res u)) 
                                               (sigOp $ SigC $ Compc (Res s) (Res u))
 
  rhoC :: XCLC (x, SepBeh (->) x y) x -> Free (SepSig XCLV XCLC) (Either x y)
  rhoC (Compc (_, BehC s) u) = sigOp (SigC $ Compc (Res $ Right s) (Res $ Left u))
  rhoC (Compc (_, BehV f) u) = Res (Right $ f u) 

instance Show (Initial (SepSig XCLV XCLC)) where
  show :: Initial (SepSig XCLV XCLC) -> String
  show (Cont (Mrg (SigV Sv))) = "S"
  show (Cont (Mrg (SigV (S'v t)))) = "S'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV (S''v s t)))) = "S''(" ++ show s ++ ", " ++ show t ++ ")"
  show (Cont (Mrg (SigV Kv))) = "K"
  show (Cont (Mrg ((SigV (K'v t))))) = "K'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV Iv))) = "I"
  show (Cont (Mrg (SigC (Compc t s)))) = "(" ++ show t ++ " ⋅ " ++ show s ++ ")"

instance Eq (Initial (SepSig XCLV XCLC)) where
  (==) :: Initial (SepSig XCLV XCLC) -> Initial (SepSig XCLV XCLC) -> Bool
  Cont (Mrg (SigV Sv)) == Cont (Mrg (SigV Sv)) = True
  Cont (Mrg (SigV Kv)) == Cont (Mrg (SigV Kv)) = True
  Cont (Mrg (SigV Iv)) == Cont (Mrg (SigV Iv)) = True
  Cont (Mrg (SigV (S'v t))) == Cont (Mrg (SigV (S'v s))) = t == s
  Cont (Mrg (SigV (K'v t))) == Cont (Mrg (SigV (K'v s))) = t == s
  Cont (Mrg (SigV (S''v s t)))  == Cont (Mrg (SigV (S''v s' t'))) = (s == s') && (t == t')
  Cont (Mrg (SigC (Compc t s))) == Cont (Mrg (SigC (Compc t' s'))) = (t==t') && (s==s')
  _ == _ = False

instance Show (InitialV XCLV XCLC) where
  show Sv = "S"
  show (S'v t) = "S'(" ++ show t ++ ")"
  show (S''v s t) = "S''(" ++ show s ++ ", " ++ show t ++ ")"
  show Kv = "K"
  show (K'v t) = "K'(" ++ show t ++ ")"
  show Iv = "I"
 
instance Eq (InitialV XCLV XCLC) where
  (==) :: InitialV XCLV XCLC -> InitialV XCLV XCLC -> Bool
  Sv == Sv = True
  (S'v t) == (S'v t') = t == t'
  (S''v s t) == (S''v s' t') = (s==s') && (t==t')
  Kv == Kv = True
  (K'v t) == (K'v t') = t==t'
  Iv == Iv = True
  _ == _ = False

instance Show (InitialC XCLV XCLC) where
  show (Compc t s) = "(" ++ show t ++ " ⋅ " ++ show s ++ ")"

instance Eq (InitialC XCLV XCLC) where
  Compc t s == Compc t' s' = (t == t') && (s==s')

-- Test functions for XCL
tryEvalVxCL :: InitialV XCLV XCLC -> Initial (SepSig XCLV XCLC) -> Initial (SepSig XCLV XCLC)
tryEvalVxCL = gammaV

tryEvalCxCL :: InitialC XCLV XCLC -> Initial (SepSig XCLV XCLC)
tryEvalCxCL = gammaC @XCLV @XCLC @(->) Proxy

tryEvalBxCL :: Initial (SepSig XCLV XCLC) -> InitialV XCLV XCLC
tryEvalBxCL = betahat @XCLV @XCLC @(->) Proxy

tryEvalZxCL :: Initial (SepSig XCLV XCLC) -> InitialV XCLV XCLC
tryEvalZxCL = zetahat @(->) @XCLV @XCLC 

-------------------------------------------------------------------------------
-- SECTION 3: Non-deterministic xCL (NDxCL), Sec. 6.3
-------------------------------------------------------------------------------

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

-- SepHOGSOST instance for NDxCL
instance SepHOGSOST NDxCLV NDxCLC (->) [] where
  rhoVT :: NDxCLV x -> x -> Free (SepSig NDxCLV NDxCLC) x
  rhoVT NS = sigOp . SigV . NS' . Res
  rhoVT NK = sigOp . SigV . NK' . Res
  rhoVT NI = Res
  rhoVT (NS' t) = sigOp . SigV . NS'' (Res t) . Res
  rhoVT (NK' t) = const (Res t)
  rhoVT (NS'' t s) = \u -> sigOp $ SigC $ NComp (sigOp $ SigC $ NComp (Res t) (Res u)) 
                                                (sigOp $ SigC $ NComp (Res s) (Res u))
  rhoVT (VPar t s) = \u -> sigOp $ SigC $ Par (sigOp $ SigC $ NComp (Res t) (Res u)) (sigOp $ SigC $ NComp (Res s) (Res u))

  rhoCT :: NDxCLC (x, SepBehT [] (->) x y) x -> [Free (SepSig NDxCLV NDxCLC) (Either x y)]
  rhoCT (NComp (s, BehCT (s' : l)) t) = sigOp (SigC $ NComp (Res $ Right s') (Res $ Left t)) : rhoCT @_ @_ @(->) (NComp (s, BehCT l) t)
  rhoCT (NComp (s, BehVT f) t)  = [ Res (Right $ f t) ]
  rhoCT (NComp (s, BehCT [] ) t) = []

  rhoCT (DSum s t) = [Res $ Left s, Res $ Left t]
 
  rhoCT (Par (s, BehCT (s' : k)) (t, BehCT (t' : l))) = [sigOp $ SigC $ Par (Res $ Right s') (Res $ Right t')] 
    ++ rhoCT @_ @_ @(->) (Par (s, BehCT (s' : k)) (t, BehCT l)) 
    ++ rhoCT @_ @_ @(->) (Par (s, BehCT k) (t, BehCT (t' :  l)))
  
  rhoCT (Par (s, BehVT f) (t, BehCT (t' : l)))  = [sigOp $ SigC $ Par (Res $ Left s) (Res $ Right t')] 
    ++ rhoCT @_ @_ @(->) (Par (s, BehVT f) (t, BehCT l)) 
  rhoCT (Par (s, BehCT (s' : k)) (t, BehVT g))  = [sigOp $ SigC $ Par (Res $ Right s') (Res $ Left t)] 
    ++ rhoCT @_ @_ @(->) (Par (s, BehCT k) (t, BehVT g))
  rhoCT (Par (s, BehVT _) (t, BehVT _))  = [sigOp $ SigV $ VPar (Res $ Left s) (Res $ Left t)]
  rhoCT (Par (_, BehCT []) _) = []
  rhoCT (Par _ (t, BehCT [])) = []

  chi :: NDxCLC [x] y -> [NDxCLC x y]
  chi (NComp (x : xs) y) = NComp x y : chi @NDxCLV @NDxCLC @(->) @[] (NComp xs y)
  chi (NComp [] y) = []
  chi (DSum x y) = [DSum x y]
  chi (Par (s : k) (t : l)) = [Par s t] ++ chi @NDxCLV @NDxCLC @(->) @[] (Par (s : k) l) ++ chi @NDxCLV @NDxCLC @(->) @[] (Par k (t : l))
  chi (Par [] l) = []
  chi (Par k []) = []

instance Show (Initial (SepSig NDxCLV NDxCLC)) where
  show :: Initial (SepSig NDxCLV NDxCLC) -> String
  show (Cont (Mrg (SigV NS))) = "S"
  show (Cont (Mrg (SigV (NS' t)))) = "S'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV (NS'' s t)))) = "S''(" ++ show s ++ ", " ++ show t ++ ")"
  show (Cont (Mrg (SigV NK))) = "K"
  show (Cont (Mrg ((SigV (NK' t))))) = "K'(" ++ show t ++ ")"
  show (Cont (Mrg (SigV NI))) = "I"
  show (Cont (Mrg (SigV (VPar s t)))) = "(" ++ show s ++ " ⊔ " ++ show t ++ ")"
  show (Cont (Mrg (SigC (NComp t s)))) = "(" ++ show t ++ " ⋅ " ++ show s ++ ")"
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
  show (VPar s t) = "(" ++ show t ++ " ⊔ " ++ show s ++ ")"

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
  show (NComp t s) = "(" ++ show t ++ " ⋅ " ++ show s ++ ")"
  show (DSum t s) = "(" ++ show t ++ " + " ++ show s ++ ")"
  show (Par t s) = "(" ++ show t ++ " || " ++ show s ++ ")"

instance Eq (InitialC NDxCLV NDxCLC) where
  NComp t s == NComp t' s' = (t == t') && (s==s')
  DSum t s  == DSum t' s'  = (t == t') && (s==s')  
  Par t s == Par t' s' = (t == t') && (s==s')

-- Test functions for NDxCL
tryEvalVT :: InitialV NDxCLV NDxCLC -> Initial (SepSig NDxCLV NDxCLC) -> Initial (SepSig NDxCLV NDxCLC)
tryEvalVT = gammaVT @_ @_ @_ @[]

tryEvalCT :: InitialC NDxCLV NDxCLC -> [Initial (SepSig NDxCLV NDxCLC)]
tryEvalCT = gammaCT @NDxCLV @NDxCLC @(->) @[] Proxy

tryEvalBT :: Initial (SepSig NDxCLV NDxCLC) -> [InitialV NDxCLV NDxCLC]
tryEvalBT = betahatT @NDxCLV @NDxCLC @(->) @[] Proxy

tryEvalZT :: Initial (SepSig NDxCLV NDxCLC) -> [InitialV NDxCLV NDxCLC]
tryEvalZT = zetahatT @(->) @NDxCLV @NDxCLC @[]

-------------------------------------------------------------------------------
-- SECTION 4: Call-by-Value xCL (CBVxCLV1, CBVxCLC1), Sec 6.4., with (a) rule
-------------------------------------------------------------------------------

data CBVxCLV1 x 
  = Scbv1 
  | Kcbv1 
  | Icbv1 
  | Scbv1' x 
  | Kcbv1' x 
  | Scbv1'' x x
  deriving (Functor)

data CBVxCLC1 x y = Compcbv1 x x

instance Functor (CBVxCLC1 a) where
  fmap :: (b -> c) -> CBVxCLC1 a b -> CBVxCLC1 a c
  fmap f (Compcbv1 x y) = Compcbv1 x y
  
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
  show (Cont (Mrg (SigC (Compcbv1 t s)))) = "(" ++ show t ++ " ⋅ " ++ show s ++ ")"

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
  show (Compcbv1 t s) = "(" ++ show t ++ " ⋅ " ++ show s ++ ")"

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
  rhoC (Compcbv1 (t , BehC t') (s , _)) = sigOp $ SigC $ Compcbv1 (Res $ Right t') (Res $ Left s)
  rhoC (Compcbv1 (t , BehV _) (s , BehC s')) = sigOp $ SigC $ Compcbv1 (Res $ Left t) (Res $ Right s')
  rhoC (Compcbv1 (t , BehV f) (s , BehV _))  = Res $ Right (f s)

tryEvalBCBW :: InitialC CBVxCLV1 CBVxCLC1 -> InitialV CBVxCLV1 CBVxCLC1
tryEvalBCBW = beta @CBVxCLV1 @CBVxCLC1 @(->) Proxy 

tryEvalZCBW :: InitialC CBVxCLV1 CBVxCLC1 -> InitialV CBVxCLV1 CBVxCLC1
tryEvalZCBW = zeta @(->) @CBVxCLV1 @CBVxCLC1 

-------------------------------------------------------------------------------
-- SECTION 5: Call-by-Value xCL (CBVxCLV2, CBVxCLC2), Sec 6.4., with (a1), (a2) rules
-------------------------------------------------------------------------------

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

instance Functor (CBVxCLC2 a) where
  fmap :: (b -> c) -> CBVxCLC2 a b -> CBVxCLC2 a c
  fmap f (Compcbv2 x y) = Compcbv2 x y

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
  show (Cont (Mrg (SigC (Compcbv2 t s)))) = "(" ++ show t ++ " ⋅ " ++ show s ++ ")"

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
  show (Compcbv2 t s) = "(" ++ show t ++ " ⋅ " ++ show s ++ ")"

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

-------------------------------------------------------------------------------
-- SECTION 6: Call-by-Value xCL (CBVxCLV3, CBVxCLC3), Sec 6.4., with additional composition operators
-------------------------------------------------------------------------------

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

instance Functor (CBVxCLC3 a) where
  fmap :: (b -> c) -> CBVxCLC3 a b -> CBVxCLC3 a c
  fmap f (Compcbv3 x y) = Compcbv3 x (f y)
  fmap f (TCompcbv3 x y) = TCompcbv3 x (f y)
  fmap f (RCompcbv3 x y) = RCompcbv3 (f x) y

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
  show (Cont (Mrg (SigC (Compcbv3 t s)))) = "(" ++ show t ++ " ⋅ " ++ show s ++ ")"
  show (Cont (Mrg (SigC (TCompcbv3 t s)))) = "(" ++ show t ++ " ⋅' " ++ show s ++ ")"
  show (Cont (Mrg (SigC (RCompcbv3 t s)))) = "(" ++ show t ++ " ⋅'' " ++ show s ++ ")"

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
  show (Compcbv3 t s)  = "(" ++ show t ++ " ⋅ " ++ show s ++ ")"
  show (TCompcbv3 t s) = "(" ++ show t ++ " ⋅' " ++ show s ++ ")"
  show (RCompcbv3 t s) = "(" ++ show t ++ " ⋅'' " ++ show s ++ ")"

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