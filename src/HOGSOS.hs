module HOGSOS where

import Data.Bifunctor ( Bifunctor(first) )
import Control.Arrow ((&&&)) -- For arrows to a product object.
import Syntax ( Initial, Free(..), XCL, Mrg(..), XCL'(..), sigOp )
import Behaviour ( Beh(..), MixFunctor(mx_second) )

-- Definitions related to HoGSOS laws:

-- HoGSOS law.
class (Bifunctor s, MixFunctor b) => HOGSOS s b where
  rho :: s (x, b x y) x -> b x (Free (Mrg s) (Either x y))

  -- Operational model.
  gamma :: Initial (Mrg s) -> b (Initial (Mrg s)) (Initial (Mrg s))
  gamma (Cont (Mrg t)) = mx_second (>>= nabla) $ rho $ first (id &&& gamma) t
    where nabla = either id id

-- Instantiating the operational semantics of xCL as a HoGSOS law.
instance HOGSOS XCL' Beh where
  rho :: XCL' (x, Beh x y) x -> Beh x (Free XCL (Either x y))
  rho S = Eval $ sigOp . S' . Res . Left
  rho K = Eval $ sigOp . K' . Res . Left
  rho I = Eval $ Res . Left
  rho (S' (s, _)) = Eval $ \t -> sigOp $ S'' (Res $ Left s) (Res $ Left t)
  rho (K' (s, _)) = Eval $ const $ Res $ Left s
  rho (S'' (s, _) (u, _)) = Eval $ \t -> sigOp $ Comp (sigOp $ Comp (Res $ Left s) (Res $ Left t)) (sigOp $ Comp (Res $ Left u) (Res $ Left t))
  rho (Comp (_, Red s) u) = Red $ sigOp $ Comp (Res $ Right s) (Res $ Left u)
  rho (Comp (_, Eval f) u) = Red $ Res (Right $ f u)

-- A function for testing the specification.
tryEval :: Initial XCL -> Initial XCL -> Either (Initial XCL) (Initial XCL)
tryEval t s = case gamma t of
  Eval f -> Left $ f s
  Red x  -> Right x

