module Benchmark where

import Data.Proxy ( Proxy(Proxy) )
import Data.Bifunctor ( Bifunctor(bimap, first, second) )
import Control.Monad (join, (<=<))
import Control.Arrow ((&&&))
import Syntax 
import HOGSOS ( tryEval )
import Separable 
import BigStep ( tryEvalZT )
import Examples
import Utils

-- Introduction:
-- We have a list of samples for every function that can be tested here, accompanying a function that can run the test on the whole function.
-- To execute the test please just run the defined function(s) in each case.
-- For each case there are functions named "test[LanguageName]Beta" and "test[LanguageName]Zeta" that run the Beta and Zeta function of the language on the list of test cases.
-- Also there is a function in most cases named "test[LanguageName]ZetaAgreement" that shows in which cases of the test list the result of applying Beta and Zeta coincide. 
-- For every case please pay attention to the type of the input arguments, when inputting them.

------------------------------------------------------------------------------
-- Testing multistep and big-step reductions for Example 2.1.
benchmarkArt :: [InitialC ArtV ArtC]
benchmarkArt = [
  F $ sigOp $ SigC $ F $ sigOp $ SigV $ G $ sigOp $ SigC Omega
  , F $ sigOp $ SigC $ F $ sigOp $ SigC $ F $ sigOp $ SigV $ G $ sigOp $ SigC Omega
  , F $ sigOp $ SigV $ G $ sigOp $ SigC Omega
  ]

testArtBeta :: [InitialV ArtV ArtC]
testArtBeta = fmap tryEvalBArt benchmarkArt

testArtZeta :: [InitialV ArtV ArtC]
testArtZeta = fmap tryEvalZArt benchmarkArt

testArtZetaAgreement :: IO ()
testArtZetaAgreement = do putStrLn $ "Example terms: " ++ show benchmarkArt;  compareLists testArtBeta testArtZeta

------------------------------------------------------------------------------
-- Testing behaviour for xCL:
-- Type: Initial XCL -> Initial XCL -> Either (Initial XCL) (Initial XCL)
-- For this case, please input a list of pairs. The second argument is the label.
-- However, for non-value terms, the second argument will not take effect. Those are silent transitions.
benchmarkxCL :: [(Initial XCL, Initial XCL)]
benchmarkxCL = [
  (sigOp K , sigOp I)
  , (sigOp $ S'' (sigOp K) (sigOp I) , sigOp S)
  , (sigOp $ Comp (sigOp $ S'' (sigOp K) (sigOp I)) (sigOp $ Comp (sigOp S) (sigOp I)) , sigOp I)
  ]

testxCLGamma :: [Either (Initial XCL) (Initial XCL)]
testxCLGamma = fmap (uncurry tryEval) benchmarkxCL

------------------------------------------------------------------------------
-- Testing operational models, multi-step transitions, and the big-step model non-deterministic xCL:
-- For this case we have different functions. So we define two separate benchmark lists.
-- For gammaV we need pairs as inputs, while for gammaC we don't need pairs.
-- Type: InitialV NDxCLV NDxCLC -> Initial (SepSig NDxCLV NDxCLC) -> [Initial (SepSig NDxCLV NDxCLC)]
benchmarkVnxCL :: [(InitialV NDxCLV NDxCLC, Initial (SepSig NDxCLV NDxCLC))]
benchmarkVnxCL = [
  (NS' $ sigOp $ SigV NK , sigOp $ SigV NS) 
  , (NS'' (sigOp $ SigV NK) (sigOp $ SigV NI)  , sigOp $ SigV NS) 
  ]

testnxCLGammaV :: [Initial (SepSig NDxCLV NDxCLC)]
testnxCLGammaV = fmap (uncurry tryEvalVT) benchmarkVnxCL

benchmarkCnxCL :: [InitialC NDxCLV NDxCLC]
benchmarkCnxCL = [
  NComp (sigOp $ SigC $ NComp (sigOp $ SigV $ VPar (sigOp $ SigV NI) (sigOp $ SigV NS)) (sigOp $ SigC $ Par (sigOp $ SigV NK) (sigOp $ SigV NK) )) (sigOp $ SigV NK)
  , NComp (sigOp $ SigC $ NComp (sigOp $ SigV $ VPar (sigOp $ SigV NI) (sigOp $ SigV NS)) (sigOp $ SigC $ Par (sigOp $ SigV NK) (sigOp $ SigV NK) )) (sigOp $ SigV NK)
  , NComp (sigOp $ SigC $ NComp (sigOp $ SigV $ VPar (sigOp $ SigV NI) (sigOp $ SigV NS)) (sigOp $ SigC $ Par (sigOp $ SigV NK) (sigOp $ SigV NK) )) (sigOp $ SigV NK)
  ]

testnxCLGammaC :: [[Initial (SepSig NDxCLV NDxCLC)]]
testnxCLGammaC = fmap tryEvalCT benchmarkCnxCL

------------------------------------------------------------------------------
-- Testing multistep and big-step reductions for non-deterministic xCL:
benchmarknxCL :: [Initial (SepSig NDxCLV NDxCLC)]
benchmarknxCL = [
  sigOp $ SigV NI
  , sigOp $ SigV (NS'' (sigOp $ SigV NK) (sigOp $ SigV NI) )
  , sigOp $ SigC $ NComp (sigOp $ SigC $ NComp (sigOp $ SigV NS) (sigOp $ SigV NK)) (sigOp $ SigV NI)
  , sigOp $ SigC $ NComp (sigOp $ SigC $ DSum (sigOp $ SigV NS) (sigOp $ SigV NK)) (sigOp $ SigV NI)
  , sigOp $ SigC $ NComp (sigOp $ SigC $ NComp (sigOp $ SigC $ DSum (sigOp $ SigV NS) (sigOp $ SigV NK)) (sigOp $ SigV NS)) (sigOp $ SigV NK)
  , sigOp $ SigC $ DSum  (sigOp $ SigC $ NComp (sigOp $ SigC $ DSum (sigOp $ SigV NK) (sigOp $ SigV NK)) (sigOp $ SigV NI)) (sigOp $ SigC $ NComp (sigOp $ SigC $ DSum (sigOp $ SigV NK) (sigOp $ SigV NK)) (sigOp $ SigV NI))
  , sigOp $ SigC $ Par (sigOp $ SigC $ NComp (sigOp $ SigC $ NComp (sigOp $ SigC $ NComp (sigOp $ SigV NK) (sigOp $ SigV NI))(sigOp $ SigV NI))(sigOp $ SigV NI))(sigOp $ SigC $ NComp (sigOp $ SigC $ NComp (sigOp $ SigV NK) (sigOp $ SigV NK)) (sigOp $ SigV NI))
  , sigOp $ SigC $ NComp (sigOp $ SigC $ NComp (sigOp $ SigV $ VPar (sigOp $ SigV NI) (sigOp $ SigV NS)) (sigOp $ SigC $ Par (sigOp $ SigV NK) (sigOp $ SigV NK) )) (sigOp $ SigV NK)
  , sigOp $ SigC $ DSum (sigOp $ SigC $ NComp (sigOp $ SigV $ VPar (sigOp $ SigV NI) (sigOp $ SigV NS)) (sigOp $ SigC $ Par (sigOp $ SigV NK) (sigOp $ SigV NK) )) (sigOp $ SigV NK)
  ]

testnxCLBeta :: [[InitialV NDxCLV NDxCLC]]
testnxCLBeta = fmap tryEvalBT benchmarknxCL

testnxCLZeta :: [[InitialV NDxCLV NDxCLC]]
testnxCLZeta = fmap tryEvalZT benchmarknxCL

testnxCLZetaAgreement :: IO ()
testnxCLZetaAgreement = do putStrLn $ "Example terms: " ++ show benchmarknxCL;  compareLists testnxCLBeta testnxCLZeta

------------------------------------------------------------------------------
-- Testing multistep and big-step reductions for CBV1:
benchmarkCBV1 :: [InitialC CBVxCLV1 CBVxCLC1]
benchmarkCBV1 = [
  Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigV Scbv1) (sigOp $ SigV Kcbv1)) (sigOp $ SigV Icbv1)
  , Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigV Scbv1) (sigOp $ SigV Kcbv1)) (sigOp $ SigV Scbv1)) (sigOp $ SigV Kcbv1)
  , Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigV Kcbv1) (sigOp $ SigV Kcbv1)) (sigOp $ SigV Icbv1)) (sigOp $ SigC $ Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigV Kcbv1) (sigOp $ SigV Kcbv1)) (sigOp $ SigV Icbv1))
  ]

testCBV1Beta :: [InitialV CBVxCLV1 CBVxCLC1]
testCBV1Beta = fmap tryEvalBCBW benchmarkCBV1

testCBV1Zeta :: [InitialV CBVxCLV1 CBVxCLC1]
testCBV1Zeta = fmap tryEvalZCBW benchmarkCBV1

testCBV1ZetaAgreement :: IO ()
testCBV1ZetaAgreement = do putStrLn $ "Example terms: " ++ show benchmarkCBV1;  compareLists testCBV1Beta testCBV1Zeta

------------------------------------------------------------------------------
-- Testing multistep and big-step reductions for CBV2:
benchmarkCBV2 :: [InitialC CBVxCLV2 CBVxCLC2]
benchmarkCBV2 = [
  Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigV Scbv2) (sigOp $ SigV Kcbv2)) (sigOp $ SigV Icbv2)
  , Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigV Scbv2) (sigOp $ SigV Kcbv2)) (sigOp $ SigV Scbv2)) (sigOp $ SigV Kcbv2)
  , Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigV Kcbv2) (sigOp $ SigV Kcbv2)) (sigOp $ SigV Icbv2)) (sigOp $ SigC $ Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigV Kcbv2) (sigOp $ SigV Kcbv2)) (sigOp $ SigV Icbv2))  
  ]

testCBV2Beta :: [InitialV CBVxCLV2 CBVxCLC2]
testCBV2Beta = fmap tryEvalBCBU benchmarkCBV2

testCBV2Zeta :: [InitialV CBVxCLV2 CBVxCLC2]
testCBV2Zeta = fmap tryEvalZCBU benchmarkCBV2

testCBV2ZetaAgreement :: IO ()
testCBV2ZetaAgreement = do putStrLn $ "Example terms: " ++ show benchmarkCBV2;  compareLists testCBV2Beta testCBV2Zeta

------------------------------------------------------------------------------
-- Testing multistep and big-step reductions for CBV3:
benchmarkCBV3 :: [InitialC CBVxCLV3 CBVxCLC3]
benchmarkCBV3 = [
  Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigV Scbv3) (sigOp $ SigV Kcbv3)) (sigOp $ SigV Icbv3)
  , Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigV Scbv3) (sigOp $ SigV Kcbv3)) (sigOp $ SigV Scbv3)) (sigOp $ SigV Kcbv3)
  , Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigV Kcbv3) (sigOp $ SigV Kcbv3)) (sigOp $ SigV Icbv3)) (sigOp $ SigC $ Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigV Kcbv3) (sigOp $ SigV Kcbv3)) (sigOp $ SigV Icbv3))  
  ]

testCBV3Beta :: [InitialV CBVxCLV3 CBVxCLC3]
testCBV3Beta = fmap tryEvalBCBV benchmarkCBV3

testCBV3Zeta :: [InitialV CBVxCLV3 CBVxCLC3]
testCBV3Zeta = fmap tryEvalZCBV benchmarkCBV3

testCBV3ZetaAgreement :: IO ()
testCBV3ZetaAgreement = do putStrLn $ "Example terms: " ++ show benchmarkCBV3; compareLists testCBV3Beta testCBV3Zeta
