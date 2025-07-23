{-|

Module      : Tests
Description : Tests for testing examples from ``Examples.hs``

This module defines Test terms and test functions for evaluating:

- Multi-step semantics (`beta`)
- Big-step semantics (`zeta`)
- Agreement between the two semantics (Thm 5.4)

It includes test suites for various languages (e.g., Art, NDxCL, CBVxCL variants),
and uses `equalityTests` from `Utils` to report semantic agreement.

Each language has:
- A list of sample terms
- Functions named `test[LanguageName]Beta` and `test[LanguageName]Zeta` to run the respective semantics
- A function `test[LanguageName]ZetaAgreement` (when applicable) to compare the results of `beta` and `zeta`

To run a test, simply evaluate the corresponding function in GHCi. 
Ensure the input types match the expected signatures for each test case.

-}

module Tests where

import Data.Proxy ( Proxy(Proxy) )
import Data.Bifunctor ( Bifunctor(bimap, first, second) )

import Syntax 
import Separable 
import Examples
import Utils

-------------------------------------------------------------------------------
-- SECTION 1: ArtV/ArtC Example Language
-------------------------------------------------------------------------------

testArt :: [InitialC ArtV ArtC]
testArt = [
  F $ sigOp $ SigC $ F $ sigOp $ SigV $ G $ sigOp $ SigC Omega
  , F $ sigOp $ SigC $ F $ sigOp $ SigC $ F $ sigOp $ SigV $ G $ sigOp $ SigC Omega
  , F $ sigOp $ SigV $ G $ sigOp $ SigC Omega
  ]

testArtBeta :: [InitialV ArtV ArtC]
testArtBeta = fmap tryEvalBArt testArt

testArtZeta :: [InitialV ArtV ArtC]
testArtZeta = fmap tryEvalZArt testArt

testArtZetaAgreement :: IO ()
testArtZetaAgreement = do
  putStrLn $ "Example terms: " ++ show testArt
  equalityTests testArtBeta testArtZeta [False, False, True]

-------------------------------------------------------------------------------
-- SECTION 2: xCL (Extended Combinatory Logic)
-------------------------------------------------------------------------------

testxCL :: [Initial (SepSig XCLV XCLC)]
testxCL = [
  sigOp $ SigV Kv 
  , sigOp $ SigV $ S''v (sigOp $ SigV Kv) (sigOp $ SigV Iv) 
  , sigOp $ SigC $ Compc (sigOp $ SigV $ S''v (sigOp $ SigV Kv) (sigOp $ SigV Iv)) (sigOp $ SigC $ Compc (sigOp $ SigV Sv) (sigOp $ SigV Iv)) 
  ]

testxCLBeta :: [InitialV XCLV XCLC]
testxCLBeta = fmap tryEvalBxCL testxCL

testxCLZeta :: [InitialV XCLV XCLC]
testxCLZeta = fmap tryEvalZxCL testxCL

testxCLZetaAgreement :: IO ()
testxCLZetaAgreement = do
  putStrLn $ "Example terms: " ++ show testxCL
  equalityTests testxCLBeta testxCLZeta (fmap (const True) testxCL)

-------------------------------------------------------------------------------
-- SECTION 3: Non-deterministic xCL 
-------------------------------------------------------------------------------

testnxCL :: [Initial (SepSig NDxCLV NDxCLC)]
testnxCL = [
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
testnxCLBeta = fmap tryEvalBT testnxCL

testnxCLZeta :: [[InitialV NDxCLV NDxCLC]]
testnxCLZeta = fmap tryEvalZT testnxCL

testnxCLZetaAgreement :: IO ()
testnxCLZetaAgreement = do
  putStrLn $ "Example terms: " ++ show testnxCL
  equalityTests testnxCLBeta testnxCLZeta (fmap (const True) testnxCL)

-------------------------------------------------------------------------------
-- SECTION 4: Call-by-Value xCL (CBVxCLV1, CBVxCLC1)
-------------------------------------------------------------------------------

testCBV1 :: [InitialC CBVxCLV1 CBVxCLC1]
testCBV1 = [
  Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigV Scbv1) (sigOp $ SigV Kcbv1)) (sigOp $ SigV Icbv1)
  , Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigV Scbv1) (sigOp $ SigV Kcbv1)) (sigOp $ SigV Scbv1)) (sigOp $ SigV Kcbv1)
  , Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigV Kcbv1) (sigOp $ SigV Kcbv1)) (sigOp $ SigV Icbv1)) (sigOp $ SigC $ Compcbv1 (sigOp $ SigC $ Compcbv1 (sigOp $ SigV Kcbv1) (sigOp $ SigV Kcbv1)) (sigOp $ SigV Icbv1))
  ]

testCBV1Beta :: [InitialV CBVxCLV1 CBVxCLC1]
testCBV1Beta = fmap tryEvalBCBW testCBV1

testCBV1Zeta :: [InitialV CBVxCLV1 CBVxCLC1]
testCBV1Zeta = fmap tryEvalZCBW testCBV1

testCBV1ZetaAgreement :: IO ()
testCBV1ZetaAgreement = do
  putStrLn $ "Example terms: " ++ show testCBV1
  equalityTests testCBV1Beta testCBV1Zeta (fmap (const True) testCBV1)

-------------------------------------------------------------------------------
-- SECTION 5: Call-by-Value xCL (CBVxCLV2, CBVxCLC2)
-------------------------------------------------------------------------------

testCBV2 :: [InitialC CBVxCLV2 CBVxCLC2]
testCBV2 = [
  Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigV Scbv2) (sigOp $ SigV Kcbv2)) (sigOp $ SigV Icbv2)
  , Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigV Scbv2) (sigOp $ SigV Kcbv2)) (sigOp $ SigV Scbv2)) (sigOp $ SigV Kcbv2)
  , Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigV Kcbv2) (sigOp $ SigV Kcbv2)) (sigOp $ SigV Icbv2)) (sigOp $ SigC $ Compcbv2 (sigOp $ SigC $ Compcbv2 (sigOp $ SigV Kcbv2) (sigOp $ SigV Kcbv2)) (sigOp $ SigV Icbv2))  
  ]

testCBV2Beta :: [InitialV CBVxCLV2 CBVxCLC2]
testCBV2Beta = fmap tryEvalBCBU testCBV2

testCBV2Zeta :: [InitialV CBVxCLV2 CBVxCLC2]
testCBV2Zeta = fmap tryEvalZCBU testCBV2

testCBV2ZetaAgreement :: IO ()
testCBV2ZetaAgreement = do
  putStrLn $ "Example terms: " ++ show testCBV2
  equalityTests testCBV2Beta testCBV2Zeta (fmap (const True) testCBV2)

-------------------------------------------------------------------------------
-- SECTION 6: Call-by-Value xCL (CBVxCLV3, CBVxCLC3)
-------------------------------------------------------------------------------

testCBV3 :: [InitialC CBVxCLV3 CBVxCLC3]
testCBV3 = [
  Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigV Scbv3) (sigOp $ SigV Kcbv3)) (sigOp $ SigV Icbv3)
  , Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigV Scbv3) (sigOp $ SigV Kcbv3)) (sigOp $ SigV Scbv3)) (sigOp $ SigV Kcbv3)
  , Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigV Kcbv3) (sigOp $ SigV Kcbv3)) (sigOp $ SigV Icbv3)) (sigOp $ SigC $ Compcbv3 (sigOp $ SigC $ Compcbv3 (sigOp $ SigV Kcbv3) (sigOp $ SigV Kcbv3)) (sigOp $ SigV Icbv3))  
  ]

testCBV3Beta :: [InitialV CBVxCLV3 CBVxCLC3]
testCBV3Beta = fmap tryEvalBCBV testCBV3

testCBV3Zeta :: [InitialV CBVxCLV3 CBVxCLC3]
testCBV3Zeta = fmap tryEvalZCBV testCBV3

testCBV3ZetaAgreement :: IO ()
testCBV3ZetaAgreement = do
  putStrLn $ "Example terms: " ++ show testCBV3
  equalityTests testCBV3Beta testCBV3Zeta (fmap (const True) testCBV3)

-------------------------------------------------------------------------------
-- Run all Tests
-------------------------------------------------------------------------------

runAllTests :: IO ()
runAllTests = do

  putStrLn "=== Running Tests for Art ===\n"
  testArtZetaAgreement
  putStrLn ""

  putStrLn "=== Running Tests for xCL ===\n"
  testxCLZetaAgreement
  putStrLn ""

  putStrLn "=== Running Tests for NDxCL ===\n"
  testnxCLZetaAgreement
  putStrLn ""

  putStrLn "=== Running Tests for CBV1 ===\n"
  testCBV1ZetaAgreement
  putStrLn ""

  putStrLn "=== Running Tests for CBV2 ===\n"
  testCBV2ZetaAgreement
  putStrLn ""

  putStrLn "=== Running Tests for CBV3 ===\n"
  testCBV3ZetaAgreement
  putStrLn ""

main :: IO ()
main = runAllTests
