{-|

Module      : Utils
Description : Utility functions for testing and output comparison

This module provides helper functions used across the artifact, concretely:

- `equalityTests`: A function to compare two lists element-wise and compare result with expectation

These utilities are used in test scripts to validate semantic agreement between evaluation strategies.

-}

module Utils where

-- Function to test equality between corresponding elements of two lists
-- against expected boolean results, printing pass/fail messages.
equalityTests :: (Show a, Eq a) => [a] -> [a] -> [Bool] -> IO ()
equalityTests [] [] [] = return ()
equalityTests xs ys es 
  | length xs /= length ys || length ys /= length es = 
      putStrLn "ERROR: Incompatible list lengths - all three lists must have the same length."
equalityTests (x:xs) (y:ys) (expected:es) = do
  let actualEqual = x == y
      testPassed = actualEqual == expected
  
  if testPassed
    then putStrLn $ "✓ PASS: " ++ show x ++ 
                   (if expected then " = " else " /= ") ++ 
                   show y ++ " (as expected)"
    else putStrLn $ "✗ FAIL: " ++ show x ++ 
                   (if actualEqual then " = " else " /= ") ++ 
                   show y ++ ", but expected " ++ 
                   (if expected then "equal" else "not equal")
  
  equalityTests xs ys es