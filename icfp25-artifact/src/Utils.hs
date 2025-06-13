{-|
Module      : Utils
Description : Utility functions for testing and output comparison

This module provides helper functions used across the artifact, concretely:

- `compareLists`: A function to compare two lists element-wise and print results

These utilities are used in benchmark scripts to validate semantic agreement
between different evaluation strategies.
-}

module Utils where

-- Function to compare two lists elementwise and print a message for each comparison.
compareLists :: (Show a, Eq a) => [a] -> [a] -> IO ()
compareLists [] [] = return ()
compareLists xs [] = putStrLn "Incompatible list lengths."
compareLists [] ys = putStrLn "Incompatible list lengths."
compareLists (x:xs) (y:ys) = do
  if x == y
    then putStrLn $ "> " ++ show x ++ " = "  ++ show y
    else putStrLn $ "> " ++ show x ++ " /= " ++ show y
  compareLists xs ys
