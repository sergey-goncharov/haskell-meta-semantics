# ICFP 2025 Artifact: Big Steps in Higher-Order Mathematical Operational Semantics

## Overview

This artifact accompanies the ICFP 2025 paper "Big Steps in Higher-Order Mathematical Operational Semantics" and provides Haskell source files that implement the type classes for small-step and big-step semantics, construction, examples and benchmarks discussed in the paper. 

## File Structure

- ``Syntax.hs``: Contains the abstract notions needed about the syntax of a language (standard and separated), along with the syntax of xCL and non-deterministic xCL.
- ``Behaviour.hs``: Implements the behaviour functor in general (standard and separated), and for the cases of deterministic and non-deterministic behaviour.
- ``HOGSOS.hs``: Implements HoGSOS laws in the standard sense, and instantiates xCL as a HoGSOS law.
- ``Separable.hs``: Implements separable HoGSOS laws (equipped with multi-step transitions) and instantiates non-deterministic xCL as a separated HoGSOS law.
- ``BigStep.hs``: Implements abstract big-step SOS along with its operational model.
- ``Examples.hs``: Implements the omega-f-g language from the introduction of the paper, along with three versions of call-by-value xCL.
- ``Benchmark.hs``: Contains tests and instructions to run them, showing the results of the small-step (presented by multi-step transition) and big-step specifications.
- ``Utils.hs``: Defines an auxiliary function to help with the presentation.

## Requirements

To build and run the artifact, you will need:

- **GHC   ≥ 9.4**
- **Cabal ≥ 3.0**
- No external libraries beyond the standard `base` package (version ≥ 4.12 and < 5)
A
All modules are written in **Haskell2010** and use common language extensions such as `TypeApplications`, `FlexibleInstances`, and `ScopedTypeVariables`.

## Building the Artifact
Using **Cabal**:

```bash
cabal update
cabal build

