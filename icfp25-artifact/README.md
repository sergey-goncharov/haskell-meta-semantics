# ICFP 2025 Artifact: Big Steps in Higher-Order Mathematical Operational Semantics

## Overview

This artifact accompanies the ICFP 2025 paper "Big Steps in Higher-Order Mathematical Operational Semantics" and provides Haskell source files that implement the type classes for small-step and big-step semantics, related constructions, examples and tests supporting the paper.

Links to the paper material are provided in comments via "Thm. \<number\>", "Sec. \<number\>", "Display (\<number\>)", etc.

The implementation only contains constructions, but not proofs (as Haskell does not support them). It covers only those examples, that are mentioned in the paper as examples in the category of sets. Thus, e.g. Sec. 6.2 (Recursion and Conditionals) and Sec. 7.3 (lambda-calculus) are not covered, as those involve categories of many-sorted sets and presheaves correspondingly.

## Artifact Structure

The files inside the ``src`` folder are subject to the following dependencies:

```                                             
┌───────────┐    ┌───────────┐    ┌──────────────┐    ┌────────────┐   ┌─────────────┐    ┌──────────┐
│ Syntax.hs │───►│ HOGSOS.hs │───►│ Separable.hs │───►│ BigStep.hs │──►│ Examples.hs │───►│ Tests.hs │
└───────────┘    └───────────┘    └──────────────┘    └────────────┘   └─────────────┘    └──────────┘ 
┌──────────────┐       ▲                                               ┌──────────┐            ▲  
│ Behaviour.hs │───────┘                                               │ Utils.hs │────────────┘
└──────────────┘                                                       └──────────┘
```

The main function is ``runAllTests`` in Tests.hs. It tests the main result of the paper Thm. 5.4 on example cases from the paper, including Exp. 2.1, for which it fails, because the strong separability condition is not satisfied. ``Main.hs`` is used a wrapper for ``runAllTests``, for compatibility with cabal.

## Source File Contents

- ``Syntax.hs``: Contains the abstract notion of syntax of a language via functors and monads
- ``Behaviour.hs``: Contains the abstract notion of behaviour and auxiliary definitions
- ``HOGSOS.hs``: Implements HO-GSOS as a type class
- ``Separable.hs``: Implements separable HO-GSOS laws, multi-step transitions and instantiates HO-GSOS as separated HO-GSOS 
- ``BigStep.hs``: Implements abstract big-step SOS, its operational model, and the translation from small-step (separated HO-GSOS) to big-step
- ``Examples.hs``: Implements the omega-f-g language from the introduction of the paper, together with xCL and those its versions from 
the "Case Studies" Section (Sec. 6) that live in the category of sets.
- ``Tests.hs``: Contains tests and instructions to run them, showing the results of the small-step (presented by multi-step transition) and big-step specifications.
- ``Utils.hs``: Defines an auxiliary function to help with the presentation.

## Reuse

The framework is parametric in 

1. Two language functors: for _value formers_ (instance of ``Functor``) and for _computation formers_ (instance of ``Bifunctor``) 
2. Value part of the behavior functor (instance of ``MixFunctor``)
3. Monad for modelling effects behind small-step/big-step transitions (instance of ``Monad``) 
4. Small-step operations semantics in the form of separated HO-GSOS (instance of ``SepHOGSOS``)

These ingredients must be provided for experimenting with custom languages/semantics -- examples are given in ``Examples.hs``. It is expected that only 1. and 4. can be broadly varied -- for 2. one typically uses the exponentiation functor ``->`` (true for all present examples); for 3. one typically uses the identity monad or the list monad (true for all present examples). 

## Requirements

To build and run the artifact, you will need:

- **GHC   ≥ 9.4**
- **Cabal ≥ 3.0**
- No external libraries beyond the standard `base` package (version ≥ 4.12 and < 5)

All modules are written in **Haskell2010** and use common language extensions such as `TypeApplications`, `FlexibleInstances`, and `ScopedTypeVariables`.

## Building the Artifact
Using **Cabal**:

```bash
cabal update
cabal build
```
## Running Tests
Using **Cabal**:

```bash
cabal exec tests
```
