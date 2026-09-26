/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Algebra
public import ToMathlib.Analysis
public import ToMathlib.Topology
public import Pochhammer
public import ComplexAnalysis
public import SeveralComplexVariables
public import StdSimplexMeasure
public import Dirichlet
public import Carlson

/-!
# Carlson special functions and their foundations

This umbrella module imports the project’s mathematical libraries: algebraic, analytic, and
topological foundations; Pochhammer and Gamma identities; standard-simplex measures and
Dirichlet integrals; Carlson special functions; and analysis in one and several complex
variables. Its results are supplied by the imported modules.

## Main results

This module re-exports the following developments:

* `ToMathlib.Algebra`: General algebra support.
* `ToMathlib.Analysis`: General analysis support.
* `ToMathlib.Topology`: General topology support.
* `Pochhammer`: Pochhammer infrastructure.
* `ComplexAnalysis`: The subset of single-variable complex analysis used here.
* `SeveralComplexVariables`: The subset of several complex variables used here.
* `StdSimplexMeasure`: Standard-simplex geometry, measure and integration.
* `Dirichlet`: Dirichlet measures, averages and transforms.
* `Carlson`: Carlson special functions.

## References

* `ToMathlib.Algebra`: formal background used by this module.
* `ToMathlib.Analysis`: formal background used by this module.
* `ToMathlib.Topology`: formal background used by this module.
-/
