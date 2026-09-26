/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Topology.LocallyConstantGluing
public import ToMathlib.Topology.CompactExhaustion
public import ToMathlib.Topology.Frontier
public import ToMathlib.Topology.Graph
public import ToMathlib.Topology.Path
public import ToMathlib.Topology.SeparateContinuous
public import ToMathlib.Topology.UpperSemicontinuous

/-!
# General topology support

Gluing functions with locally constant differences on simply connected spaces, compact
exhaustions, frontier and path lemmas, graph homeomorphisms, semicontinuity, and
Baire bounds for separately continuous maps. Declarations extend the existing Mathlib APIs.
This library has no dependency on project analysis, complex function theory, or applications.

## Main results

This module re-exports the following developments:

* `ToMathlib.Topology.LocallyConstantGluing`: Gluing functions with locally constant differences.
* `ToMathlib.Topology.CompactExhaustion`: Compact exhaustions of open subsets.
* `ToMathlib.Topology.Frontier`: Frontiers and complementary components.
* `ToMathlib.Topology.Graph`: Graphs characterized by equations.
* `ToMathlib.Topology.Path`: First exit of a path from an open set.
* `ToMathlib.Topology.SeparateContinuous`: Uniform bounds for separately continuous maps.
* `ToMathlib.Topology.UpperSemicontinuous`: Nonnegative multiples of upper semicontinuous functions.

## References

* `ToMathlib.Topology.LocallyConstantGluing`: formal background used by this module.
* `ToMathlib.Topology.CompactExhaustion`: formal background used by this module.
* `ToMathlib.Topology.Frontier`: formal background used by this module.
-/
