/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.Basic
public import SeveralComplexVariables.Osgood
public import SeveralComplexVariables.LocallyUniform
public import SeveralComplexVariables.ParametricIntegral

/-!
# Several-complex-variables infrastructure

This umbrella file imports the project-local homes for finite-dimensional complex analyticity,
Osgood's theorem, locally uniform limits, and analytic parameter-dependent integrals.  The
individual files are deliberately independent of the simplex-measure and Carlson developments
so that they can evolve into separate Mathlib contributions.
-/
