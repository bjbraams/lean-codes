/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.Face
public import SimplexMellin.Uniqueness
public import SimplexMellin.Bridge
public import SimplexMellin.Inversion
public import SimplexMellin.Schwartz

/-!
# The simplex Mellin transform

The regularized Dirichlet transform `T_b[g] = ∫_Δ ∏ i, u i ^ (b i - 1) / Γ(b i) g(u) du` of a
kernel `g` on the standard simplex, viewed as a transform in its own right: the angular part of
the multivariable Mellin transform in simplicial polar coordinates. Its definition, entire
continuation and structural laws are in `Dirichlet.Transform`, which is shared with Carlson's
Dirichlet averages; this library develops the theory beyond what the averages need.

## Main results

* `SimplexMellin.Face`: face formulas at nonpositive integer parameters, `bᵢ = 0` and `bᵢ = -m`.
* `SimplexMellin.Uniqueness`: a continuous kernel is determined by its transform at the positive
  integer parameters (its monomial moments).
* `SimplexMellin.Bridge`: the Mellin bridge
  `mvMellin (φ(∑ x) g(x / ∑ x)) b = ℳ[φ](∑ b) ∏ Γ(b i) T_b[g]`, and its continued form.
* `SimplexMellin.Inversion`: inversion on vertical planes and Plancherel.
* `SimplexMellin.Schwartz`: the inversion formula with the Gamma factors is unconditional for
  smooth kernels vanishing near the faces.

The declarations live in the `Dirichlet` namespace. The research programme is recorded in
`DirichletTransformProgram.md`.
-/
