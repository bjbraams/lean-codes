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
public import SimplexMellin.L2
public import SimplexMellin.WeightedL2
public import SimplexMellin.Schwartz
public import SimplexMellin.FiniteRegularity
public import SimplexMellin.RadialProfile
public import SimplexMellin.IntrinsicInversion
public import SimplexMellin.LogRatioSchwartz
public import SimplexMellin.BoundaryDecay
public import SimplexMellin.PaleyWiener
public import SimplexMellin.LogRatio
public import SimplexMellin.Hyperplane
public import SimplexMellin.Image
public import SimplexMellin.Lattice
public import SimplexMellin.Poles
public import SimplexMellin.Estimate
public import SimplexMellin.Master

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
* `SimplexMellin.L2`: Plancherel for all continuous boundary kernels; the radial transform
  in `L²`, its inversion and distance preservation, and agreement with native Mellin integrals.
* `SimplexMellin.WeightedL2`: the exponential-profile transform on the complete weighted
  simplex `L²` space, an isometry onto a closed image with inverse; exact normalization,
  dense Schwartz approximation and agreement with native integrals for continuous kernels.
* `SimplexMellin.Schwartz`: exponential-profile inversion and Plancherel for kernels smooth
  near the closed simplex, including kernels nonzero on the faces; all angular derivatives
  are uniformly bounded.
* `SimplexMellin.FiniteRegularity`: exponential-profile inversion for `C^N` boundary kernels
  with `2N > card ι` (a sufficient Sobolev bound).
* `SimplexMellin.IntrinsicInversion`: full-plane absolute inversion for exponential and
  compact positive smooth radial profiles with the improved sufficient count `2N > card ι - 1`;
  diagonal invariance of the angular factor supplies the additional radial decay.
* `SimplexMellin.RadialProfile`: compactly supported smooth radial profiles, with inversion
  for finite-regularity boundary kernels and Plancherel for smooth boundary kernels.
* `SimplexMellin.LogRatioSchwartz`: positive Mellin weights are Schwartz in the intrinsic
  log-ratio dimension; native Fourier identification and absolute inversion from one
  positive fixed-sum vertical hyperplane for boundary kernels with `2N > card ι - 1`.
* `SimplexMellin.BoundaryDecay`: finite-order frequency decay and rapid decay on fixed-sum
  vertical hyperplanes for smooth boundary kernels.
* `SimplexMellin.Poles`: coordinate pole numerators, boundary-jet residues, and equivalence
  between removal of zero-parameter poles and vanishing of the face trace.
* `SimplexMellin.PaleyWiener`: the necessity half of a Paley–Wiener description of the image:
  for kernels vanishing near the faces the native integral is entire, of exponential type, and
  Schwartz on vertical planes after multiplication by a compactly supported radial factor.
* `SimplexMellin.LogRatio`: log-ratio coordinates `w j = log (u j / u i₀)` and the change of
  variables `∫_Δ f = ∫ (∏ u(w)) f(u(w)) dw`.
* `SimplexMellin.Hyperplane`: on a hyperplane `∑ b i = s` the transform is a Fourier–Laplace
  transform in log-ratio coordinates; Paley–Wiener on hyperplanes: every Paley–Wiener function
  is the hyperplane restriction of the transform of a kernel smooth near the simplex and
  vanishing near the faces, smooth kernels give Paley–Wiener restrictions, and one hyperplane
  determines the kernel.
* `SimplexMellin.Image`: the Paley–Wiener description of the image: the transforms of kernels
  smooth near the simplex and vanishing near its faces are the entire functions with the sum-shift
  equation, an exponential bound in the real parts, and Paley–Wiener bounds on one hyperplane
  (via Carlson's theorem, `ToMathlib.Analysis.Complex.Carlson`).
* `SimplexMellin.Lattice`: the transform of a continuous kernel on `Re b > 0` is determined by its
  values on `ℕ^ι + 𝟙` (the monomial moments), by Carlson's theorem in several variables.
* `SimplexMellin.Estimate`: on compact parameter sets, `|T_b[g]|` is bounded by a constant times
  a bound for finitely many derivatives of `g` on the simplex.
* `SimplexMellin.Master`: a master theorem with simplex structure: the several-variable Mellin
  transform of `Φ(∑ x) g(x / ∑ x)`, `Φ` the function of Ramanujan's master theorem.

The declarations live in the `Dirichlet` namespace. The research programme is recorded in
`DirichletTransformProgram.md`.
-/
