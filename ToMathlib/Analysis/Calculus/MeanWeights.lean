/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Weights defined by differentiation at the diagonal

The weight of coordinate `i` is the derivative at the all-one vector in direction
`Pi.single i 1`. This definition works over both real and complex scalars and does
not impose an order-theoretic notion of mean. Normalization along the diagonal
implies that the weights sum to one.

## References

* J. L. Brenner and B. C. Carlson, *Homogeneous mean values: weights and asymptotics*,
  J. Math. Anal. Appl. 123 (1987), 265–280, Section 2.
-/

open Filter
open scoped Topology
@[expose] public noncomputable section
namespace Function
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight of a coordinate is its derivative at the all-one vector. -/
def meanWeight (f : (ι → 𝕜) → 𝕜) (i : ι) : 𝕜 :=
  fderiv 𝕜 f 1 (Pi.single i 1)

/-- The sum of the coordinate weights is the derivative in the diagonal direction. -/
theorem sum_meanWeight (f : (ι → 𝕜) → 𝕜) :
    ∑ i, meanWeight 𝕜 f i = fderiv 𝕜 f 1 1 := by
  unfold meanWeight
  rw [← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply]

/-- The weights give the entire first derivative at the all-one vector. -/
theorem fderiv_one_eq_sum_meanWeight (f : (ι → 𝕜) → 𝕜) (v : ι → 𝕜) :
    fderiv 𝕜 f 1 v = ∑ i, v i * meanWeight 𝕜 f i := by
  simp only [meanWeight, ← smul_eq_mul, ← map_smul, ← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply]

/-- If the restriction of `f` to the diagonal has derivative one at the all-one vector, then the
derivative-defined weights sum to one. No positivity or homogeneity assumption is needed; in
particular it suffices that `f (fun _ ↦ r) = r` near `r = 1`. -/
theorem sum_meanWeight_eq_one {f : (ι → 𝕜) → 𝕜} (hf : DifferentiableAt 𝕜 f 1)
    (hdiag : HasDerivAt (fun r : 𝕜 ↦ f (fun _ ↦ r)) 1 1) :
    ∑ i, meanWeight 𝕜 f i = 1 := by
  rw [sum_meanWeight]
  have h : HasDerivAt (fun r : 𝕜 ↦ f (fun _ ↦ r)) (fderiv 𝕜 f 1 1) 1 :=
    hf.hasFDerivAt.comp_hasDerivAt 1 (hasDerivAt_pi.mpr fun _ ↦ hasDerivAt_id 1)
  exact h.unique hdiag

end Function
