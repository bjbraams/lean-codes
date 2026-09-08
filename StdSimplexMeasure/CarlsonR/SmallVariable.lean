/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonR.IntegralEvaluation
import StdSimplexMeasure.CarlsonR.Relations

/-!
# Dependence of Carlson's R-function on a small variable

This file develops [Carl77, Section 8.3].  Its core result identifies the sectorial limit as
one variable tends to zero with deletion of that variable and a beta-factor correction.
-/

open Complex Filter ProbabilityTheory
open scoped Classical Topology
public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- A closed right-half-plane subsector used when a native R-integral variable approaches
zero.  Carlson's wider slit-plane sector is recovered only after continuation in the
variables. -/
def carlsonSmallVariableSector (δ r : ℝ) : Set ℂ :=
  {w | ‖w‖ ≤ r ∧ (w = 0 ∨ |arg w| ≤ Real.pi / 2 - δ)}

/-- Every point of Carlson's small-variable sector has norm at most its radius. -/
theorem norm_le_of_mem_carlsonSmallVariableSector {δ r : ℝ} {w : ℂ}
    (hw : w ∈ carlsonSmallVariableSector δ r) : ‖w‖ ≤ r :=
  hw.1

/-- The parameter vector obtained by deleting a distinguished coordinate. -/
def eraseCarlsonParameter (i : ι) (b : ι → ℂ) : {j // j ≠ i} → ℂ :=
  fun j => b j

/-- The variable vector obtained by deleting a distinguished coordinate. -/
def eraseCarlsonVariable (i : ι) (z : ι → ℂ) : {j // j ≠ i} → ℂ :=
  fun j => z j

/-- Carlson's sectorial small-variable limit, Theorem 8.3-1, in regularized form.

The beta factors in Carlson's unregularized statement are absorbed by Gamma regularization;
the remaining shifted Gamma factor is displayed explicitly. -/
theorem tendsto_regCarlsonRIntegral_update_zero
    [Nontrivial ι] (i : ι) {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (ha'i : 0 < (a' - b i).re) (hsum : a + a' = ∑ j, b j)
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    Tendsto (fun w => regCarlsonRIntegral (-a) b (Function.update z i w))
      (𝓝[≠] 0 ⊓ 𝓟 (carlsonSmallVariableSector 1 1))
      (𝓝 (Gamma (a' - b i) / Gamma a' *
        regCarlsonRIntegral (-a) (eraseCarlsonParameter i b)
          (eraseCarlsonVariable i z))) := by
  sorry

/- Gauss's summation formula is a two-variable hypergeometric specialization of the theorem
above and is intentionally not included in the core R-function API. -/

end DirichletTransform
end CarlsonR
