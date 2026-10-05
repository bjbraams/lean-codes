/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Gamma
public import TauCeti.Probability.Distributions.Dirichlet.Basic

/-!
# Bridge to the Tau Ceti Dirichlet distribution

The Tau Ceti contributors define the Dirichlet law `TauCeti.Probability.dirichletMeasure` on
`EuclideanSpace ℝ ι` as the push-forward of independent unit-rate Gamma variables under
normalization by their sum (`TauCeti.Probability.Distributions.Dirichlet.Basic`). The project's
`ProbabilityTheory.dirichletMeasure` is instead a density against the coordinate-normalized
simplex measure on `ι → ℝ`. For positive parameters on a nonempty index type the two agree under
the canonical equivalence `EuclideanSpace.equiv ι ℝ`: this is the second marginal of
`ProbabilityTheory.map_sum_simplexNormalize_pi_gammaMeasure` at unit rate.

The bridge allows statements proved for either measure to be transported to the other.

## Main results

* `ProbabilityTheory.map_dirichletMeasure_euclidean`: the image of the local Dirichlet measure in
  `EuclideanSpace ℝ ι` is the Tau Ceti Dirichlet law.
* `ProbabilityTheory.dirichletMeasure_eq_map_tauCeti`: conversely, the local Dirichlet measure is
  the coordinate image of the Tau Ceti law.
* `ProbabilityTheory.integral_dirichletMeasure_eq_tauCeti`: the corresponding transfer of
  integrals.

## References

* `TauCeti.Probability.Distributions.Dirichlet.Basic`.
-/

@[expose] public noncomputable section

open Dirichlet MeasureTheory

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι] {b : ι → ℝ}

/-- For positive parameters, the image of the local Dirichlet measure under the canonical
equivalence with `EuclideanSpace ℝ ι` is the Tau Ceti contributors' Gamma-normalization Dirichlet
law `TauCeti.Probability.dirichletMeasure`. -/
theorem map_dirichletMeasure_euclidean (hb : b ∈ mvRealBetaDomain) :
    (dirichletMeasure b).map (EuclideanSpace.equiv ι ℝ).symm =
      TauCeti.Probability.dirichletMeasure b := by
  have hpos : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have := isProbabilityMeasure_gammaMeasure hpos one_pos
  have := isProbabilityMeasure_dirichletMeasure hb
  have hsnd := congrArg (Measure.map Prod.snd)
    (map_sum_simplexNormalize_pi_gammaMeasure hb (r := 1) one_pos)
  rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod, measure_univ,
    one_smul] at hsnd
  rw [TauCeti.Probability.dirichletMeasure_of_pos hb, ← hsnd,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  ext i
  simp [Convexity.StdSimplex.normalizeCoordinates]

/-- For positive parameters, the local Dirichlet measure is the coordinate image of the Tau Ceti
contributors' Dirichlet law. -/
theorem dirichletMeasure_eq_map_tauCeti (hb : b ∈ mvRealBetaDomain) :
    dirichletMeasure b =
      (TauCeti.Probability.dirichletMeasure b).map (EuclideanSpace.equiv ι ℝ) := by
  rw [← map_dirichletMeasure_euclidean hb, Measure.map_map (by fun_prop) (by fun_prop)]
  simp

/-- Integrals against the local Dirichlet measure are integrals against the Tau Ceti
contributors' Dirichlet law, read in Euclidean coordinates. No measurability is assumed. -/
theorem integral_dirichletMeasure_eq_tauCeti {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hb : b ∈ mvRealBetaDomain) (g : (ι → ℝ) → E) :
    ∫ u, g u ∂dirichletMeasure b =
      ∫ x, g (EuclideanSpace.equiv ι ℝ x) ∂TauCeti.Probability.dirichletMeasure b := by
  rw [dirichletMeasure_eq_map_tauCeti hb]
  exact integral_map_equiv (EuclideanSpace.equiv ι ℝ).toHomeomorph.toMeasurableEquiv g

end ProbabilityTheory
