/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.SeveralComplexVariables.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Locally uniform limits of analytic maps in several variables

This file is the proposed home for the finite-dimensional several-variable Weierstrass
convergence theorem and its normally summable series consequences.  The topological notion
`TendstoLocallyUniformlyOn` is already general; what is missing is preservation of complex
analyticity when the source is a finite-dimensional complex normed space rather than `ℂ`.

This is a temporary project home for material ultimately intended for a Mathlib location such as
`Mathlib.Analysis.Complex.SeveralVariables.LocallyUniform`.

## Main results

* `TendstoLocallyUniformlyOn.analyticOnNhd_pi` is the several-variable Weierstrass convergence
  theorem for finite complex coordinate spaces.
* `HasSumLocallyUniformlyOn.analyticOnNhd_pi` is its series form.

Useful companion results should give locally uniform convergence of derivatives and justify
termwise Fréchet or coordinate differentiation.  The proof should use the theorem in `Basic`
after establishing differentiability of the locally uniform limit.
-/

public section

open Filter Set
open scoped Classical

namespace SeveralComplexVariables

/-! Compact-local majorants and normal-summability helper definitions may live here. -/

end SeveralComplexVariables

variable {ι κ F : Type*} [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Weierstrass convergence theorem, finite-coordinate form.** A locally uniform limit of
analytic maps on an open subset of a finite complex coordinate space is analytic. -/
theorem TendstoLocallyUniformlyOn.analyticOnNhd_pi
    {U : Set (ι → ℂ)} {l : Filter κ} [l.NeBot]
    {f : κ → (ι → ℂ) → F} {g : (ι → ℂ) → F}
    (hlim : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ n in l, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) :
    AnalyticOnNhd ℂ g U := by
  apply SeveralComplexVariables.analyticOnNhd_pi_of_analyticOnNhd_update hU
  intro z hz i
  let update : ℂ → (ι → ℂ) := fun w ↦ Function.update z i w
  let V : Set ℂ := update ⁻¹' U
  have hupdate : Continuous update := by
    dsimp only [update]
    fun_prop
  have hupdate_diff : Differentiable ℂ update := by
    dsimp only [update]
    rw [show (fun w : ℂ ↦ Function.update z i w) = fun w ↦
        z + ContinuousLinearMap.single ℂ (fun _ : ι ↦ ℂ) i (w - z i) by
      funext w j
      by_cases hji : j = i <;> simp [hji]]
    fun_prop
  have hV : IsOpen V := hU.preimage hupdate
  have hmap : Set.MapsTo update V U := fun _ hw ↦ hw
  have hlim' : TendstoLocallyUniformlyOn
      (fun n ↦ f n ∘ update) (g ∘ update) l V :=
    hlim.comp update hmap hupdate.continuousOn
  have hfdiff : ∀ᶠ n in l, DifferentiableOn ℂ (f n ∘ update) V := by
    filter_upwards [hf] with n hn
    intro w hw
    exact (((hn.differentiableOn _ hw).differentiableAt
      (hU.mem_nhds (hmap hw))).comp w hupdate_diff.differentiableAt).differentiableWithinAt
  exact (hlim'.differentiableOn hfdiff hV).analyticAt
    (hV.mem_nhds (show update (z i) ∈ U by simpa [update] using hz))

/-- A locally uniformly convergent sum of analytic maps on an open finite complex coordinate
space is analytic. -/
theorem HasSumLocallyUniformlyOn.analyticOnNhd_pi
    {U : Set (ι → ℂ)} {f : κ → (ι → ℂ) → F} {g : (ι → ℂ) → F}
    (hsum : HasSumLocallyUniformlyOn f g U)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) :
    AnalyticOnNhd ℂ g U := by
  apply TendstoLocallyUniformlyOn.analyticOnNhd_pi hsum _ hU
  filter_upwards with s
  exact Finset.analyticOnNhd_fun_sum s fun n _ ↦ hf n

/-- A series of analytic maps is analytic when its terms admit a summable uniform majorant on
every compact subset of the domain. -/
theorem analyticOnNhd_tsum_of_summable_norm_on_compacts
    {U : Set (ι → ℂ)} {f : κ → (ι → ℂ) → F}
    (hU : IsOpen U) (hf : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (hmajorant : ∀ K ⊆ U, IsCompact K → ∃ M : κ → ℝ,
      Summable M ∧ ∀ n x, x ∈ K → ‖f n x‖ ≤ M n) :
    AnalyticOnNhd ℂ (fun x ↦ ∑' n, f n x) U := by
  have hs : SummableLocallyUniformlyOn f U :=
    SummableLocallyUniformlyOn_of_locally_bounded hU hmajorant
  exact hs.hasSumLocallyUniformlyOn.analyticOnNhd_pi hf hU

end
