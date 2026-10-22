/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellMatrix
public import Dirichlet.Average.MatrixTaylor

/-!
# The continued matrix binomial series

Carlson (1971), Section 6. The scalar binomial series represents the continued
regularized matrix average for every complex row and column parameter vector.
The coefficients are the entire continuations of the shifted polynomial moments.
The full entry disk about one is retained. Native coefficient identities and
joint node holomorphy suffice by the parameter-Taylor recognition theorem.
-/

open Complex Set Polynomial Dirichlet
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
/-- Radial scaling of a matrix remains in the unit disk about one as long as
its scalar norm times the entry radius is less than one. -/
private theorem matrix_radial_mem_ball (Z : ι → κ → ℂ) {r : ℝ}
    (hZ : ∀ i j, ‖Z i j - 1‖ ≤ r) {w : ℂ} (hw : ‖w‖ * r < 1) :
    (fun i j => 1 + w * (Z i j - 1)) ∈ matrixNodeDomain (Metric.ball 1 1) := by
  intro i j
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul]
  exact (mul_le_mul_of_nonneg_left (hZ i j) (norm_nonneg _)).trans_lt hw

/-- Shifted polynomial moments have entire continuations in both parameter vectors. -/
theorem isRegMatrixContinuation_shifted_pow (Z : ι → κ → ℂ) (n : ℕ) :
    IsRegMatrixContinuation Z (fun z => (1 - z) ^ n)
      (continuedRegMatrixDirichletAverage Z (fun z => (1 - z) ^ n)) :=
  isRegMatrixContinuation_of_convex isOpen_univ convex_univ (by fun_prop)
    (fun _ _ => mem_univ _)

/-- The binomial coefficients of the continued matrix family are entire. -/
private theorem analyticOnNhd_matrix_binomial_coeff (Z : ι → κ → ℂ) (a : ℂ) (n : ℕ) :
    AnalyticOnNhd ℂ (fun p : (ι → ℂ) × (κ → ℂ) =>
      (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) *
        continuedRegMatrixDirichletAverage Z (fun z => (1 - z) ^ n) p) univ :=
  analyticOnNhd_const.mul (isRegMatrixContinuation_shifted_pow Z n).1

/-- A native radial binomial series has the fixed matrix moments as coefficients. -/
private theorem hasSum_native_matrix_radial_binomial {b : ι → ℂ} {β : κ → ℂ}
    (hb : b ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent)
    (Z : ι → κ → ℂ) (a : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hZ : ∀ i j, ‖Z i j - 1‖ ≤ r) {w : ℂ} (hw : ‖w‖ * r < 1) :
    HasSum (fun n => ((ascPochhammer ℂ n).eval a / (n.factorial : ℂ) *
        continuedRegMatrixDirichletAverage Z (fun z => (1 - z) ^ n) (b, β)) * w ^ n)
      (regMatrixDirichletAverage b β (fun i j => 1 + w * (Z i j - 1))
        (fun z => z ^ (-a))) := by
  have h := hasSum_regMatrixDirichletAverage_cpow_neg hb hβ
    (fun i j => 1 + w * (Z i j - 1)) a (‖w‖ * r) (by positivity) hw (fun i j => by
      simpa only [add_sub_cancel_left, norm_mul] using
        mul_le_mul_of_nonneg_left (hZ i j) (norm_nonneg w))
  convert h using 1
  funext n
  rw [(isRegMatrixContinuation_shifted_pow Z n).2 b β hb hβ,
    regMatrixDirichletAverage_radial_moment]
  ring

/-- **Carlson (1971), (6.2), binomial kernel, continued.** The full matrix entry disk
supports the binomial series at arbitrary complex row and column parameters. -/
theorem hasSum_continuedRegMatrixDirichletAverage_cpow_neg
    (b : ι → ℂ) (β : κ → ℂ) (Z : ι → κ → ℂ) (a : ℂ)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hZ : ∀ i j, ‖Z i j - 1‖ ≤ r) :
    HasSum (fun n => (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) *
      continuedRegMatrixDirichletAverage Z (fun z => (1 - z) ^ n) (b, β))
      (continuedRegMatrixDirichletAverage Z (fun z => z ^ (-a)) (b, β)) := by
  obtain ⟨s, hrs, hs1⟩ := exists_between hr1
  have hs : 0 < s := hr.trans_lt hrs
  have hR : 0 < s⁻¹ := inv_pos.mpr hs
  have hwr (w : ℂ) (hw : ‖w‖ < s⁻¹) : ‖w‖ * r < 1 := by
    have hws : ‖w‖ * s < 1 := (lt_div_iff₀ hs).mp (by simpa only [one_div] using hw)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrs.le (norm_nonneg _)) hws
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => z ^ (-a)) (Metric.ball 1 1) := by
    intro z hz
    have hn : ‖z - 1‖ < 1 := by simpa [dist_eq_norm] using hz
    have he := (abs_re_le_norm (z - 1)).trans_lt hn
    simp only [sub_re, one_re] at he
    have hzre : 0 < z.re := by linarith [neg_abs_le (z.re - 1)]
    exact analyticAt_id.cpow analyticAt_const (Or.inl hzre)
  have ht := hasSum_continuedRegMatrixDirichletAverage_of_native_series
    Metric.isOpen_ball (convex_ball 1 1) hf hR
    (Z := fun w i j => 1 + w * (Z i j - 1)) (by
      intro w _
      apply analyticAt_pi_iff.mpr
      intro i
      apply analyticAt_pi_iff.mpr
      intro j
      exact analyticAt_const.add (analyticAt_id.mul analyticAt_const))
    (fun w hw => matrix_radial_mem_ball Z hZ (hwr w hw))
    (analyticOnNhd_matrix_binomial_coeff Z a)
    (fun c γ hc hγ w hw => hasSum_native_matrix_radial_binomial hc hγ Z a hr hZ (hwr w hw))
    b β (w := 1) (by simpa using (one_lt_inv₀ hs).mpr hs1)
  simpa only [one_pow, mul_one, one_mul, add_sub_cancel] using ht

end Carlson
