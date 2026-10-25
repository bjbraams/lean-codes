/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.AppellF4Equal
public import Carlson.TwoVariable.MatrixTaylor
public import Carlson.TwoVariable.RPolynomial.SpecialValues

/-!
# Bailey's restricted F₄ matrix

Carlson (1975), equations (2.9)–(2.10) and (4.4). The restriction `b = a + 1/2`
turns F₄ into a double average over a parallelogram. Symmetric beta moments
vanish in odd degrees; their even degrees recover the squared-argument F₄
coefficients by duplication. The continued identity retains both duplication
ratios, including their zeros at exceptional averaging parameters.
-/

open Complex Polynomial Dirichlet Set Filter Finset
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The entire even symmetric moment on the native parameter half-plane. -/
private theorem regEqualRPolynomial_even_opposite_of_re (n : ℕ) {β : ℂ}
    (hβ : 0 < β.re) (x : ℂ) :
    regEqualRPolynomial (2 * n) β x (-x) =
      (ascPochhammer ℂ n).eval (1 / 2) * x ^ (2 * n) / Gamma (β + 1 / 2 + n) := by
  have hc : 0 < (β + 1 / 2).re := by simp only [add_re]; norm_num; linarith
  have hG := Gamma_ne_zero_of_re_pos hc
  have hGn : Gamma (β + 1 / 2 + n) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simpa only [add_re, natCast_re] using
      (add_pos_of_pos_of_nonneg hc (Nat.cast_nonneg (α := ℝ) n)))
  have hP := ascPochhammer_eval_ne_zero_of_re_pos hβ n
  rw [regEqualRPolynomial_eq_numerator (2 * n) hβ, numerator₂_even_opposite,
    ← two_mul β, ascPochhammer_eval_double,
    ← Gamma_add_nat_div_Gamma_eq (β + 1 / 2)
      (fun k hk => hG ((Gamma_eq_zero_iff _).mpr ⟨k, hk⟩))]
  generalize Gamma (β + 1 / 2 + n) = A at *
  generalize Gamma (β + 1 / 2) = B at *
  generalize (ascPochhammer ℂ n).eval β = P at *
  field_simp

/-- The normalized even symmetric moment, with all removable parameter values filled. -/
theorem regEqualRPolynomial_even_opposite (n : ℕ) (β x : ℂ) :
    regEqualRPolynomial (2 * n) β x (-x) =
      (ascPochhammer ℂ n).eval (1 / 2) * x ^ (2 * n) / Gamma (β + 1 / 2 + n) := by
  have hf : AnalyticOnNhd ℂ (fun s => regEqualRPolynomial (2 * n) s x (-x)) univ :=
    fun _ _ => analyticAt_regEqualRPolynomial_comp analyticAt_id
      analyticAt_const analyticAt_const (2 * n)
  have hg : AnalyticOnNhd ℂ (fun s =>
      (ascPochhammer ℂ n).eval (1 / 2) * x ^ (2 * n) / Gamma (s + 1 / 2 + n)) univ := by
    intro s _
    simp only [div_eq_mul_inv]
    apply AnalyticAt.mul analyticAt_const
    exact (differentiable_one_div_Gamma.analyticAt _).comp
      (f := fun s : ℂ => s + 1 / 2 + n)
      ((analyticAt_id.add analyticAt_const).add analyticAt_const)
  apply congrFun (hf.eq_of_eventuallyEq hg (z₀ := (1 : ℂ)) ?_) β
  filter_upwards [Complex.continuous_re.continuousAt.eventually_const_lt
    (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with s hs
  exact regEqualRPolynomial_even_opposite_of_re n hs x

/-- The regularized even symmetric moment at every complex averaging parameter. -/
theorem regRPolynomial_even_opposite (n : ℕ) (β x : ℂ) :
    regRPolynomial (2 * n) β β x (-x) = quadraticGammaRatio β *
      ((ascPochhammer ℂ n).eval (1 / 2) * x ^ (2 * n) / Gamma (β + 1 / 2 + n)) := by
  rw [regRPolynomial, regCarlsonRPolynomial_pair_self_eq, regEqualRPolynomial_even_opposite]

/-- The parallelogram matrix for Bailey's restriction `b = a + 1/2`. -/
def appellF4BaileyMatrix (x y : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![1 - x - y, 1 - x + y], ![1 + x - y, 1 + x + y]]

/-- The shifted parallelogram kernel is a sum of centered row and column coordinates. -/
theorem matrixAffineForm_appellF4Bailey (x y : ℂ) {u v : Fin 2 → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2))
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :
    1 - matrixAffineForm (appellF4BaileyMatrix x y) u v =
      carlsonAffineForm (pair x (-x)) u + carlsonAffineForm (pair y (-y)) v := by
  have hu1 : (u 1 : ℂ) = 1 - (u 0 : ℂ) := by
    have h : (u 0 : ℂ) + u 1 = 1 := by exact_mod_cast (by simpa [Fin.sum_univ_two] using hu.2)
    linear_combination h
  have hv1 : (v 1 : ℂ) = 1 - (v 0 : ℂ) := by
    have h : (v 0 : ℂ) + v 1 = 1 := by exact_mod_cast (by simpa [Fin.sum_univ_two] using hv.2)
    linear_combination h
  simp only [matrixAffineForm, appellF4BaileyMatrix, carlsonAffineForm, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, pair_zero, pair_one,
    hu1, hv1]
  ring

/-- The explicit polynomial moment of the centered parallelogram. -/
def appellF4BaileyMoment (x y : ℂ) (N : ℕ)
    (p : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℂ :=
  ∑ q ∈ antidiagonal N, (N.choose q.1 : ℂ) *
    regCarlsonRPolynomial q.1 p.1 (pair x (-x)) *
      regCarlsonRPolynomial q.2 p.2 (pair y (-y))

/-- The native centered matrix moments are products of symmetric coordinate moments. -/
private theorem native_appellF4BaileyMoment {r β : Fin 2 → ℂ}
    (hr : r ∈ mvBetaConvergent) (hβ : β ∈ mvBetaConvergent) (x y : ℂ) (N : ℕ) :
    regMatrixDirichletAverage r β (appellF4BaileyMatrix x y) (fun z => (1 - z) ^ N) =
      appellF4BaileyMoment x y N (r, β) := by
  rw [regMatrixDirichletAverage_binomial_moment hr hβ (appellF4BaileyMatrix x y)
    (carlsonAffineForm (pair x (-x))) (fun _ => 1)
    (fun _ => 1) (carlsonAffineForm (pair y (-y)))
    (continuous_carlsonAffineForm _) continuous_const continuous_const
    (continuous_carlsonAffineForm _)
    (fun u hu v hv => by rw [matrixAffineForm_appellF4Bailey x y hu hv]; ring)]
  unfold appellF4BaileyMoment
  apply Finset.sum_congr rfl
  intro q _
  simp only [one_pow, one_mul, mul_one]
  change (N.choose q.1 : ℂ) * regCarlsonDirichletAverage r (pair x (-x)) (fun z => z ^ q.1) *
    regCarlsonDirichletAverage β (pair y (-y)) (fun z => z ^ q.2) = _
  rw [regCarlsonDirichletAverage_pow _ _ hr, regCarlsonDirichletAverage_pow _ _ hβ]

/-- The centered polynomial moments are entire in the independent parameter vectors. -/
private theorem analyticOnNhd_appellF4BaileyMoment (x y : ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (appellF4BaileyMoment x y N) univ := by
  intro p _
  have hr (i : Fin 2) : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × (Fin 2 → ℂ) => q.1 i) p :=
    (analyticAt_pi_iff.mp analyticAt_fst) i
  have hc (i : Fin 2) : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × (Fin 2 → ℂ) => q.2 i) p :=
    (analyticAt_pi_iff.mp analyticAt_snd) i
  unfold appellF4BaileyMoment
  apply Finset.analyticAt_fun_sum
  intro q _
  apply AnalyticAt.mul
  · apply AnalyticAt.mul analyticAt_const
    exact analyticAt_regCarlsonRPolynomial_comp
      (b := fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) => p.1)
      (z := fun _ => pair x (-x)) hr (fun _ => analyticAt_const) q.1
  · exact analyticAt_regCarlsonRPolynomial_comp
      (b := fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) => p.2)
      (z := fun _ => pair y (-y)) hc (fun _ => analyticAt_const) q.2

/-- The centered matrix moment formula holds at arbitrary independent complex parameters. -/
theorem continuedRegMatrixDirichletAverage_appellF4Bailey_moment
    (r β : Fin 2 → ℂ) (x y : ℂ) (N : ℕ) :
    continuedRegMatrixDirichletAverage (appellF4BaileyMatrix x y) (fun z => (1 - z) ^ N)
      (r, β) = appellF4BaileyMoment x y N (r, β) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent_prod
    (isRegMatrixContinuation_shifted_pow (appellF4BaileyMatrix x y) N).1
    (analyticOnNhd_appellF4BaileyMoment x y N) ?_) (r, β)
  intro s γ hs hγ
  rw [(isRegMatrixContinuation_shifted_pow (appellF4BaileyMatrix x y) N).2 s γ hs hγ]
  exact native_appellF4BaileyMoment hs hγ x y N

/-- The centered binomial coefficient before deleting the vanishing odd moments. -/
def appellF4BaileyTerm (a c d x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  (ascPochhammer ℂ (p.1 + p.2)).eval (2 * a) /
      ((p.1.factorial : ℂ) * p.2.factorial) *
    regRPolynomial p.1 (c - 1 / 2) (c - 1 / 2) x (-x) *
      regRPolynomial p.2 (d - 1 / 2) (d - 1 / 2) y (-y)

/-- Duplication converts the even centered coefficients into F₄ coefficients. -/
theorem appellF4BaileyTerm_even (a c d x y : ℂ) (m n : ℕ) :
    appellF4BaileyTerm a c d x y (2 * m, 2 * n) =
      (quadraticGammaRatio (c - 1 / 2) * quadraticGammaRatio (d - 1 / 2)) *
        (regularizedAppellF4Coeff a (a + 1 / 2) c d (m, n) * (x ^ 2) ^ m * (y ^ 2) ^ n) := by
  rw [appellF4BaileyTerm, show 2 * m + 2 * n = 2 * (m + n) by omega,
    ascPochhammer_eval_double, regRPolynomial_even_opposite, regRPolynomial_even_opposite,
    regularizedAppellF4Coeff_eq,
    show c - 1 / 2 + 1 / 2 + m = c + m by ring,
    show d - 1 / 2 + 1 / 2 + n = d + n by ring,
    ← four_pow_mul_ascPochhammer_half m, ← four_pow_mul_ascPochhammer_half n, pow_add]
  have hm := ascPochhammer_eval_ne_zero_of_re_pos (show 0 < (1 / 2 : ℂ).re by norm_num) m
  have hn := ascPochhammer_eval_ne_zero_of_re_pos (show 0 < (1 / 2 : ℂ).re by norm_num) n
  simp only [one_div] at hm hn ⊢
  simp only [div_eq_mul_inv, mul_inv_rev]
  generalize (Gamma (c + m))⁻¹ = G at *
  generalize (Gamma (d + n))⁻¹ = H at *
  generalize (ascPochhammer ℂ m).eval (2 : ℂ)⁻¹ = M at *
  generalize (ascPochhammer ℂ n).eval (2 : ℂ)⁻¹ = N at *
  field_simp
  ring

/-- Odd centered coefficients vanish in either coordinate. -/
theorem appellF4BaileyTerm_eq_zero (a c d x y : ℂ) (p : ℕ × ℕ)
    (hp : Odd p.1 ∨ Odd p.2) : appellF4BaileyTerm a c d x y p = 0 := by
  rcases hp with h | h
  · rw [appellF4BaileyTerm, regRPolynomial_eq_zero_of_odd _ h]
    simp
  · rw [appellF4BaileyTerm, regRPolynomial_eq_zero_of_odd _ h]
    simp

/-- The centered double series is absolutely convergent on the full squared-argument F₄ region. -/
theorem hasSum_appellF4BaileyTerm (a c d : ℂ) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    HasSum (appellF4BaileyTerm a c d x y)
      ((quadraticGammaRatio (c - 1 / 2) * quadraticGammaRatio (d - 1 / 2)) *
        regularizedAppellF4 a (a + 1 / 2) c d (x ^ 2) (y ^ 2)) := by
  let E : ℕ × ℕ → ℕ × ℕ := fun p => (2 * p.1, 2 * p.2)
  have hE : Function.Injective E := by
    intro p q h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (by dsimp [E] at h1; omega) (by dsimp [E] at h2; omega)
  have hz : ∀ p, p ∉ range E → appellF4BaileyTerm a c d x y p = 0 := by
    intro p hp
    apply appellF4BaileyTerm_eq_zero
    by_cases h1 : Even p.1
    · by_cases h2 : Even p.2
      · obtain ⟨m, hm⟩ := h1
        obtain ⟨n, hn⟩ := h2
        exact False.elim (hp ⟨(m, n), Prod.ext (by dsimp [E]; omega) (by dsimp [E]; omega)⟩)
      · exact Or.inr (Nat.not_even_iff_odd.mp h2)
    · exact Or.inl (Nat.not_even_iff_odd.mp h1)
  apply (hE.hasSum_iff hz).mp
  have hregion : Real.sqrt ‖x ^ 2‖ + Real.sqrt ‖y ^ 2‖ < 1 := by
    simpa only [norm_pow, Real.sqrt_sq (norm_nonneg _)] using hxy
  convert (hasSum_regularizedAppellF4 a (a + 1 / 2) c d hregion).mul_left
    (quadraticGammaRatio (c - 1 / 2) * quadraticGammaRatio (d - 1 / 2)) using 1
  funext p
  exact appellF4BaileyTerm_even a c d x y p.1 p.2

/-- The centered parallelogram is contained in the disk of radius `‖x‖ + ‖y‖` about one. -/
theorem norm_appellF4BaileyMatrix_sub_one_le (x y : ℂ) (i j : Fin 2) :
    ‖appellF4BaileyMatrix x y i j - 1‖ ≤ ‖x‖ + ‖y‖ := by
  fin_cases i <;> fin_cases j
  · change ‖1 - x - y - 1‖ ≤ _
    rw [show 1 - x - y - 1 = -(x + y) by ring, norm_neg]
    exact norm_add_le _ _
  · change ‖1 - x + y - 1‖ ≤ _
    rw [show 1 - x + y - 1 = y - x by ring]
    exact (norm_sub_le _ _).trans_eq (add_comm _ _)
  · change ‖1 + x - y - 1‖ ≤ _
    rw [show 1 + x - y - 1 = x - y by ring]
    exact norm_sub_le _ _
  · change ‖1 + x + y - 1‖ ≤ _
    rw [show 1 + x + y - 1 = x + y by ring]
    exact norm_add_le _ _

/-- **Carlson (1975), (2.10)/(4.4), continued.** Bailey's restricted F₄ is a centered
parallelogram average. The division-free normalization holds at every complex parameter. -/
theorem continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_bailey
    (a c d : ℂ) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    continuedRegMatrixDirichletAverage (appellF4BaileyMatrix x y) (fun z => z ^ (-(2 * a)))
      (pair (c - 1 / 2) (c - 1 / 2), pair (d - 1 / 2) (d - 1 / 2)) =
        (quadraticGammaRatio (c - 1 / 2) * quadraticGammaRatio (d - 1 / 2)) *
          regularizedAppellF4 a (a + 1 / 2) c d (x ^ 2) (y ^ 2) := by
  have hL := hasSum_continuedRegMatrixDirichletAverage_cpow_neg
    (pair (c - 1 / 2) (c - 1 / 2)) (pair (d - 1 / 2) (d - 1 / 2))
    (appellF4BaileyMatrix x y) (2 * a) (by positivity) hxy
    (norm_appellF4BaileyMatrix_sub_one_le x y)
  have h := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr
    (hasSum_appellF4BaileyTerm a c d hxy)
  have hR := h.sigma (fun _ => hasSum_fintype _)
  apply hL.unique
  convert hR using 1
  funext N
  change _ = ∑ p : ↥(antidiagonal N), appellF4BaileyTerm a c d x y p.val
  rw [Finset.sum_coe_sort (antidiagonal N) (appellF4BaileyTerm a c d x y),
    continuedRegMatrixDirichletAverage_appellF4Bailey_moment, appellF4BaileyMoment,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := mem_antidiagonal.mp hp
  rw [appellF4BaileyTerm, ← hdeg, Nat.cast_add_choose ℂ]
  simp [regRPolynomial, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_ne_zero.mpr (p.1 + p.2).factorial_ne_zero]

/-- Bailey's parallelogram has right-half-plane entries on the full squared-argument region. -/
theorem appellF4BaileyMatrix_mem_rightHalfPlane {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    appellF4BaileyMatrix x y ∈ matrixNodeDomain carlsonRightHalfPlane := by
  intro i j
  have h := (abs_re_le_norm (appellF4BaileyMatrix x y i j - 1)).trans
    (norm_appellF4BaileyMatrix_sub_one_le x y i j)
  change 0 < (appellF4BaileyMatrix x y i j).re
  simp only [sub_re, one_re] at h
  linarith [neg_abs_le ((appellF4BaileyMatrix x y i j).re - 1)]

/-- Bailey's native regularized double average, with arbitrary complex numerator parameter. -/
theorem regMatrixDirichletAverage_eq_regularizedAppellF4_bailey (a c d : ℂ)
    (hc : 1 / 2 < c.re) (hd : 1 / 2 < d.re) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    regMatrixDirichletAverage (pair (c - 1 / 2) (c - 1 / 2))
      (pair (d - 1 / 2) (d - 1 / 2)) (appellF4BaileyMatrix x y) (fun z => z ^ (-(2 * a))) =
        (quadraticGammaRatio (c - 1 / 2) * quadraticGammaRatio (d - 1 / 2)) *
          regularizedAppellF4 a (a + 1 / 2) c d (x ^ 2) (y ^ 2) := by
  rw [← continuedRegMatrixDirichletAverage_eq_regularizedAppellF4_bailey a c d hxy]
  symm
  apply continuedRegMatrixDirichletAverage_eq_native isOpen_carlsonRightHalfPlane
    convex_carlsonRightHalfPlane
    (fun z hz => analyticAt_id.cpow analyticAt_const (Or.inl hz))
    (appellF4BaileyMatrix_mem_rightHalfPlane hxy)
  · intro i
    have h : 0 < (c - 1 / 2).re := by simp only [sub_re]; norm_num; linarith
    fin_cases i <;> exact h
  · intro i
    have h : 0 < (d - 1 / 2).re := by simp only [sub_re]; norm_num; linarith
    fin_cases i <;> exact h

/-- **Carlson (1975), (2.10)/(4.4), native normalized form.**
Bailey's restriction of F₄ is the centered parallelogram double average. -/
theorem matrixDirichletAverage_eq_appellF4_bailey (a c d : ℂ)
    (hc : 1 / 2 < c.re) (hd : 1 / 2 < d.re) {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    matrixDirichletAverage (pair (c - 1 / 2) (c - 1 / 2))
      (pair (d - 1 / 2) (d - 1 / 2)) (appellF4BaileyMatrix x y) (fun z => z ^ (-(2 * a))) =
        appellF4 a (a + 1 / 2) c d (x ^ 2) (y ^ 2) := by
  rw [matrixDirichletAverage, sum_pair, sum_pair,
    regMatrixDirichletAverage_eq_regularizedAppellF4_bailey a c d hc hd hxy, appellF4]
  have hβ : 0 < (c - 1 / 2).re := by simp only [sub_re]; norm_num; linarith
  have hγ : 0 < (d - 1 / 2).re := by simp only [sub_re]; norm_num; linarith
  have hC := Gamma_mul_quadraticGammaRatio hβ
  have hD := Gamma_mul_quadraticGammaRatio hγ
  rw [show c - 1 / 2 + 1 / 2 = c by ring] at hC
  rw [show d - 1 / 2 + 1 / 2 = d by ring] at hD
  calc
    _ = (Gamma ((c - 1 / 2) + (c - 1 / 2)) * quadraticGammaRatio (c - 1 / 2)) *
        (Gamma ((d - 1 / 2) + (d - 1 / 2)) * quadraticGammaRatio (d - 1 / 2)) *
          regularizedAppellF4 a (a + 1 / 2) c d (x ^ 2) (y ^ 2) := by ring
    _ = _ := by rw [hC, hD]

end Carlson.TwoVariable
