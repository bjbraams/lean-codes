/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.GeneratingIdentities
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Carlson.RPolynomial.TaylorContinuation

/-!
# R-polynomials with roots of unity as nodes (Exercises 6.9-13 and 6.9-14)

With the `k`-th roots of unity as nodes and equal parameters, the generating relation 6.6-1 is
`∏ⱼ (1 - t ωʲ)^(-β) = (1 - tᵏ)^(-β)` for small `t`; comparing coefficients gives the
R-polynomials, and the Taylor representation 6.3-1 gives averages over regular polygons. The
identity of the generating functions uses that the logarithm of a product of factors close to
one is the sum of their logarithms (`log_prod_one_add`).

## Main results

* `Carlson.carlsonRPolynomialNumerator_rootsOfUnity`: Exercise 6.9-13.
* `Carlson.hasSum_polygon`: Exercise 6.9-14 (the `F` part), in regularized form.
* `Carlson.log_prod_one_add`, `Carlson.prod_one_add_cpow`, `Carlson.prod_one_sub_mul_pow`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.9.
-/

open Complex Finset
@[expose] public noncomputable section
namespace Carlson

/-- The logarithm of a product of factors close to one is the sum of their logarithms. -/
theorem log_prod_one_add {α : Type*} (s : Finset α) {w : α → ℂ}
    (hw : ∀ j ∈ s, ‖w j‖ ≤ 1 / 2) (hsum : ∑ j ∈ s, 3 / 2 * ‖w j‖ < Real.pi) :
    log (∏ j ∈ s, (1 + w j)) = ∑ j ∈ s, log (1 + w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha] at hsum
    have hws : ∀ j ∈ s, ‖w j‖ ≤ 1 / 2 := fun j hj => hw j (mem_insert_of_mem hj)
    have hwa := hw a (mem_insert_self a s)
    have hpos : 0 ≤ ∑ j ∈ s, 3 / 2 * ‖w j‖ := sum_nonneg fun j _ => by positivity
    have hih := ih hws (by nlinarith [norm_nonneg (w a)])
    have hne : ∀ j ∈ insert a s, 1 + w j ≠ 0 := fun j hj h => by
      have := hw j hj
      have h1 : w j = -1 := by linear_combination h
      rw [h1, norm_neg, norm_one] at this; norm_num at this
    have hP : ∏ j ∈ s, (1 + w j) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j hj => hne j (mem_insert_of_mem hj)
    have hima : |arg (1 + w a)| ≤ 3 / 2 * ‖w a‖ := by
      rw [← log_im]; exact (abs_im_le_norm _).trans (norm_log_one_add_half_le_self hwa)
    have hims : |arg (∏ j ∈ s, (1 + w j))| ≤ ∑ j ∈ s, 3 / 2 * ‖w j‖ := by
      rw [← log_im, hih, im_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
      exact (abs_im_le_norm _).trans (norm_log_one_add_half_le_self (hws j hj))
    rw [prod_insert ha, sum_insert ha, ← hih]
    refine (log_mul_eq_add_log_iff (hne a (mem_insert_self a s)) hP).mpr ⟨?_, ?_⟩
    · linarith [(abs_le.mp hima).1, (abs_le.mp hims).1]
    · linarith [(abs_le.mp hima).2, (abs_le.mp hims).2]

/-- A product of powers of factors close to one is the power of the product. -/
theorem prod_one_add_cpow {α : Type*} (s : Finset α) {w : α → ℂ}
    (hw : ∀ j ∈ s, ‖w j‖ ≤ 1 / 2) (hsum : ∑ j ∈ s, 3 / 2 * ‖w j‖ < Real.pi) (β : ℂ) :
    ∏ j ∈ s, (1 + w j) ^ β = (∏ j ∈ s, (1 + w j)) ^ β := by
  have hne : ∀ j ∈ s, 1 + w j ≠ 0 := fun j hj h => by
    have := hw j hj
    have h1 : w j = -1 := by linear_combination h
    rw [h1, norm_neg, norm_one] at this; norm_num at this
  rw [cpow_def_of_ne_zero (prod_ne_zero_iff.mpr hne), log_prod_one_add s hw hsum, sum_mul,
    exp_sum]
  exact prod_congr rfl fun j hj => cpow_def_of_ne_zero (hne j hj) β

/-- `∏_{j < k} (1 - t ωʲ) = 1 - tᵏ` for a primitive `k`-th root of unity `ω`. -/
theorem prod_one_sub_mul_pow {ω : ℂ} {k : ℕ} (hω : IsPrimitiveRoot ω k) (hk : 0 < k) (t : ℂ) :
    ∏ j ∈ range k, (1 - t * ω ^ j) = 1 - t ^ k := by
  classical
  have : NeZero k := ⟨hk.ne'⟩
  rcases eq_or_ne t 0 with rfl | ht
  · simp [zero_pow hk.ne']
  have hpoly := congrArg (Polynomial.eval t⁻¹) (Polynomial.X_pow_sub_one_eq_prod hk hω)
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, Polynomial.eval_C] at hpoly
  have hbij : ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), (t⁻¹ - ζ) =
      ∏ j ∈ range k, (t⁻¹ - ω ^ j) := by
    refine (prod_nbij (fun j => ω ^ j) (fun j hj => ?_) (fun i hi j hj h => ?_)
      (fun ζ hζ => ?_) (fun j _ => rfl)).symm
    · rw [Polynomial.mem_nthRootsFinset hk]; rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one,
        one_pow]
    · exact hω.pow_inj (mem_range.mp hi) (mem_range.mp hj) h
    · obtain ⟨i, hi, rfl⟩ := hω.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hk 1).mp hζ)
      exact ⟨i, mem_range.mpr hi, rfl⟩
  rw [hbij] at hpoly
  have hmul : ∏ j ∈ range k, (1 - t * ω ^ j) = t ^ k * ∏ j ∈ range k, (t⁻¹ - ω ^ j) := by
    rw [← card_range k, ← prod_const, card_range, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ => by field_simp
  rw [hmul, ← hpoly, mul_sub, ← mul_pow, mul_inv_cancel₀ ht, one_pow, mul_one]

/-- **Exercise 6.9-13**, in numerator form: with the `k`-th roots of unity `1, ω, …, ω^(k-1)` as
nodes and all parameters equal to `β`, `Nₙ(β, …, β; 1, ω, …, ω^(k-1))/n!` is `(β)ₘ/m!` if
`n = km` and zero otherwise. Equivalently `R_{km+p} = 0` for `0 < p < k` and
`R_{km} = (km)! (β)ₘ/(m! (kβ)_{km})`. -/
theorem carlsonRPolynomialNumerator_rootsOfUnity {ω : ℂ} {k : ℕ} (hω : IsPrimitiveRoot ω k)
    (hk : 0 < k) (β : ℂ) (n : ℕ) :
    carlsonRPolynomialNumerator n (fun _ : Fin k => β) (fun j => ω ^ (j : ℕ)) /
        (n.factorial : ℂ) =
      if k ∣ n then (ascPochhammer ℂ (n / k)).eval β / ((n / k).factorial : ℂ) else 0 := by
  classical
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set δ : ℝ := 1 / (2 * k)
  have hδ : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hωn : ∀ j : ℕ, ‖ω ^ j‖ = 1 := fun j => by
    rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hω.pow_eq_one hk.ne', one_pow]
  set F : ℂ → ℂ := fun t => 1 / (1 - t ^ k) ^ β
  refine congrFun (coeff_eq_of_hasSum_pow hδ (F := F)
    (a := fun n => carlsonRPolynomialNumerator n (fun _ : Fin k => β) (fun j => ω ^ (j : ℕ)) /
      (n.factorial : ℂ))
    (b := fun n => if k ∣ n then (ascPochhammer ℂ (n / k)).eval β / ((n / k).factorial : ℂ)
      else 0) (fun t ht => ?_) (fun t ht => ?_)) n
  · have htz : ∀ j : Fin k, ‖t * ω ^ (j : ℕ)‖ < 1 := fun j => by
      rw [norm_mul, hωn, mul_one]; linarith
    have h := hasSum_carlsonRPolynomialNumerator_div_factorial (fun _ : Fin k => β)
      (fun j => ω ^ (j : ℕ)) t htz
    convert h using 1
    have hprod := prod_one_add_cpow (univ : Finset (Fin k)) (w := fun j => -(t * ω ^ (j : ℕ)))
      (fun j _ => by rw [norm_neg, norm_mul, hωn, mul_one]; linarith)
      (by
        simp only [norm_neg, norm_mul, hωn, mul_one, sum_const, card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have : (k : ℝ) * (3 / 2 * ‖t‖) < k * (3 / 2 * δ) := by gcongr
        have hkδ : (k : ℝ) * (3 / 2 * δ) = 3 / 4 := by simp only [δ]; field_simp; ring
        linarith [Real.two_le_pi]) β
    simp only [← sub_eq_add_neg] at hprod
    rw [Fin.prod_univ_eq_prod_range (fun j => 1 - t * ω ^ j) k, prod_one_sub_mul_pow hω hk] at hprod
    simp only [carlsonRGeneratingKernel, F, one_div, prod_inv_distrib, hprod]
  · have htk : ‖t ^ k * 1‖ < 1 := by
      rw [mul_one, norm_pow]
      calc ‖t‖ ^ k ≤ ‖t‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (by linarith) hk
        _ < 1 := by rw [pow_one]; linarith
    have h1 := hasSum_carlsonRPolynomialNumerator_div_factorial (fun _ : Unit => β)
      (fun _ => 1) (t ^ k) (fun _ => htk)
    simp only [carlsonRPolynomialNumerator_const, Finset.univ_unique, sum_singleton, one_pow,
      mul_one, carlsonRGeneratingKernel, prod_const, Finset.card_singleton, pow_one] at h1
    have hinj : Function.Injective fun m : ℕ => k * m := fun a b h => by
      simpa [hk.ne'] using h
    refine (hinj.hasSum_iff (f := fun n => (if k ∣ n then
      (ascPochhammer ℂ (n / k)).eval β / ((n / k).factorial : ℂ) else 0) * t ^ n)
      fun n hn => ?_).mp ?_
    · have : ¬ k ∣ n := fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
      simp [this]
    · refine h1.congr_fun fun m => ?_
      simp [Nat.mul_div_cancel_left m hk, pow_mul]

/-- **Exercise 6.9-14** (Dirichlet averages over a regular polygon), regularized form: if `f` is
holomorphic on a disk about `λ` of radius `R > ‖x‖`, and the nodes are the vertices
`λ + x ωʲ` of a regular `k`-gon, the continued average with all parameters equal to `β` is
`F(β, …, β; z)/Γ(kβ) = ∑ₘ f^(km)(λ) x^(km) (β)ₘ/(m! Γ(kβ + km))`. -/
theorem hasSum_polygon {ω : ℂ} {k : ℕ} (hω : IsPrimitiveRoot ω k) (hk : 0 < k) {A : ℂ}
    {R : ℝ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball A R)) {x : ℂ} (hx : ‖x‖ < R)
    {G : (Fin k → ℂ) → ℂ}
    (hG : Dirichlet.IsRegCarlsonContinuation f (fun j : Fin k => A + x * ω ^ (j : ℕ)) G)
    (β : ℂ) :
    HasSum (fun m => iteratedDeriv (k * m) f A * x ^ (k * m) *
        (ascPochhammer ℂ m).eval β / (m.factorial : ℂ) * (Gamma (k * β + (k * m : ℕ)))⁻¹)
      (G fun _ => β) := by
  have hR : 0 < R := (norm_nonneg x).trans_lt hx
  have hωn : ∀ j : ℕ, ‖ω ^ j‖ = 1 := fun j => by
    rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hω.pow_eq_one hk.ne', one_pow]
  have hz : ‖fun j : Fin k => A + x * ω ^ (j : ℕ) - A‖ < R := by
    refine (pi_norm_lt_iff hR).mpr fun j => ?_
    simp only [add_sub_cancel_left, norm_mul, hωn, mul_one]; exact hx
  have hs := hG.hasSum_taylor hf hz (fun _ => β)
  have hterm : ∀ n, iteratedDeriv n f A / (n.factorial : ℂ) *
      regCarlsonRPolynomial n (fun _ : Fin k => β) (fun j => A + x * ω ^ (j : ℕ) - A) =
      if k ∣ n then iteratedDeriv n f A * x ^ n * (ascPochhammer ℂ (n / k)).eval β /
        ((n / k).factorial : ℂ) * (Gamma (k * β + n))⁻¹ else 0 := fun n => by
    have hN := carlsonRPolynomialNumerator_rootsOfUnity hω hk β n
    have hsm := carlsonRPolynomialNumerator_smul n (fun _ : Fin k => β) (fun j => ω ^ (j : ℕ)) x
    simp only [add_sub_cancel_left]
    rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma, hsm, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hf' : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [div_eq_iff hf'] at hN
    rw [hN]
    split_ifs
    · field_simp
    · simp
  rw [funext hterm] at hs
  have hinj : Function.Injective fun m : ℕ => k * m := fun a b h => by simpa [hk.ne'] using h
  have := (hinj.hasSum_iff fun n hn => by
    have : ¬ k ∣ n := fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
    simp [this]).mpr hs
  refine this.congr_fun fun m => ?_
  simp [Nat.mul_div_cancel_left m hk]

end Carlson
