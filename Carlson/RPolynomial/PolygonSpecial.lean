/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.RootsOfUnity
public import Carlson.RPolynomial.EqualParameterBounds
public import Carlson.S.Continuation
public import Carlson.R.SlitIntegral

/-!
# S and R functions over a regular polygon (Exercise 6.9-14)

`hasSum_polygon` expands the average of `f` over the vertices of a regular `k`-gon in the
derivatives `f^{(km)}(λ)`. With Gauss's multiplication formula
`(kβ)_{km} = k^{km} ∏_{j<k} (β + j/k)ₘ` this becomes a generalized hypergeometric series: for
`f = exp` the S-function is `e^λ ₀F_{k-1}`, and for `f(w) = w^{-a}` the R-function is
`λ^{-a} ₖF_{k-1}`.

## Main results

* `Carlson.ascPochhammer_eval_mul_nat`: Gauss's multiplication formula for Pochhammer symbols.
* `Carlson.hasSum_carlsonS_polygon`: Exercise 6.9-14, the S-function.
* `Carlson.hasSum_carlsonR_polygon`: Exercise 6.9-14, the R-function.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.9.
-/

open Complex Finset Filter
open scoped Topology

@[expose] public noncomputable section

namespace Carlson

/-- The ascending Pochhammer symbol as a product over `range n`. -/
theorem ascPochhammer_eval_eq_prod_range (s : ℂ) (n : ℕ) :
    (ascPochhammer ℂ n).eval s = ∏ j ∈ range n, (s + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, ih, prod_range_succ]
    simp

/-- **Gauss's multiplication formula** for Pochhammer symbols:
`(kβ)_{km} = k^{km} ∏_{j<k} (β + j/k)ₘ`. -/
theorem ascPochhammer_eval_mul_nat {k : ℕ} (hk : 0 < k) (β : ℂ) (m : ℕ) :
    (ascPochhammer ℂ (k * m)).eval (k * β) =
      (k : ℂ) ^ (k * m) * ∏ j ∈ range k, (ascPochhammer ℂ m).eval (β + j / k) := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show k * (m + 1) = k * m + k by ring, ascPochhammer_eval_add, ih]
    have hprod : (ascPochhammer ℂ k).eval (k * β + (k * m : ℕ)) =
        (k : ℂ) ^ k * ∏ j ∈ range k, (β + j / k + m) := by
      rw [ascPochhammer_eval_eq_prod_range, ← card_range k, ← prod_const, card_range,
        ← prod_mul_distrib]
      refine prod_congr rfl fun j _ => ?_
      push_cast; field_simp; ring
    rw [hprod]
    simp_rw [ascPochhammer_succ_eval]
    rw [prod_mul_distrib, pow_add]
    ring

/-- All iterated derivatives of `exp` are `exp`. -/
theorem iteratedDeriv_exp' (n : ℕ) : iteratedDeriv n exp = exp := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, Complex.deriv_exp]

/-- Iterated derivatives of a principal power on the slit plane. -/
theorem iteratedDeriv_cpow_const_of_mem_slitPlane (t : ℂ) (n : ℕ) {w : ℂ} (hw : w ∈ slitPlane) :
    iteratedDeriv n (fun u : ℂ => u ^ t) w = (descPochhammer ℂ n).eval t * w ^ (t - n) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    have he : iteratedDeriv n (fun u : ℂ => u ^ t) =ᶠ[𝓝 w]
        fun u => (descPochhammer ℂ n).eval t * u ^ (t - n) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hw] with u hu using ih hu
    have hd := ((hasDerivAt_id w).cpow_const (c := t - n) hw).const_mul
      ((descPochhammer ℂ n).eval t)
    simp only [id] at hd
    rw [iteratedDeriv_succ, he.deriv_eq, hd.deriv, descPochhammer_succ_eval]
    push_cast
    ring_nf

/-- The full product `∏_{j<k} (β + j/k)ₘ` splits off its `j = 0` factor `(β)ₘ`. -/
theorem prod_range_ascPochhammer_eq {k : ℕ} (hk : 0 < k) (β : ℂ) (m : ℕ) :
    ∏ j ∈ range k, (ascPochhammer ℂ m).eval (β + j / k) =
      (ascPochhammer ℂ m).eval β * ∏ j ∈ Ico 1 k, (ascPochhammer ℂ m).eval (β + j / k) := by
  rw [range_eq_Ico, prod_eq_prod_Ico_succ_bot hk]
  simp

/-- Common bookkeeping: `Γ(kβ) / Γ(kβ + km) = 1/(k^{km} (β)ₘ ∏_{1≤j<k} (β + j/k)ₘ)`, with all
factors nonzero when `kβ` is not a nonpositive integer. -/
theorem Gamma_add_mul_nat_eq {k : ℕ} (hk : 0 < k) {β : ℂ} (hβ : ∀ m : ℕ, (k : ℂ) * β ≠ -m)
    (m : ℕ) :
    Gamma ((k : ℂ) * β + (k * m : ℕ)) = (k : ℂ) ^ (k * m) * (ascPochhammer ℂ m).eval β *
        (∏ j ∈ Ico 1 k, (ascPochhammer ℂ m).eval (β + j / k)) * Gamma (k * β) ∧
      Gamma (k * β) ≠ 0 ∧ (ascPochhammer ℂ m).eval β ≠ 0 ∧
        ∏ j ∈ Ico 1 k, (ascPochhammer ℂ m).eval (β + j / k) ≠ 0 := by
  have hG := Gamma_ne_zero hβ
  have h := Gamma_add_nat_div_Gamma_eq ((k : ℂ) * β) hβ (n := k * m)
  have hmul := ascPochhammer_eval_mul_nat hk β m
  rw [prod_range_ascPochhammer_eq hk] at hmul
  have hΓ' : Gamma ((k : ℂ) * β + (k * m : ℕ)) =
      (ascPochhammer ℂ (k * m)).eval ((k : ℂ) * β) * Gamma (k * β) := by
    rw [← h, div_mul_cancel₀ _ hG]
  have hne : Gamma ((k : ℂ) * β + (k * m : ℕ)) ≠ 0 := Gamma_ne_zero fun j hj =>
    hβ (j + k * m) (by push_cast at hj ⊢; linear_combination hj)
  have hpoch : (ascPochhammer ℂ (k * m)).eval ((k : ℂ) * β) ≠ 0 := fun h0 =>
    hne (by rw [hΓ', h0, zero_mul])
  rw [hmul] at hpoch hΓ'
  exact ⟨hΓ'.trans (by ring), hG, fun h0 => hpoch (by rw [h0]; ring),
    fun h0 => hpoch (by rw [h0]; ring)⟩

/-- **Exercise 6.9-14, the S-function**: if the nodes are the vertices `λ + x ωʲ` of a regular
`k`-gon and `kβ` is not a nonpositive integer, then
`S(β, …, β; z) = e^λ ₀F_{k-1}[β + 1/k, …, β + (k-1)/k; (x/k)^k]`. -/
theorem hasSum_carlsonS_polygon {ω : ℂ} {k : ℕ} (hω : IsPrimitiveRoot ω k) (hk : 0 < k)
    (A x β : ℂ) (hβ : ∀ m : ℕ, (k : ℂ) * β ≠ -m) :
    HasSum (fun m : ℕ => exp A * (((x / k) ^ k) ^ m /
        ((∏ j ∈ Ico 1 k, (ascPochhammer ℂ m).eval (β + j / k)) * m.factorial)))
      (carlsonS (fun _ : Fin k => β) (fun j : Fin k => A + x * ω ^ (j : ℕ))) := by
  set z : Fin k → ℂ := fun j => A + x * ω ^ (j : ℕ)
  have hG : Dirichlet.IsRegCarlsonContinuation exp z (regCarlsonSSeries z) :=
    isRegCarlsonSContinuation_series z
  have hf : AnalyticOnNhd ℂ exp (Metric.ball A (‖x‖ + 1)) := fun w _ =>
    Complex.differentiable_exp.analyticAt w
  have h := hasSum_polygon hω hk hf (by linarith [norm_nonneg x]) hG β
  have hsum : ∑ _i : Fin k, β = k * β := by simp
  unfold carlsonS regCarlsonS
  rw [hsum]
  refine (h.mul_left (Gamma (k * β))).congr_fun fun m => ?_
  obtain ⟨hΓ, hG0, hb, hP⟩ := Gamma_add_mul_nat_eq hk hβ m
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkm : (k : ℂ) ^ (k * m) ≠ 0 := pow_ne_zero _ hk0
  have hf' : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  rw [iteratedDeriv_exp', hΓ, ← pow_mul, div_pow]
  generalize Gamma ((k : ℂ) * β) = G at hG0 ⊢
  generalize ∏ j ∈ Ico 1 k, (ascPochhammer ℂ m).eval (β + j / k) = P at hP ⊢
  field_simp

/-- **Exercise 6.9-14, the R-function**: if the nodes are the vertices `λ + x ωʲ` of a regular
`k`-gon inside a disk `B(λ, R)` contained in the slit plane, and `kβ` is not a nonpositive
integer, then `R_{-a}(β, …, β; z) =
λ^{-a} ₖF_{k-1}[a/k, (a+1)/k, …, (a+k-1)/k; β + 1/k, …, β + (k-1)/k; (-x/λ)^k]`. -/
theorem hasSum_carlsonR_polygon {ω : ℂ} {k : ℕ} (hω : IsPrimitiveRoot ω k) (hk : 0 < k)
    {A x : ℂ} {R : ℝ} (hball : Metric.ball A R ⊆ slitPlane) (hx : ‖x‖ < R) (a β : ℂ)
    (hβ : ∀ m : ℕ, (k : ℂ) * β ≠ -m) :
    HasSum (fun m : ℕ => A ^ (-a) * ((∏ j ∈ range k, (ascPochhammer ℂ m).eval ((a + j) / k)) *
        ((-x / A) ^ k) ^ m /
          ((∏ j ∈ Ico 1 k, (ascPochhammer ℂ m).eval (β + j / k)) * m.factorial)))
      (carlsonR (-a) (fun _ : Fin k => β) (fun j : Fin k => A + x * ω ^ (j : ℕ))) := by
  set z : Fin k → ℂ := fun j => A + x * ω ^ (j : ℕ)
  have hR : 0 < R := (norm_nonneg x).trans_lt hx
  have hA : A ∈ slitPlane := hball (Metric.mem_ball_self hR)
  have hA0 : A ≠ 0 := slitPlane_ne_zero hA
  have hωn : ∀ j : ℕ, ‖ω ^ j‖ = 1 := fun j => by
    rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hω.pow_eq_one hk.ne', one_pow]
  have hzball : Set.range z ⊆ Metric.ball A R := by
    rintro _ ⟨j, rfl⟩
    simp only [z, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, hωn, mul_one]
    exact hx
  have hhull : convexHull ℝ (Set.range z) ⊆ slitPlane :=
    (convexHull_min hzball (convex_ball A R)).trans hball
  have hG := isRegCarlsonRContinuation_regCarlsonR_of_convexHull (-a) hhull
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => w ^ (-a)) (Metric.ball A R) := fun w hw =>
    analyticAt_id.cpow analyticAt_const (hball hw)
  have h := hasSum_polygon hω hk hf hx hG β
  have hsum : ∑ _i : Fin k, β = k * β := by simp
  unfold carlsonR
  rw [hsum]
  refine (h.mul_left (Gamma (k * β))).congr_fun fun m => ?_
  obtain ⟨hΓ, hG0, hb, hP⟩ := Gamma_add_mul_nat_eq hk hβ m
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkm : (k : ℂ) ^ (k * m) ≠ 0 := pow_ne_zero _ hk0
  have hf' : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hAkm : A ^ (k * m) ≠ 0 := pow_ne_zero _ hA0
  have hdesc : (descPochhammer ℂ (k * m)).eval (-a) =
      (-1) ^ (k * m) * (ascPochhammer ℂ (k * m)).eval a := by
    have := ascPochhammer_eval_neg_eq_descPochhammer (R := ℂ) (-a) (k * m)
    rw [neg_neg] at this
    rw [this, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  have hgauss := ascPochhammer_eval_mul_nat hk (a / k) m
  rw [show (k : ℂ) * (a / k) = a by field_simp] at hgauss
  have hprod : ∏ j ∈ range k, (ascPochhammer ℂ m).eval (a / k + j / k) =
      ∏ j ∈ range k, (ascPochhammer ℂ m).eval ((a + j) / k) :=
    prod_congr rfl fun j _ => by rw [add_div]
  rw [hprod] at hgauss
  rw [iteratedDeriv_cpow_const_of_mem_slitPlane _ _ hA, hdesc, hgauss, hΓ,
    show -a - ((k * m : ℕ) : ℂ) = -a - ((k * m : ℕ) : ℂ) from rfl, cpow_sub _ _ hA0,
    cpow_natCast, ← pow_mul, div_pow, neg_pow x]
  generalize Gamma ((k : ℂ) * β) = G at hG0 ⊢
  generalize ∏ j ∈ Ico 1 k, (ascPochhammer ℂ m).eval (β + j / k) = P at hP ⊢
  field_simp

end Carlson
