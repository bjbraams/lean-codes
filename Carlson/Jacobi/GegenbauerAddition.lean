/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.GegenbauerProduct
public import Carlson.Jacobi.FiniteExpansion
public import Carlson.Jacobi.FourierCosine
public import Carlson.Jacobi.EndpointBridge
public import Carlson.Jacobi.GegenbauerDerivative
public import ComplexAnalysis.RealUniqueness

/-!
# The addition theorems for Gegenbauer and Legendre polynomials

Carlson's Theorem 7.3-1 (Gegenbauer's addition theorem):
`C_n^ν(cos θ cos φ + x sin θ sin φ)
  = ∑ₘ (ν)ₘ sinᵐθ sinᵐφ / ((ν - 1/2)ₘ C_{n-m}^{ν+m}(1)) C_{n-m}^{ν+m}(cos θ) C_{n-m}^{ν+m}(cos φ)
    C_m^{ν-1/2}(x)`.

The proof follows Carlson. The polynomial `f(x) = C_n^ν(A + Bx)`, `A = cos θ cos φ`,
`B = sin θ sin φ`, is expanded in Jacobi polynomials with `α = β = ν - 1` on `[-1, 1]` (Theorem
7.2-2). Its coefficients are Dirichlet averages of derivatives, computed by the derivative formula
(7.3-2) and evaluated by Gegenbauer's product formula (6.11-4), which requires `re ν > 0` and
real angles. The Jacobi polynomials are Gegenbauer polynomials by (7.3-7), via Legendre's
duplication formula for Pochhammer symbols. The identity extends to complex angles by the identity
theorem from the real line, and to every `ν` at which the denominators do not vanish by analytic
continuation in `ν` on the complement of a countable set.

At `ν = 1/2` the denominators `(ν - 1/2)ₘ` vanish; Carlson passes to a limit. Here the Jacobi form
of the expansion, valid for every `re ν > 0`, is used directly: at `α = β = -1/2` the Jacobi
polynomials are Chebyshev polynomials, `pₘ(cos ψ) = cos(mψ)/2^{m-1}`, which gives the addition
theorem for Legendre polynomials (7.3-11) with Carlson's associated Legendre functions (7.3-9).

## Main definitions

* `Carlson.TwoVariable.gegenbauerAdditionSum`: the right side of (7.3-8).
* `Carlson.TwoVariable.gegenbauerAdditionJacobiSum`: its Jacobi form.
* `Carlson.TwoVariable.assocLegendre`: `P_n^m(cos θ)` in Carlson's form (7.3-9).
* `Carlson.TwoVariable.assocLegendreNeg`, `Carlson.TwoVariable.assocLegendreInt`: `P_n^{-k}` by
  (6.10-18), and `P_n^m` for integer `m`.

## Main results

* `Carlson.TwoVariable.eval_jacobiOn_gegenbauer`: formula (7.3-7).
* `Carlson.TwoVariable.gegenbauer_addition_jacobi`: the Jacobi form, for `re ν > 0`.
* `Carlson.TwoVariable.gegenbauer_addition`: Theorem 7.3-1.
* `Carlson.TwoVariable.legendre_addition`: the addition theorem (7.3-11) for Legendre polynomials.
* `Carlson.TwoVariable.legendre_integral_product`: Legendre's integral for a product, Carlson
  (6.11-6), for all complex angles.
* `Carlson.TwoVariable.gegenbauer_eq_carlsonRPolynomial`: (6.10-12) for `C_{n-k}^{1/2+k}`.
* `Carlson.TwoVariable.assocLegendreNeg_eq`: the reflection (6.10-19).
* `Carlson.TwoVariable.legendre_addition_exp`: the second form of (7.3-11).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.3.
-/

open Dirichlet
open Complex Set Filter MeasureTheory Polynomial
open scoped Topology
@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- **Carlson (7.3-7)**: the monic Jacobi polynomial on `[-1, 1]` with `α = β = ν - 1` is a
Gegenbauer polynomial, `2^m (ν - 1/2)ₘ pₘ(x) = m! C_m^{ν-1/2}(x)`. -/
theorem eval_jacobiOn_gegenbauer (ν x : ℂ) (m : ℕ)
    (h1 : (ascPochhammer ℂ m).eval (ν - 1 / 2) ≠ 0) (h2 : (ascPochhammer ℂ m).eval ν ≠ 0) :
    (jacobiOn (ν - 1) (ν - 1) (-1) 1 m).eval x * (2 ^ m * (ascPochhammer ℂ m).eval (ν - 1 / 2)) =
      (m.factorial : ℂ) * (gegenbauer (ν - 1 / 2) m).eval x := by
  have hdup := (ascPochhammer_eval_double (ν - 1 / 2) m).trans (mul_assoc _ _ _)
  rw [show ν - 1 / 2 + 1 / 2 = ν by ring, show 2 * (ν - 1 / 2) = 2 * ν - 1 by ring] at hdup
  have hsplit : (ascPochhammer ℂ (2 * m)).eval (2 * ν - 1) =
      (ascPochhammer ℂ m).eval (2 * ν - 1) * (ascPochhammer ℂ m).eval (2 * ν - 1 + m) := by
    rw [show 2 * m = m + m from two_mul m]; exact ascPochhammer_add_eval _ m m
  have hD : (ascPochhammer ℂ (2 * m)).eval (2 * ν - 1) ≠ 0 := by
    rw [hdup]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero h1 h2)
  rw [hsplit] at hD
  have hA : (ascPochhammer ℂ m).eval (2 * ν - 1) ≠ 0 := left_ne_zero_of_mul hD
  have hB : (ascPochhammer ℂ m).eval (2 * ν - 1 + m) ≠ 0 := right_ne_zero_of_mul hD
  have hB' : (ascPochhammer ℂ m).eval ((ν - 1) + (ν - 1) + m + 1) ≠ 0 := by
    convert hB using 2; ring
  have he := eval_jacobiOn_affine_monicJacobi (ν - 1) (ν - 1) 0 1 x m hB'
  simp only [zero_sub, zero_add, one_mul, one_pow] at he
  rw [he, monicJacobi, eval_mul, eval_C]
  have hg := congrArg (Polynomial.eval x) (pochhammer_mul_gegenbauer (K := ℂ) (ν - 1 / 2) m)
  simp only [eval_mul, eval_C] at hg
  rw [show ν - 1 / 2 + 1 / 2 = ν by ring, show 2 * (ν - 1 / 2) = 2 * ν - 1 by ring,
    show ν - 1 / 2 - 1 / 2 = ν - 1 by ring] at hg
  have hJ : (jacobi (ν - 1) (ν - 1) m).eval x =
      (ascPochhammer ℂ m).eval ν * (gegenbauer (ν - 1 / 2) m).eval x /
        (ascPochhammer ℂ m).eval (2 * ν - 1) := by
    rw [hg, mul_div_cancel_left₀ _ hA]
  rw [hJ, show (ν - 1) + (ν - 1) + m + 1 = 2 * ν - 1 + m by ring]
  have h4 : (4 : ℂ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  rw [hsplit] at hdup
  set P := (ascPochhammer ℂ m).eval (2 * ν - 1)
  set Q := (ascPochhammer ℂ m).eval (2 * ν - 1 + m)
  set U := (ascPochhammer ℂ m).eval ν
  set V := (ascPochhammer ℂ m).eval (ν - 1 / 2)
  set G := (gegenbauer (ν - 1 / 2) m).eval x
  calc (2 ^ m * (m.factorial : ℂ) / Q) * (U * G / P) * (2 ^ m * V)
      = (m.factorial : ℂ) * G * ((2 ^ m * 2 ^ m) * (V * U)) / (P * Q) := by ring
    _ = (m.factorial : ℂ) * G := by
      rw [← h4, ← hdup, mul_div_assoc, div_self (mul_ne_zero hA hB), mul_one]

/-- `C_k^λ(1) ≠ 0` for `re λ > 0`. -/
theorem eval_gegenbauer_one_ne_zero {lam : ℂ} (h : 0 < lam.re) (k : ℕ) :
    (gegenbauer lam k).eval 1 ≠ 0 := by
  rw [eval_gegenbauer_one]
  exact div_ne_zero (Complex.ascPochhammer_eval_ne_zero_of_re_pos (by simp; linarith) k)
    (by exact_mod_cast k.factorial_ne_zero)

/-- The Jacobi coefficients of `C_n^ν(A + B x)` with `α = β = ν - 1` on `[-1, 1]`, for real
angles with `A = cos θ cos φ`, `B = sin θ sin φ` (Carlson (7.3-5), (7.3-6)). -/
theorem carlsonJacobiCoefficient_gegenbauer_comp {ν : ℂ} (hν : 0 < ν.re) (θ φ : ℝ) {m n : ℕ}
    (hm : m ≤ n) :
    carlsonJacobiCoefficient (ν - 1) (ν - 1) (-1) 1 m
        ((gegenbauer ν n).comp (C (sin θ * sin φ) * X + C (cos θ * cos φ))) =
      (sin θ * sin φ) ^ m * 2 ^ m * (ascPochhammer ℂ m).eval ν *
        ((gegenbauer (ν + m) (n - m)).eval (cos θ) * (gegenbauer (ν + m) (n - m)).eval (cos φ)) /
        ((gegenbauer (ν + m) (n - m)).eval 1 * m.factorial) := by
  set A : ℂ := cos θ * cos φ
  set B : ℂ := sin θ * sin φ
  have hνm : 0 < (ν + m).re := by simp; positivity
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hk : k + m - m = k := by omega
  rw [hk] at *
  rw [carlsonJacobiCoefficient_apply, iterate_derivative_comp_affine,
    iterate_derivative_gegenbauer ν k m, mul_comp, C_comp, ← smul_eq_C_mul, ← smul_eq_C_mul,
    map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  -- the average of the composed polynomial
  have hparam : ν - 1 + m + 1 = ν + m := by ring
  rw [hparam]
  have hb : pair (ν + m) (ν + m) ∈ Complex.mvBetaConvergent := by
    intro i; fin_cases i <;> exact hνm
  have havg : carlsonPolynomialAverage (pair (ν + m) (ν + m)) (pair (-1) 1)
      ((gegenbauer (ν + m) k).comp (C B * X + C A)) =
      carlsonDirichletAverage (pair (ν + m) (ν + m)) (pair (cos (θ + φ)) (cos (θ - φ)))
        (fun x => (gegenbauer (ν + m) k).eval x) := by
    simp only [carlsonPolynomialAverage, LinearMap.smul_apply, smul_eq_mul]
    rw [regCarlsonPolynomialAverage_comp_affine, carlsonDirichletAverage]
    have hz : (fun i => B * pair (-1) 1 i + A) = pair (cos (θ + φ)) (cos (θ - φ)) := by
      funext i; fin_cases i
      · simp only [pair, Fin.zero_eta, Matrix.cons_val_zero, B, A]
        rw [Complex.cos_add]; ring
      · simp only [pair, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, B, A]
        rw [Complex.cos_sub]; ring
    rw [hz, regCarlsonPolynomialAverage_eq_native _ _ hb]
  rw [havg]
  have hprod := gegenbauer_product_formula hνm θ φ k
  have hG1 := eval_gegenbauer_one_ne_zero hνm k
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  rw [hprod]
  field_simp

/-- Derivatives beyond the degree annihilate Gegenbauer polynomials. -/
theorem iterate_derivative_gegenbauer_of_lt (ν : ℂ) {n m : ℕ} (h : n < m) :
    derivative^[m] (gegenbauer ν n) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
  have := iterate_derivative_gegenbauer ν 0 n
  rw [zero_add] at this
  rw [show n + j + 1 = (j + 1) + n by ring, Function.iterate_add_apply, this, gegenbauer_zero,
    mul_one, Function.iterate_succ_apply, derivative_C, iterate_derivative_zero]

/-- The right side of the addition formula in its Jacobi form (Carlson (7.2-10) with (7.3-6)),
before the Jacobi polynomials `pₘ` on `[-1, 1]` are expressed through `C_m^{ν-1/2}`. -/
def gegenbauerAdditionJacobiSum (ν : ℂ) (n : ℕ) (θ φ x : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (n + 1), (sin θ * sin φ) ^ m * 2 ^ m * (ascPochhammer ℂ m).eval ν *
    ((gegenbauer (ν + m) (n - m)).eval (cos θ) * (gegenbauer (ν + m) (n - m)).eval (cos φ)) /
    ((gegenbauer (ν + m) (n - m)).eval 1 * m.factorial) *
    (jacobiOn (ν - 1) (ν - 1) (-1) 1 m).eval x

/-- The Jacobi form of the addition theorem for real angles and `re ν > 0`. -/
theorem gegenbauer_addition_jacobi_of_real {ν : ℂ} (hν : 0 < ν.re) (n : ℕ) (θ φ : ℝ) (x : ℂ) :
    (gegenbauer ν n).eval (cos θ * cos φ + x * (sin θ * sin φ)) =
      gegenbauerAdditionJacobiSum ν n θ φ x := by
  set A : ℂ := cos θ * cos φ
  set B : ℂ := sin θ * sin φ
  set p := (gegenbauer ν n).comp (C B * X + C A)
  have hc : IsGammaRegular ((ν - 1) + (ν - 1) + 2) := by
    intro k hk
    have := congrArg Complex.re hk
    simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hexp := sum_carlsonJacobiCoefficient (ν - 1) (ν - 1) (-1) 1 hc p
  have hzero1 : ∀ m, p.natDegree < m → carlsonJacobiCoefficient (ν - 1) (ν - 1) (-1) 1 m p = 0 := by
    intro m hm
    rw [carlsonJacobiCoefficient_apply, iterate_derivative_eq_zero hm, map_zero, zero_div]
  have hzero2 : ∀ m, n < m → carlsonJacobiCoefficient (ν - 1) (ν - 1) (-1) 1 m p = 0 := by
    intro m hm
    rw [carlsonJacobiCoefficient_apply, iterate_derivative_comp_affine,
      iterate_derivative_gegenbauer_of_lt ν hm, zero_comp, mul_zero, map_zero, zero_div]
  set K := max (p.natDegree + 1) (n + 1)
  have hsum : ∑ m ∈ Finset.range (n + 1),
      carlsonJacobiCoefficient (ν - 1) (ν - 1) (-1) 1 m p • jacobiOn (ν - 1) (ν - 1) (-1) 1 m = p := by
    set f := fun m => carlsonJacobiCoefficient (ν - 1) (ν - 1) (-1) 1 m p •
      jacobiOn (ν - 1) (ν - 1) (-1) 1 m
    calc ∑ m ∈ Finset.range (n + 1), f m = ∑ m ∈ Finset.range K, f m :=
          Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _)) (fun m hmK hmn => by
            simp only [Finset.mem_range, not_lt] at hmK hmn
            simp only [f, hzero2 m (by omega), zero_smul])
      _ = ∑ m ∈ Finset.range (p.natDegree + 1), f m :=
          (Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left _ _)) (fun m hmK hmn => by
            simp only [Finset.mem_range, not_lt] at hmK hmn
            simp only [f, hzero1 m (by omega), zero_smul])).symm
      _ = p := hexp
  have hev := congrArg (Polynomial.eval x) hsum
  rw [eval_finsetSum] at hev
  have hlhs : p.eval x = (gegenbauer ν n).eval (A + x * B) := by
    simp only [p, eval_comp, eval_add, eval_mul, eval_C, eval_X]; ring_nf
  rw [← hlhs, ← hev]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [eval_smul, smul_eq_mul, carlsonJacobiCoefficient_gegenbauer_comp hν θ φ hmn]

/-- **The addition theorem, base case**: for `re ν > 0` with `(ν - 1/2)ₘ ≠ 0` for `m ≤ n`, real
`θ, φ` and every `x`, Carlson's formula (7.3-8). -/
theorem gegenbauer_addition_of_real {ν : ℂ} (hν : 0 < ν.re) (n : ℕ)
    (hh : ∀ m ≤ n, (ascPochhammer ℂ m).eval (ν - 1 / 2) ≠ 0) (θ φ : ℝ) (x : ℂ) :
    (gegenbauer ν n).eval (cos θ * cos φ + x * (sin θ * sin φ)) =
      ∑ m ∈ Finset.range (n + 1), (ascPochhammer ℂ m).eval ν * (sin θ * sin φ) ^ m /
        ((ascPochhammer ℂ m).eval (ν - 1 / 2) * (gegenbauer (ν + m) (n - m)).eval 1) *
        ((gegenbauer (ν + m) (n - m)).eval (cos θ) * (gegenbauer (ν + m) (n - m)).eval (cos φ)) *
        (gegenbauer (ν - 1 / 2) m).eval x := by
  rw [gegenbauer_addition_jacobi_of_real hν n θ φ x, gegenbauerAdditionJacobiSum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hνm : 0 < (ν + m).re := by simp; positivity
  have h1 := hh m hmn
  have h2 : (ascPochhammer ℂ m).eval ν ≠ 0 := Complex.ascPochhammer_eval_ne_zero_of_re_pos hν m
  have hJ := eval_jacobiOn_gegenbauer ν x m h1 h2
  have hG1 := eval_gegenbauer_one_ne_zero hνm (n - m)
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2m : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  have hJ' : (jacobiOn (ν - 1) (ν - 1) (-1) 1 m).eval x =
      (m.factorial : ℂ) * (gegenbauer (ν - 1 / 2) m).eval x /
        (2 ^ m * (ascPochhammer ℂ m).eval (ν - 1 / 2)) := by
    rw [eq_div_iff (mul_ne_zero h2m h1)]; exact hJ
  rw [hJ']
  field_simp

/-- The right side of Carlson's addition formula (7.3-8). -/
def gegenbauerAdditionSum (ν : ℂ) (n : ℕ) (θ φ x : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (n + 1), (ascPochhammer ℂ m).eval ν * (sin θ * sin φ) ^ m /
    ((ascPochhammer ℂ m).eval (ν - 1 / 2) * (gegenbauer (ν + m) (n - m)).eval 1) *
    ((gegenbauer (ν + m) (n - m)).eval (cos θ) * (gegenbauer (ν + m) (n - m)).eval (cos φ)) *
    (gegenbauer (ν - 1 / 2) m).eval x

/-- **The addition theorem for complex angles** when `re ν > 0` and `(ν - 1/2)ₘ ≠ 0`. -/
theorem gegenbauer_addition_of_re_pos {ν : ℂ} (hν : 0 < ν.re) (n : ℕ)
    (hh : ∀ m ≤ n, (ascPochhammer ℂ m).eval (ν - 1 / 2) ≠ 0) (θ φ x : ℂ) :
    (gegenbauer ν n).eval (cos θ * cos φ + x * (sin θ * sin φ)) =
      gegenbauerAdditionSum ν n θ φ x := by
  have hA : ∀ φ' : ℂ, AnalyticOnNhd ℂ
      (fun θ' : ℂ => (gegenbauer ν n).eval (cos θ' * cos φ' + x * (sin θ' * sin φ'))) univ :=
    fun φ' => (by fun_prop : Differentiable ℂ fun θ' : ℂ =>
      (gegenbauer ν n).eval (cos θ' * cos φ' + x * (sin θ' * sin φ'))).differentiableOn.analyticOnNhd
      isOpen_univ
  have hB : ∀ φ' : ℂ, AnalyticOnNhd ℂ (fun θ' : ℂ => gegenbauerAdditionSum ν n θ' φ' x) univ :=
    fun φ' => (by unfold gegenbauerAdditionSum; fun_prop : Differentiable ℂ fun θ' : ℂ =>
      gegenbauerAdditionSum ν n θ' φ' x).differentiableOn.analyticOnNhd isOpen_univ
  have hA' : ∀ θ' : ℂ, AnalyticOnNhd ℂ
      (fun φ' : ℂ => (gegenbauer ν n).eval (cos θ' * cos φ' + x * (sin θ' * sin φ'))) univ :=
    fun θ' => (by fun_prop : Differentiable ℂ fun φ' : ℂ =>
      (gegenbauer ν n).eval (cos θ' * cos φ' + x * (sin θ' * sin φ'))).differentiableOn.analyticOnNhd
      isOpen_univ
  have hB' : ∀ θ' : ℂ, AnalyticOnNhd ℂ (fun φ' : ℂ => gegenbauerAdditionSum ν n θ' φ' x) univ :=
    fun θ' => (by unfold gegenbauerAdditionSum; fun_prop : Differentiable ℂ fun φ' : ℂ =>
      gegenbauerAdditionSum ν n θ' φ' x).differentiableOn.analyticOnNhd isOpen_univ
  -- first extend in `θ` for real `φ`, then in `φ`
  have hθ : ∀ φr : ℝ, ∀ θ' : ℂ, (gegenbauer ν n).eval (cos θ' * cos (φr : ℂ) +
      x * (sin θ' * sin (φr : ℂ))) = gegenbauerAdditionSum ν n θ' φr x := fun φr θ' =>
    (hA φr).eqOn_of_eventuallyEq_ofReal (hB φr) isPreconnected_univ (x₀ := 0) (mem_univ _)
      (Eventually.of_forall fun θr => gegenbauer_addition_of_real hν n hh θr φr x) (mem_univ θ')
  exact (hA' θ).eqOn_of_eventuallyEq_ofReal (hB' θ) isPreconnected_univ (x₀ := 0) (mem_univ _)
    (Eventually.of_forall fun φr => hθ φr θ) (mem_univ φ)

/-- The parameters at which the denominators of the addition formula vanish form a countable
set. -/
theorem countable_gegenbauerAddition_bad (n : ℕ) :
    {ν : ℂ | ∃ m ≤ n, (ascPochhammer ℂ m).eval (ν - 1 / 2) = 0 ∨
      (gegenbauer (ν + m) (n - m)).eval 1 = 0}.Countable := by
  refine ((Set.countable_range fun k : ℕ => (1 / 2 : ℂ) - k).union
    (Set.countable_range fun k : ℕ => -(k : ℂ) / 2)).mono ?_
  rintro ν ⟨m, -, h | h⟩
  · obtain ⟨k, -, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp h
    exact Or.inl ⟨k, by linear_combination -hk⟩
  · rw [eval_gegenbauer_one, div_eq_zero_iff] at h
    rcases h with h | h
    · obtain ⟨k, -, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp h
      exact Or.inr ⟨k + 2 * m, by push_cast; linear_combination -hk / 2⟩
    · exact absurd h (by exact_mod_cast (n - m).factorial_ne_zero)

/-- **Theorem 7.3-1 (Gegenbauer's addition theorem)**: for all complex `θ, φ, x` and every `ν`
at which the denominators `(ν - 1/2)ₘ` and `C_{n-m}^{ν+m}(1)` (`m ≤ n`) do not vanish,
`C_n^ν(cos θ cos φ + x sin θ sin φ)
  = ∑ₘ (ν)ₘ sinᵐθ sinᵐφ / ((ν - 1/2)ₘ C_{n-m}^{ν+m}(1)) C_{n-m}^{ν+m}(cos θ) C_{n-m}^{ν+m}(cos φ)
    C_m^{ν-1/2}(x)`. -/
theorem gegenbauer_addition (n : ℕ) {ν : ℂ}
    (hν : ∀ m ≤ n, (ascPochhammer ℂ m).eval (ν - 1 / 2) ≠ 0 ∧
      (gegenbauer (ν + m) (n - m)).eval 1 ≠ 0) (θ φ x : ℂ) :
    (gegenbauer ν n).eval (cos θ * cos φ + x * (sin θ * sin φ)) =
      gegenbauerAdditionSum ν n θ φ x := by
  set S := {ν : ℂ | ∃ m ≤ n, (ascPochhammer ℂ m).eval (ν - 1 / 2) = 0 ∨
      (gegenbauer (ν + m) (n - m)).eval 1 = 0}
  have hS := countable_gegenbauerAddition_bad n
  have hU : IsOpen Sᶜ := by
    have : Sᶜ = ⋂ m ∈ Finset.range (n + 1), ({ν : ℂ | (ascPochhammer ℂ m).eval (ν - 1 / 2) ≠ 0} ∩
        {ν : ℂ | (gegenbauer (ν + m) (n - m)).eval 1 ≠ 0}) := by
      ext ν
      simp only [S, mem_compl_iff, mem_ofPred_eq, not_exists, not_and, not_or, mem_iInter,
        Finset.mem_range, mem_inter_iff, Nat.lt_succ_iff]
    rw [this]
    refine isOpen_biInter_finset fun m _ => (isOpen_ne_fun (by fun_prop) continuous_const).inter
      (isOpen_ne_fun ?_ continuous_const)
    exact (by unfold gegenbauer shiftedGegenbauer
              simp only [eval_comp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
              fun_prop : Continuous fun ν : ℂ => (gegenbauer (ν + m) (n - m)).eval 1)
  have hconn : IsPreconnected Sᶜ :=
    (hS.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  have hmem : ∀ μ ∈ Sᶜ, ∀ m ≤ n, (ascPochhammer ℂ m).eval (μ - 1 / 2) ≠ 0 ∧
      (gegenbauer (μ + m) (n - m)).eval 1 ≠ 0 := by
    intro μ hμ m hm
    simp only [S, mem_compl_iff, mem_ofPred_eq, not_exists, not_and, not_or] at hμ
    exact hμ m hm
  have hL : AnalyticOnNhd ℂ (fun μ : ℂ =>
      (gegenbauer μ n).eval (cos θ * cos φ + x * (sin θ * sin φ))) Sᶜ :=
    (by unfold gegenbauer shiftedGegenbauer
        simp only [eval_comp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
        fun_prop : Differentiable ℂ fun μ : ℂ =>
          (gegenbauer μ n).eval (cos θ * cos φ + x * (sin θ * sin φ))).differentiableOn.analyticOnNhd
      hU
  have hR : AnalyticOnNhd ℂ (fun μ : ℂ => gegenbauerAdditionSum μ n θ φ x) Sᶜ := by
    refine DifferentiableOn.analyticOnNhd ?_ hU
    intro μ hμ
    unfold gegenbauerAdditionSum
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hd : ∀ (k : ℕ) (f : ℂ → ℂ), Differentiable ℂ f →
        Differentiable ℂ fun μ : ℂ => (gegenbauer (f μ) k).eval 1 := by
      intro k f hf
      unfold gegenbauer shiftedGegenbauer
      simp only [eval_comp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      fun_prop
    have hd' : ∀ (k : ℕ) (f : ℂ → ℂ) (y : ℂ), Differentiable ℂ f →
        Differentiable ℂ fun μ : ℂ => (gegenbauer (f μ) k).eval y := by
      intro k f y hf
      unfold gegenbauer shiftedGegenbauer
      simp only [eval_comp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      fun_prop
    refine ((((by fun_prop : Differentiable ℂ fun μ : ℂ =>
        (ascPochhammer ℂ m).eval μ * (sin θ * sin φ) ^ m) μ).div
      (((by fun_prop : Differentiable ℂ fun μ : ℂ => (ascPochhammer ℂ m).eval (μ - 1 / 2)) μ).mul
        (hd (n - m) (fun μ => μ + m) (by fun_prop) μ))
      (mul_ne_zero (hmem μ hμ m hmn).1 (hmem μ hμ m hmn).2)).mul
      (((hd' (n - m) (fun μ => μ + m) (cos θ) (by fun_prop)) μ).mul
        ((hd' (n - m) (fun μ => μ + m) (cos φ) (by fun_prop)) μ))).mul
      ((hd' m (fun μ => μ - 1 / 2) x (by fun_prop)) μ)
  have h1 : (1 : ℂ) ∈ Sᶜ := by
    simp only [S, mem_compl_iff, mem_ofPred_eq, not_exists, not_and, not_or]
    intro m _
    refine ⟨Complex.ascPochhammer_eval_ne_zero_of_re_pos (by norm_num) m,
      eval_gegenbauer_one_ne_zero (by simp; positivity) _⟩
  have heq := hL.eqOn_of_preconnected_of_eventuallyEq hR hconn h1 (by
    filter_upwards [hU.mem_nhds h1, (Complex.continuous_re.continuousAt (x := (1 : ℂ))).eventually
      (lt_mem_nhds (show (0 : ℝ) < (1 : ℂ).re by norm_num))] with μ hμ hre
    exact gegenbauer_addition_of_re_pos hre n (fun m hm => (hmem μ hμ m hm).1) θ φ x)
  have hν' : ν ∈ Sᶜ := by
    simp only [S, mem_compl_iff, mem_ofPred_eq, not_exists, not_and, not_or]
    exact fun m hm => hν m hm
  exact heq hν'

/-- The Jacobi form of the addition theorem for complex angles and `re ν > 0`. -/
theorem gegenbauer_addition_jacobi {ν : ℂ} (hν : 0 < ν.re) (n : ℕ) (θ φ x : ℂ) :
    (gegenbauer ν n).eval (cos θ * cos φ + x * (sin θ * sin φ)) =
      gegenbauerAdditionJacobiSum ν n θ φ x := by
  have hA : ∀ φ' : ℂ, AnalyticOnNhd ℂ
      (fun θ' : ℂ => (gegenbauer ν n).eval (cos θ' * cos φ' + x * (sin θ' * sin φ'))) univ :=
    fun φ' => (by fun_prop : Differentiable ℂ fun θ' : ℂ =>
      (gegenbauer ν n).eval (cos θ' * cos φ' + x * (sin θ' * sin φ'))).differentiableOn.analyticOnNhd
      isOpen_univ
  have hB : ∀ φ' : ℂ, AnalyticOnNhd ℂ (fun θ' : ℂ => gegenbauerAdditionJacobiSum ν n θ' φ' x) univ :=
    fun φ' => (by unfold gegenbauerAdditionJacobiSum; fun_prop : Differentiable ℂ fun θ' : ℂ =>
      gegenbauerAdditionJacobiSum ν n θ' φ' x).differentiableOn.analyticOnNhd isOpen_univ
  have hA' : ∀ θ' : ℂ, AnalyticOnNhd ℂ
      (fun φ' : ℂ => (gegenbauer ν n).eval (cos θ' * cos φ' + x * (sin θ' * sin φ'))) univ :=
    fun θ' => (by fun_prop : Differentiable ℂ fun φ' : ℂ =>
      (gegenbauer ν n).eval (cos θ' * cos φ' + x * (sin θ' * sin φ'))).differentiableOn.analyticOnNhd
      isOpen_univ
  have hB' : ∀ θ' : ℂ, AnalyticOnNhd ℂ (fun φ' : ℂ => gegenbauerAdditionJacobiSum ν n θ' φ' x) univ :=
    fun θ' => (by unfold gegenbauerAdditionJacobiSum; fun_prop : Differentiable ℂ fun φ' : ℂ =>
      gegenbauerAdditionJacobiSum ν n θ' φ' x).differentiableOn.analyticOnNhd isOpen_univ
  have hθ : ∀ φr : ℝ, ∀ θ' : ℂ, (gegenbauer ν n).eval (cos θ' * cos (φr : ℂ) +
      x * (sin θ' * sin (φr : ℂ))) = gegenbauerAdditionJacobiSum ν n θ' φr x := fun φr θ' =>
    (hA φr).eqOn_of_eventuallyEq_ofReal (hB φr) isPreconnected_univ (x₀ := 0) (mem_univ _)
      (Eventually.of_forall fun θr => gegenbauer_addition_jacobi_of_real hν n θr φr x) (mem_univ θ')
  exact (hA' θ).eqOn_of_eventuallyEq_ofReal (hB' θ) isPreconnected_univ (x₀ := 0) (mem_univ _)
    (Eventually.of_forall fun φr => hθ φr θ) (mem_univ φ)

/-- Carlson's associated Legendre function in the form (7.3-9):
`P_n^m(cos θ) = (-1)^m 2^m (1/2)ₘ sinᵐθ C_{n-m}^{1/2+m}(cos θ)`, as a function of the angle. -/
def assocLegendre (n m : ℕ) (θ : ℂ) : ℂ :=
  (-1) ^ m * 2 ^ m * (ascPochhammer ℂ m).eval (1 / 2) * sin θ ^ m *
    (gegenbauer (1 / 2 + m : ℂ) (n - m)).eval (cos θ)

/-- **The addition theorem for Legendre polynomials** (Carlson (7.3-11)): for all complex
`θ, φ, ψ`, with `Pₙ = C_n^{1/2}`,
`Pₙ(cos θ cos φ + sin θ sin φ cos ψ)
  = Pₙ(cos θ) Pₙ(cos φ) + 2 ∑_{m=1}^n (n-m)!/(n+m)! P_n^m(cos θ) P_n^m(cos φ) cos mψ`. -/
theorem legendre_addition (n : ℕ) (θ φ ψ : ℂ) :
    (gegenbauer (1 / 2 : ℂ) n).eval (cos θ * cos φ + sin θ * sin φ * cos ψ) =
      (gegenbauer (1 / 2 : ℂ) n).eval (cos θ) * (gegenbauer (1 / 2 : ℂ) n).eval (cos φ) +
        2 * ∑ m ∈ Finset.Icc 1 n, ((n - m).factorial : ℂ) / ((n + m).factorial : ℂ) *
          (assocLegendre n m θ * assocLegendre n m φ) * cos (m * ψ) := by
  have h := gegenbauer_addition_jacobi (ν := 1 / 2) (by norm_num) n θ φ (cos ψ)
  rw [show cos θ * cos φ + cos ψ * (sin θ * sin φ) = cos θ * cos φ + sin θ * sin φ * cos ψ by ring]
    at h
  rw [h, gegenbauerAdditionJacobiSum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot
    (Nat.succ_pos n)]
  -- the term `m = 0`
  have h0 : (jacobiOn (1 / 2 - 1 : ℂ) (1 / 2 - 1) (-1) 1 0).eval (cos ψ) = 1 := by
    have := eval_jacobiOn_affine_monicJacobi (1 / 2 - 1 : ℂ) (1 / 2 - 1) 0 1 (cos ψ) 0 (by simp)
    simp only [zero_sub, zero_add, one_mul, pow_zero] at this
    rw [this, monicJacobi]; simp [jacobi]
  have hP1 : (gegenbauer (1 / 2 : ℂ) n).eval 1 = 1 := by
    rw [eval_gegenbauer_one, show (2 : ℂ) * (1 / 2) = 1 by norm_num, ascPochhammer_eval_one]
    exact div_self (by exact_mod_cast n.factorial_ne_zero)
  simp only [pow_zero, Nat.cast_zero, add_zero, Nat.sub_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, one_mul, ascPochhammer_zero, eval_one, h0, hP1, div_one]
  congr 1
  rw [Finset.mul_sum, show Finset.Ico (0 + 1) (n + 1) = Finset.Icc 1 n by
    ext m; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm1, hmn⟩ := Finset.mem_Icc.mp hm
  have hm0 : m ≠ 0 := by omega
  -- Chebyshev evaluation of the Jacobi polynomial at `α = β = -1/2`
  have hP : (ascPochhammer ℂ m).eval ((1 / 2 - 1 : ℂ) + (1 / 2 - 1) + m + 1) ≠ 0 := by
    rw [show (1 / 2 - 1 + (1 / 2 - 1) + m + 1 : ℂ) = m by ring]
    exact Complex.ascPochhammer_eval_ne_zero_of_re_pos (by simp; exact_mod_cast Nat.pos_of_ne_zero hm0) m
  have hJ := eval_jacobiOn_affine_monicJacobi (1 / 2 - 1 : ℂ) (1 / 2 - 1) 0 1 (cos ψ) m hP
  simp only [zero_sub, zero_add, one_mul, one_pow] at hJ
  rw [show (1 / 2 - 1 : ℂ) = -1 / 2 by norm_num] at hJ
  rw [show (1 / 2 - 1 : ℂ) = -1 / 2 by norm_num, hJ, eval_monicJacobi_neg_half_cos m hm0]
  -- the Pochhammer bookkeeping: `C_{n-m}^{1/2+m}(1) m! = (n+m)!/(4^m (1/2)ₘ (n-m)!)`
  have hC1 : (gegenbauer (1 / 2 + m : ℂ) (n - m)).eval 1 =
      ((n + m).factorial : ℂ) / ((2 * m).factorial * (n - m).factorial) := by
    rw [eval_gegenbauer_one, show (2 : ℂ) * (1 / 2 + m) = 1 + (2 * m : ℕ) by push_cast; ring]
    have hmul := congrArg (Polynomial.eval (1 : ℂ)) (ascPochhammer_mul (S := ℂ) (2 * m) (n - m))
    rw [eval_mul, eval_comp, eval_add, eval_X, eval_natCast, ascPochhammer_eval_one,
      ascPochhammer_eval_one, show 2 * m + (n - m) = n + m by omega] at hmul
    rw [show (1 : ℂ) + (2 * m : ℕ) = 1 + ((2 * m : ℕ) : ℂ) from rfl, add_comm (1 : ℂ)]
    have hf : ((2 * m).factorial : ℂ) ≠ 0 := by exact_mod_cast (2 * m).factorial_ne_zero
    have hnm'' : ((n - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
    rw [eq_div_iff (mul_ne_zero hf hnm''), ← hmul, add_comm ((2 * m : ℕ) : ℂ) 1]
    field_simp
  have hdup : ((2 * m).factorial : ℂ) = 4 ^ m * (ascPochhammer ℂ m).eval (1 / 2) * m.factorial := by
    have := (ascPochhammer_eval_double (1 / 2 : ℂ) m).trans (mul_assoc _ _ _)
    rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, ascPochhammer_eval_one,
      show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, ascPochhammer_eval_one] at this
    rw [this]; ring
  have hL : assocLegendre n m θ * assocLegendre n m φ =
      4 ^ m * (ascPochhammer ℂ m).eval (1 / 2) ^ 2 * (sin θ * sin φ) ^ m *
        ((gegenbauer (1 / 2 + m : ℂ) (n - m)).eval (cos θ) *
          (gegenbauer (1 / 2 + m : ℂ) (n - m)).eval (cos φ)) := by
    simp only [assocLegendre]
    have hs : (-1 : ℂ) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
    have h4 : (4 : ℂ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    rw [h4, mul_pow]
    linear_combination (2 ^ m * 2 ^ m * (ascPochhammer ℂ m).eval (1 / 2) ^ 2 *
      (sin θ ^ m * sin φ ^ m) * ((gegenbauer (1 / 2 + m : ℂ) (n - m)).eval (cos θ) *
        (gegenbauer (1 / 2 + m : ℂ) (n - m)).eval (cos φ))) * hs
  rw [hL, hC1, hdup]
  have hnm : ((n + m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n + m).factorial_ne_zero
  have hnm' : ((n - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
  have hmf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hP0 : (ascPochhammer ℂ m).eval (1 / 2 : ℂ) ≠ 0 :=
    Complex.ascPochhammer_eval_ne_zero_of_re_pos (by norm_num) m
  have hpow : (2 : ℂ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h4 : (4 : ℂ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  rw [h4, hpow]
  field_simp


/-- `∫₀^π cos (m ψ) dψ = 0` for a positive integer `m`, as a complex integral. -/
theorem integral_cos_nat_mul_eq_zero {m : ℕ} (hm : m ≠ 0) :
    ∫ ψ in (0 : ℝ)..Real.pi, cos ((m : ℂ) * (ψ : ℂ)) = 0 := by
  have hre : ∀ ψ : ℝ, cos ((m : ℂ) * (ψ : ℂ)) = ((Real.cos (m * ψ) : ℝ) : ℂ) := fun ψ => by
    push_cast; ring_nf
  simp_rw [hre]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_comp_mul_left
    (fun x => Real.cos x) (by exact_mod_cast hm : (m : ℝ) ≠ 0), integral_cos]
  rw [Real.sin_nat_mul_pi, mul_zero, Real.sin_zero, sub_zero, smul_zero, ofReal_zero]

/-- **Legendre's integral for a product** (Carlson (6.11-6)): for all complex `θ, φ`,
`(1/π) ∫₀^π Pₙ(cos θ cos φ + sin θ sin φ cos ψ) dψ = Pₙ(cos θ) Pₙ(cos φ)`, with `Pₙ = C_n^{1/2}`.
It is the case `ν = 1/2` of Gegenbauer's product formula 6.11-4 after `u = sin²(ψ/2)`; here it is
obtained by integrating the addition theorem (7.3-11) over `ψ`. -/
theorem legendre_integral_product (n : ℕ) (θ φ : ℂ) :
    (1 / Real.pi : ℂ) * ∫ ψ in (0 : ℝ)..Real.pi,
        (gegenbauer (1 / 2 : ℂ) n).eval (cos θ * cos φ + sin θ * sin φ * cos (ψ : ℂ)) =
      (gegenbauer (1 / 2 : ℂ) n).eval (cos θ) * (gegenbauer (1 / 2 : ℂ) n).eval (cos φ) := by
  set P := (gegenbauer (1 / 2 : ℂ) n).eval (cos θ) * (gegenbauer (1 / 2 : ℂ) n).eval (cos φ)
  set c : ℕ → ℂ := fun m => ((n - m).factorial : ℂ) / ((n + m).factorial : ℂ) *
    (assocLegendre n m θ * assocLegendre n m φ)
  have hfun : (fun ψ : ℝ => (gegenbauer (1 / 2 : ℂ) n).eval
      (cos θ * cos φ + sin θ * sin φ * cos (ψ : ℂ))) =
      fun ψ : ℝ => P + 2 * ∑ m ∈ Finset.Icc 1 n, c m * cos ((m : ℂ) * (ψ : ℂ)) :=
    funext fun ψ => legendre_addition n θ φ ψ
  have hcos : ∀ m : ℕ, IntervalIntegrable (fun ψ : ℝ => cos ((m : ℂ) * (ψ : ℂ))) volume 0
      Real.pi := fun m =>
    (by fun_prop : Continuous fun ψ : ℝ => cos ((m : ℂ) * (ψ : ℂ))).intervalIntegrable _ _
  have hsum : ∫ ψ in (0 : ℝ)..Real.pi, ∑ m ∈ Finset.Icc 1 n, c m * cos ((m : ℂ) * (ψ : ℂ)) =
      0 := by
    rw [intervalIntegral.integral_finsetSum fun m _ => (hcos m).const_mul _]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [intervalIntegral.integral_const_mul,
      integral_cos_nat_mul_eq_zero (by have := (Finset.mem_Icc.mp hm).1; omega), mul_zero]
  have hint2 : IntervalIntegrable (fun ψ : ℝ =>
      2 * ∑ m ∈ Finset.Icc 1 n, c m * cos ((m : ℂ) * (ψ : ℂ))) volume 0 Real.pi :=
    (by fun_prop : Continuous fun ψ : ℝ =>
      2 * ∑ m ∈ Finset.Icc 1 n, c m * cos ((m : ℂ) * (ψ : ℂ))).intervalIntegrable _ _
  have h2 : ∫ ψ in (0 : ℝ)..Real.pi,
      2 * ∑ m ∈ Finset.Icc 1 n, c m * cos ((m : ℂ) * (ψ : ℂ)) = 0 := by
    rw [intervalIntegral.integral_const_mul, hsum, mul_zero]
  rw [hfun, intervalIntegral.integral_add intervalIntegrable_const hint2, h2,
    intervalIntegral.integral_const]
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [sub_zero, add_zero, Complex.real_smul]
  field_simp

/-- Carlson's associated Legendre function of negative order, defined by the last member of
(6.10-18) with `m = -k`:
`P_n^{-k}(cos θ) = 2ⁿ (1/2)ₙ/(n+k)! sinᵏθ R_{n-k}(-n, -n; cos θ + 1, cos θ - 1)`. -/
def assocLegendreNeg (n k : ℕ) (θ : ℂ) : ℂ :=
  2 ^ n * (ascPochhammer ℂ n).eval (1 / 2) / (n + k).factorial * sin θ ^ k *
    (carlsonRPolynomialNumerator₂ (n - k) (-(n : ℂ)) (-(n : ℂ)) (cos θ + 1) (cos θ - 1) /
      (ascPochhammer ℂ (n - k)).eval (-2 * (n : ℂ)))

/-- Carlson's (6.10-12) at `ν = 1/2 + k`: the Gegenbauer polynomial `C_{n-k}^{1/2+k}` as an
R-polynomial with parameters `(-n, -n)`. -/
theorem gegenbauer_eq_carlsonRPolynomial {n k : ℕ} (hk : k ≤ n) (x : ℂ) :
    ((n - k).factorial : ℂ) * (gegenbauer (1 / 2 + k : ℂ) (n - k)).eval x =
      2 ^ (n - k) * (ascPochhammer ℂ (n - k)).eval (1 / 2 + (k : ℂ)) *
        (carlsonRPolynomialNumerator₂ (n - k) (-(n : ℂ)) (-(n : ℂ)) (x + 1) (x - 1) /
          (ascPochhammer ℂ (n - k)).eval (-2 * (n : ℂ))) := by
  set N := n - k
  have h1 : (ascPochhammer ℂ N).eval ((k + 1 : ℂ) - 1 / 2) ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) N
  have h2 : (ascPochhammer ℂ N).eval ((k + 1 : ℂ)) ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by simp; positivity) N
  have hG := eval_jacobiOn_gegenbauer (k + 1) x N h1 h2
  have hJ := eval_jacobiOn_eq_numerator ((k + 1 : ℂ) - 1) ((k + 1 : ℂ) - 1) (-1) 1 x N (by
    rw [show ((k + 1 : ℂ) - 1) + ((k + 1 : ℂ) - 1) + N + 1 = ((2 * k + N + 1 : ℕ) : ℂ) by
      push_cast; ring]
    exact ascPochhammer_eval_ne_zero_of_re_pos (by rw [natCast_re]; positivity) N)
  have hn : (n : ℂ) = k + N := by simp only [N]; rw [Nat.cast_sub hk]; ring
  rw [hJ] at hG
  rw [show (k + 1 : ℂ) - 1 / 2 = 1 / 2 + k by ring] at hG
  rw [← hG]
  rw [show -((k + 1 : ℂ) - 1) - N = -(n : ℂ) by rw [hn]; ring,
    show -((k + 1 : ℂ) - 1) - ((k + 1 : ℂ) - 1) - 2 * N = -2 * (n : ℂ) by rw [hn]; ring,
    show x - -1 = x + 1 by ring]
  ring

/-- Carlson's (6.10-19): `P_n^{-k}/(n-k)! = (-1)ᵏ P_n^k/(n+k)!`, for `k ≤ n` and every complex
angle. -/
theorem assocLegendreNeg_eq {n k : ℕ} (hk : k ≤ n) (θ : ℂ) :
    assocLegendreNeg n k θ =
      (-1) ^ k * (((n - k).factorial : ℂ) / (n + k).factorial) * assocLegendre n k θ := by
  have G := gegenbauer_eq_carlsonRPolynomial hk (cos θ)
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp only [Nat.add_sub_cancel_left] at G ⊢
  have hP : (ascPochhammer ℂ N).eval (1 / 2 + (k : ℂ)) ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by simp; positivity) N
  have h2 : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero _ two_ne_zero
  set Rv := carlsonRPolynomialNumerator₂ N (-((k + N : ℕ) : ℂ)) (-((k + N : ℕ) : ℂ))
    (cos θ + 1) (cos θ - 1) / (ascPochhammer ℂ N).eval (-2 * ((k + N : ℕ) : ℂ))
  have hR : Rv = (N.factorial : ℂ) * (gegenbauer (1 / 2 + k : ℂ) N).eval (cos θ) /
      (2 ^ N * (ascPochhammer ℂ N).eval (1 / 2 + (k : ℂ))) := by
    rw [eq_div_iff (mul_ne_zero h2 hP), G]; ring
  have hmul := congrArg (eval (1 / 2 : ℂ)) (ascPochhammer_mul ℂ k N)
  simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at hmul
  unfold assocLegendreNeg assocLegendre
  simp only [Nat.add_sub_cancel_left]
  simp only [Rv] at hR
  push_cast at hR ⊢
  rw [hR, ← hmul, pow_add]
  have hs : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hf : ((k + N + k).factorial : ℂ) ≠ 0 := by exact_mod_cast (k + N + k).factorial_ne_zero
  generalize (ascPochhammer ℂ N).eval (1 / 2 + (k : ℂ)) = P at hP ⊢
  generalize (gegenbauer (1 / 2 + k : ℂ) N).eval (cos θ) = C
  rw [show (-1 : ℂ) ^ k * ((N.factorial : ℂ) / (k + N + k).factorial) *
      ((-1) ^ k * 2 ^ k * (ascPochhammer ℂ k).eval (1 / 2) * sin θ ^ k * C) =
      ((-1) ^ k * (-1) ^ k) * ((N.factorial : ℂ) / (k + N + k).factorial) *
      (2 ^ k * (ascPochhammer ℂ k).eval (1 / 2) * sin θ ^ k * C) by ring, hs, one_mul]
  field_simp

/-- The associated Legendre function `P_n^m(cos θ)` for integer `m`: Carlson's form (7.3-9) for
`m ≥ 0` and the last member of (6.10-18) for `m < 0`. -/
def assocLegendreInt (n : ℕ) (m : ℤ) (θ : ℂ) : ℂ :=
  if 0 ≤ m then assocLegendre n m.toNat θ else assocLegendreNeg n (-m).toNat θ

/-- A sum over `[-n, n]` as the middle term plus symmetric pairs. -/
theorem sum_Icc_neg_self {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℤ → M) :
    ∑ m ∈ Finset.Icc (-(n : ℤ)) n, g m = g 0 + ∑ k ∈ Finset.Icc 1 n, (g k + g (-k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hI : Finset.Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ) =
        insert (-((n + 1 : ℕ) : ℤ)) (insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) n)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hI, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      Finset.sum_Icc_succ_top (by omega)]
    push_cast
    abel

/-- **The addition theorem for Legendre polynomials**, second form (Carlson (7.3-11)): for all
complex `θ, φ, ψ`,
`Pₙ(cos θ cos φ + sin θ sin φ cos ψ) = ∑_{m=-n}^{n} (-1)ᵐ P_n^m(cos θ) P_n^{-m}(cos φ) e^{imψ}`. -/
theorem legendre_addition_exp (n : ℕ) (θ φ ψ : ℂ) :
    (gegenbauer (1 / 2 : ℂ) n).eval (cos θ * cos φ + sin θ * sin φ * cos ψ) =
      ∑ m ∈ Finset.Icc (-(n : ℤ)) n, (-1) ^ m * assocLegendreInt n m θ *
        assocLegendreInt n (-m) φ * exp (m * ψ * I) := by
  rw [legendre_addition, sum_Icc_neg_self]
  congr 1
  · simp [assocLegendreInt, assocLegendre]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    have hpos : ¬ (0 : ℤ) ≤ -(k : ℤ) := by omega
    simp only [assocLegendreInt, neg_neg, Nat.cast_nonneg, hpos, ↓reduceIte,
      Int.toNat_natCast, zpow_neg, zpow_natCast]
    rw [assocLegendreNeg_eq hkn, assocLegendreNeg_eq hkn]
    have hs : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    have hinv : ((-1 : ℂ) ^ k)⁻¹ = (-1) ^ k := by rw [← inv_pow, inv_neg, inv_one]
    rw [hinv, cos, show (k : ℂ) * ψ * I = ↑k * ψ * I from rfl,
      show ((-(k : ℤ) : ℤ) : ℂ) * ψ * I = -(k * ψ * I) by push_cast; ring,
      show -((k : ℂ) * ψ) * I = -(k * ψ * I) by ring]
    linear_combination -(((n - k).factorial : ℂ) / (n + k).factorial * assocLegendre n k θ *
      assocLegendre n k φ * (exp (k * ψ * I) + exp (-(k * ψ * I)))) * hs

end Carlson.TwoVariable
end
