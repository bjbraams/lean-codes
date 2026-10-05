/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# A Schwartz function of double-exponential type

For `c : ι → ℝ` with positive coordinates, the function

`y ↦ exp (∑ i, (c i * y i - exp (y i)))`

on `EuclideanSpace ℝ ι` is a Schwartz function: in each coordinate it decays like `exp (c i y i)`
as `y i → -∞` and double-exponentially as `y i → ∞`. It is the multivariable Mellin weight of
`e^(-∑ x)` in logarithmic coordinates `x = exp y`.

The derivative bounds come from Faà di Bruno's estimate `norm_iteratedFDeriv_comp_le` applied to
`exp ∘ P`, with `P y = ∑ i, (c i * y i - exp (y i))`: every derivative of positive order of `P`
at `y` has norm at most `∑ i, (|c i| + exp (y i))`. The resulting weighted bound factors into
one-variable bounds `(1 + |s|)^k (K + e^s)^n e^(a s - e^s) ≤ C`.

## Main results

* `pow_mul_exp_exp_le`: the one-variable bound.
* `expExpSchwartz`: the Schwartz function, with `expExpSchwartz_apply`.
-/

@[expose] public noncomputable section

open Real Set
open scoped ContDiff Nat

/-- **One-variable bound.** For `a > 0` and `K ≥ 0`,
`(1 + |s|)^k (K + e^s)^n e^(a s - e^s)` is bounded on `ℝ`. -/
theorem pow_mul_exp_exp_le {a : ℝ} (ha : 0 < a) {K : ℝ} (hK : 0 ≤ K) (k n : ℕ) :
    ∃ C, ∀ s : ℝ, (1 + |s|) ^ k * (K + exp s) ^ n * exp (a * s - exp s) ≤ C := by
  set M : ℝ := k + n + a
  have hM : 0 < M := by positivity
  set m : ℝ := max 1 ((k + 1) / a)
  refine ⟨max ((K + 1) ^ n * exp (M * Real.log M - M)) (m ^ k * (K + 1) ^ n), fun s => ?_⟩
  rcases le_total 0 s with hs | hs
  · -- `s ≥ 0`: everything is bounded by `(K + 1)^n e^(M s - e^s)`.
    refine le_trans ?_ (le_max_left _ _)
    have h1 : 1 + |s| ≤ exp s := by rw [abs_of_nonneg hs]; linarith [add_one_le_exp s]
    have h2 : K + exp s ≤ (K + 1) * exp s := by nlinarith [one_le_exp hs]
    have h3 : M * s - exp s ≤ M * Real.log M - M := by
      have := add_one_le_exp (s - Real.log M)
      rw [exp_sub, exp_log hM] at this
      have h4 : M * (s - Real.log M + 1) ≤ exp s := by
        rw [le_div_iff₀ hM] at this; linarith
      linarith
    calc (1 + |s|) ^ k * (K + exp s) ^ n * exp (a * s - exp s)
        ≤ exp s ^ k * ((K + 1) * exp s) ^ n * exp (a * s - exp s) := by
          gcongr
      _ = (K + 1) ^ n * exp (M * s - exp s) := by
          rw [mul_pow, ← exp_nat_mul, ← exp_nat_mul]
          simp only [M]
          rw [show (K + 1) ^ n * exp ((k + n + a) * s - exp s) =
            (K + 1) ^ n * (exp (k * s) * exp (n * s) * exp (a * s - exp s)) by
              rw [← exp_add, ← exp_add]; ring_nf]
          ring
      _ ≤ (K + 1) ^ n * exp (M * Real.log M - M) := by gcongr
  · -- `s ≤ 0`: the factor `(1 + |s|)^k e^(a s)` is bounded.
    refine le_trans ?_ (le_max_right _ _)
    set t := -s
    have ht : 0 ≤ t := by simp [t, hs]
    have h1 : 1 + |s| ≤ m * exp (a * t / (k + 1)) := by
      rw [abs_of_nonpos hs]
      have := add_one_le_exp (a * t / (k + 1))
      have hk1 : (0 : ℝ) < k + 1 := by positivity
      calc 1 + -s = 1 + t := rfl
        _ ≤ m * (a * t / (k + 1) + 1) := by
          have hm1 : 1 ≤ m := le_max_left _ _
          have hm2 : (k + 1) / a ≤ m := le_max_right _ _
          have : t ≤ m * (a * t / (k + 1)) := by
            rw [div_le_iff₀ ha] at hm2
            rw [mul_div_assoc', le_div_iff₀ hk1]
            nlinarith
          nlinarith
        _ ≤ m * exp (a * t / (k + 1)) := by gcongr
    have h2 : K + exp s ≤ K + 1 := by linarith [exp_le_one_iff.mpr hs]
    have h3 : exp (a * s - exp s) ≤ exp (a * s) := by
      gcongr; linarith [exp_pos s]
    have hk : (k : ℝ) * (a * t / (k + 1)) ≤ a * t := by
      have hk1 : (0 : ℝ) < k + 1 := by positivity
      rw [mul_div_assoc', div_le_iff₀ hk1]
      nlinarith [mul_nonneg ha.le ht]
    calc (1 + |s|) ^ k * (K + exp s) ^ n * exp (a * s - exp s)
        ≤ (m * exp (a * t / (k + 1))) ^ k * (K + 1) ^ n * exp (a * s) := by
          gcongr
      _ = m ^ k * (K + 1) ^ n * (exp (k * (a * t / (k + 1))) * exp (a * s)) := by
          rw [mul_pow, ← exp_nat_mul]; ring
      _ ≤ m ^ k * (K + 1) ^ n * (exp (a * t) * exp (a * s)) := by gcongr
      _ = m ^ k * (K + 1) ^ n := by
          rw [← exp_add, show a * t + a * s = 0 by simp [t], exp_zero, mul_one]

/-- The derivatives of positive order of `s ↦ c s - e^s` are bounded by `|c| + e^s`. -/
theorem norm_iteratedDeriv_linear_sub_exp_le (c : ℝ) {i : ℕ} (hi : 1 ≤ i) (s : ℝ) :
    ‖iteratedDeriv i (fun s => c * s - exp s) s‖ ≤ |c| + exp s := by
  have hd : deriv (fun s => c * s - exp s) = fun s => c - exp s := by
    funext s
    rw [deriv_fun_sub (by fun_prop) (by fun_prop)]
    simp
  have hdd : ∀ j : ℕ, iteratedDeriv (j + 2) (fun s => c * s - exp s) = fun s => -exp s := by
    intro j
    induction j with
    | zero =>
      rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
      funext s
      rw [deriv_fun_sub (by fun_prop) (by fun_prop), deriv_const, Real.deriv_exp, zero_sub]
    | succ j ih =>
      rw [show j + 1 + 2 = (j + 2) + 1 by ring, iteratedDeriv_succ, ih]
      funext s
      rw [deriv.fun_neg, Real.deriv_exp]
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rcases j with _ | j
  · rw [iteratedDeriv_one, hd, Real.norm_eq_abs]
    calc |c - exp s| ≤ |c| + |exp s| := abs_sub _ _
      _ = |c| + exp s := by rw [abs_of_pos (exp_pos s)]
  · rw [show j + 1 + 1 = j + 2 by ring, hdd, Real.norm_eq_abs, abs_neg,
      abs_of_pos (exp_pos s)]
    linarith [abs_nonneg c]

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- `1 + ∑ i, a i ≤ ∏ i, (1 + a i)` for nonnegative `a`. -/
theorem one_add_sum_le_prod_one_add {s : Finset ι} {a : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have hs := ih fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hj0 := ha j (Finset.mem_insert_self j s)
    have hsum : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i hi =>
      ha i (Finset.mem_insert_of_mem hi)
    nlinarith

/-- The Euclidean norm is at most the sum of the absolute values of the coordinates. -/
theorem EuclideanSpace.norm_le_sum_abs (y : EuclideanSpace ℝ ι) : ‖y‖ ≤ ∑ i, |y i| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  simp_rw [Real.norm_eq_abs, sq_abs]
  calc ∑ i, y i ^ 2 = ∑ i, |y i| ^ 2 := by simp_rw [sq_abs]
    _ ≤ (∑ i, |y i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

/-- The exponent `P y = ∑ i, (c i * y i - exp (y i))`. -/
def expExpExponent (c : ι → ℝ) (y : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, (c i * y i - exp (y i))

/-- The exponent is smooth. -/
theorem contDiff_expExpExponent (c : ι → ℝ) : ContDiff ℝ ∞ (expExpExponent c) := by
  unfold expExpExponent
  refine ContDiff.sum fun i _ => ?_
  have hp : ContDiff ℝ ∞ fun y : EuclideanSpace ℝ ι => y i :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).contDiff
  exact (contDiff_const.mul hp).sub (Real.contDiff_exp.comp hp)

/-- Derivatives of positive order of the exponent are bounded by `∑ i, (|c i| + exp (y i))`. -/
theorem norm_iteratedFDeriv_expExpExponent_le (c : ι → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (y : EuclideanSpace ℝ ι) :
    ‖iteratedFDeriv ℝ n (expExpExponent c) y‖ ≤ ∑ i, (|c i| + exp (y i)) := by
  set pr : ι → EuclideanSpace ℝ ι →L[ℝ] ℝ := fun i => PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i
  have hpr : ∀ i, ‖pr i‖ ≤ 1 := fun i =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
      rw [one_mul]
      exact PiLp.norm_apply_le y i
  have hp : ∀ i, ContDiff ℝ ∞ (fun s : ℝ => c i * s - exp s) := fun i => by fun_prop
  have hexp : expExpExponent c = fun y => ∑ i, ((fun s => c i * s - exp s) ∘ pr i) y := by
    funext y; rfl
  rw [hexp, iteratedFDeriv_sum (fun i _ => ((hp i).comp (pr i).contDiff).of_le
    (by exact_mod_cast le_top)), Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (pr i) (hp i) y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  calc ‖iteratedDeriv n (fun s => c i * s - exp s) (pr i y)‖ * ‖pr i‖ ^ n
      ≤ (|c i| + exp (pr i y)) * 1 := by
        gcongr
        · exact norm_iteratedDeriv_linear_sub_exp_le (c i) hn _
        · exact pow_le_one₀ (norm_nonneg _) (hpr i)
    _ = |c i| + exp (y i) := by simp [pr]

/-- The double-exponential Schwartz function `y ↦ exp (∑ i, (c i * y i - exp (y i)))`. -/
def expExpSchwartz (c : ι → ℝ) (hc : ∀ i, 0 < c i) : SchwartzMap (EuclideanSpace ℝ ι) ℂ where
  toFun y := ((exp (expExpExponent c y) : ℝ) : ℂ)
  smooth' := Complex.ofRealLI.contDiff.comp (Real.contDiff_exp.comp (contDiff_expExpExponent c))
  decay' := by
    intro k n
    -- One-variable constants.
    choose C hC using fun i => pow_mul_exp_exp_le (hc i) (by positivity : 0 ≤ 1 + |c i|) k n
    have hC0 : ∀ i, 0 ≤ C i := fun i => le_trans (by positivity) (hC i 0)
    refine ⟨n ! * ∏ i, C i, fun y => ?_⟩
    set D : ℝ := 1 + ∑ i, (|c i| + exp (y i))
    have hD1 : 1 ≤ D := by
      have : 0 ≤ ∑ i, (|c i| + exp (y i)) :=
        Finset.sum_nonneg fun i _ => by positivity
      linarith
    -- Faà di Bruno.
    have hFdB : ‖iteratedFDeriv ℝ n (fun y => ((exp (expExpExponent c y) : ℝ) : ℂ)) y‖ ≤
        n ! * exp (expExpExponent c y) * D ^ n := by
      have hcomp : (fun y => ((exp (expExpExponent c y) : ℝ) : ℂ)) =
          (Complex.ofRealLI ∘ exp) ∘ expExpExponent c := rfl
      rw [hcomp]
      refine norm_iteratedFDeriv_comp_le
        (Complex.ofRealLI.contDiff.comp Real.contDiff_exp) (contDiff_expExpExponent c)
        (by exact_mod_cast le_top) y (fun i _ => ?_) (fun i hi _ => ?_)
      · change ‖iteratedFDeriv ℝ i (⇑Complex.ofRealLI ∘ Real.exp) _‖ ≤ _
        rw [LinearIsometry.norm_iteratedFDeriv_comp_left _ Real.contDiff_exp.contDiffAt
            (by exact_mod_cast le_top), norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        have := congrFun (iteratedDeriv_exp_const_mul i 1) (expExpExponent c y)
        simp only [one_mul, one_pow] at this
        rw [this, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      · refine (norm_iteratedFDeriv_expExpExponent_le c hi y).trans ?_
        calc ∑ i, (|c i| + exp (y i)) ≤ D := by simp [D]
          _ = D ^ 1 := (pow_one D).symm
          _ ≤ D ^ i := pow_le_pow_right₀ hD1 hi
    -- Factorization of the weight.
    have hy : ‖y‖ ≤ ∏ i, (1 + |y i|) := by
      refine (EuclideanSpace.norm_le_sum_abs y).trans ?_
      have := one_add_sum_le_prod_one_add (s := Finset.univ) (a := fun i => |y i|)
        fun i _ => abs_nonneg _
      linarith
    have hDp : D ≤ ∏ i, (1 + |c i| + exp (y i)) := by
      have := one_add_sum_le_prod_one_add (s := Finset.univ)
        (a := fun i => |c i| + exp (y i)) fun i _ => by positivity
      simpa [D, add_assoc] using this
    have hexp : exp (expExpExponent c y) = ∏ i, exp (c i * y i - exp (y i)) := by
      rw [expExpExponent, exp_sum]
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => ((exp (expExpExponent c y) : ℝ) : ℂ)) y‖
        ≤ (∏ i, (1 + |y i|)) ^ k * (n ! * exp (expExpExponent c y) * D ^ n) := by
          gcongr
      _ ≤ (∏ i, (1 + |y i|)) ^ k * (n ! * exp (expExpExponent c y) *
            (∏ i, (1 + |c i| + exp (y i))) ^ n) := by
          gcongr
      _ = n ! * ∏ i, ((1 + |y i|) ^ k * (1 + |c i| + exp (y i)) ^ n *
            exp (c i * y i - exp (y i))) := by
          rw [hexp, ← Finset.prod_pow, ← Finset.prod_pow, Finset.prod_mul_distrib,
            Finset.prod_mul_distrib]
          ring
      _ ≤ n ! * ∏ i, C i := by
          gcongr with i
          exact hC i (y i)

/-- The values of `expExpSchwartz`. -/
@[simp] theorem expExpSchwartz_apply (c : ι → ℝ) (hc : ∀ i, 0 < c i) (y : EuclideanSpace ℝ ι) :
    expExpSchwartz c hc y = ((exp (∑ i, (c i * y i - exp (y i))) : ℝ) : ℂ) := rfl
