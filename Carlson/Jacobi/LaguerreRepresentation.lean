/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Laguerre
public import ToMathlib.Analysis.SpecialFunctions.Pow

/-!
# Weighted representation of Laguerre coefficients

Carlson's Theorem 7.9-3: for `re β > -1` and a function `f` whose derivatives up to order
`n` grow at most like `e^{εx}` with `ε < 1` on the positive axis,
`∫₀^∞ f p̃ₙ x^β e^{-x} dx = ∫₀^∞ f⁽ⁿ⁾ x^(β+n) e^{-x} dx`.
The proof integrates by parts `n` times using Rodrigues' formula (7.9-8); the boundary
terms vanish at both ends.

## Main results

* `laguerreGammaDeriv`: the derivatives of `x^A e^{-x}` on the positive axis, with the
  Leibniz form `laguerreGammaDeriv_eq` and the bound `exists_norm_laguerreGammaDeriv_le`.
* `integral_mul_monicLaguerre_mul_cpow_mul_exp`: Theorem 7.9-3.

## Implementation notes

Carlson writes the theorem with the normalized Euler measures `dλ_{1+β}`; after clearing the
factors `Γ(1+β)` and `Γ(1+β+n)` it is the identity above. Carlson assumes that `f` is
holomorphic near the positive axis and that `f⁽ᵐ⁾(x) e^{-εx} → 0` for `m ≤ n - 1`. Here
`f : ℝ → ℂ` only needs `n - 1` differentiable derivatives on the open positive axis, and the
growth bound is assumed on the whole open axis (so also near `0`) and for `f⁽ⁿ⁾` as well.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.9.
-/

@[expose] public noncomputable section

open Complex Set Filter Polynomial Finset MeasureTheory
open scoped Topology

namespace Carlson.TwoVariable

/-- The Laguerre weight `x^A e^{-x}` as a complex function. -/
def laguerreGamma (A : ℂ) (w : ℂ) : ℂ := w ^ A * cexp (-w)

/-- The `j`-th derivative of `x^A e^{-x}` along the positive real axis. -/
def laguerreGammaDeriv (A : ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  iteratedDeriv j (laguerreGamma A) (x : ℂ)

/-- On the positive real axis, the derivatives of `x^A e^{-x}` differentiate into each other. -/
theorem hasDerivAt_laguerreGammaDeriv (A : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (laguerreGammaDeriv A j) (laguerreGammaDeriv A (j + 1) x) x := by
  have hs : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hg : AnalyticAt ℂ (laguerreGamma A) (x : ℂ) :=
    (analyticAt_id.cpow analyticAt_const hs).mul analyticAt_id.neg.cexp
  have hd := ((hg.iterated_deriv j).differentiableAt).hasDerivAt
  rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_succ] at hd
  exact hd.comp_ofReal

/-- Leibniz form of the derivatives of `x^A e^{-x}` on the positive real axis. -/
theorem laguerreGammaDeriv_eq (A : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerreGammaDeriv A j x = ∑ i ∈ range (j + 1), (j.choose i : ℂ) *
      ((descPochhammer ℂ i).eval A * (x : ℂ) ^ (A - i)) * ((-1) ^ (j - i) * cexp (-(x : ℂ))) := by
  have hs : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have h1 : ContDiffAt ℂ j (fun w : ℂ => w ^ A) (x : ℂ) :=
    (analyticAt_id.cpow analyticAt_const hs).contDiffAt
  have h2 : ContDiffAt ℂ j (fun w : ℂ => cexp (-w)) (x : ℂ) :=
    (analyticAt_id.neg.cexp).contDiffAt
  change iteratedDeriv j (fun w : ℂ => w ^ A * cexp (-w)) (x : ℂ) = _
  rw [iteratedDeriv_fun_mul h1 h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd := iteratedDeriv_sub_cpow 0 A i (x := (x : ℂ)) (by simpa using hs)
  simp only [sub_zero] at hd
  have he := iteratedDeriv_cexp_const_mul (j - i) (-1 : ℂ)
  simp only [neg_one_mul] at he
  rw [hd, he]

/-- Growth bound for the derivatives of `x^A e^{-x}`, uniform on the positive axis. -/
theorem exists_norm_laguerreGammaDeriv_le (A : ℂ) (j : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → ‖laguerreGammaDeriv A j x‖ ≤
      K * ((x ^ (A.re - j) + x ^ A.re) * Real.exp (-x)) := by
  refine ⟨∑ i ∈ range (j + 1), (j.choose i : ℝ) * ‖(descPochhammer ℂ i).eval A‖,
    sum_nonneg fun i _ => by positivity, fun x hx => ?_⟩
  rw [laguerreGammaDeriv_eq A j hx, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
  have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hp : x ^ (A - i).re ≤ x ^ (A.re - j) + x ^ A.re := by
    refine Real.rpow_le_rpow_add_rpow hx ?_ ?_
    · simp only [sub_re, natCast_re]; linarith [(Nat.cast_le (α := ℝ)).mpr hij]
    · simp only [sub_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) i]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_cpow_eq_rpow_re_of_pos hx, show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring,
    norm_exp_ofReal, Complex.norm_natCast]
  have := mul_le_mul_of_nonneg_left hp (by positivity :
    (0 : ℝ) ≤ j.choose i * ‖(descPochhammer ℂ i).eval A‖)
  have he := Real.exp_pos (-x)
  nlinarith


/-- Pointwise bound for a function of exponential growth times a derivative of the weight. -/
theorem norm_mul_laguerreGammaDeriv_le {g : ℝ → ℂ} {ε C K : ℝ} {A : ℂ} {j : ℕ}
    (hK : ∀ x : ℝ, 0 < x → ‖laguerreGammaDeriv A j x‖ ≤
      K * ((x ^ (A.re - j) + x ^ A.re) * Real.exp (-x)))
    (hC : ∀ x : ℝ, 0 < x → ‖g x‖ ≤ C * Real.exp (ε * x)) {x : ℝ} (hx : 0 < x) :
    ‖g x * laguerreGammaDeriv A j x‖ ≤
      C * K * ((x ^ (A.re - j) + x ^ A.re) * Real.exp (-(1 - ε) * x)) := by
  rw [norm_mul]
  have hC0 : 0 ≤ C * Real.exp (ε * x) := (norm_nonneg _).trans (hC x hx)
  calc ‖g x‖ * ‖laguerreGammaDeriv A j x‖
      ≤ C * Real.exp (ε * x) * (K * ((x ^ (A.re - j) + x ^ A.re) * Real.exp (-x))) :=
        mul_le_mul (hC x hx) (hK x hx) (norm_nonneg _) hC0
    _ = C * K * ((x ^ (A.re - j) + x ^ A.re) * Real.exp (-(1 - ε) * x)) := by
        rw [show -(1 - ε) * x = ε * x + -x by ring, Real.exp_add]; ring

/-- A function of exponential growth `e^{εx}`, `ε < 1`, is integrable on the positive axis
against the `j`-th derivative of `x^A e^{-x}` when `re A - j > -1`. -/
theorem integrableOn_mul_laguerreGammaDeriv {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0))) {ε C : ℝ} (hε : ε < 1)
    (hC : ∀ x : ℝ, 0 < x → ‖g x‖ ≤ C * Real.exp (ε * x)) (A : ℂ) (j : ℕ)
    (hA : -1 < A.re - j) :
    IntegrableOn (fun x => g x * laguerreGammaDeriv A j x) (Ioi 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_laguerreGammaDeriv_le A j
  have hb : 0 < 1 - ε := by linarith
  have hI₁ := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hA one_pos hb
  have hI₂ := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A.re)
    (by linarith [Nat.cast_nonneg (α := ℝ) j]) one_pos hb
  simp only [Real.rpow_one] at hI₁ hI₂
  have hI : IntegrableOn (fun x : ℝ =>
      C * K * ((x ^ (A.re - j) + x ^ A.re) * Real.exp (-(1 - ε) * x))) (Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.const_mul (hI₁.add hI₂) (C * K))
      (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  have hc : ContinuousOn (laguerreGammaDeriv A j) (Ioi 0) := fun x hx =>
    (hasDerivAt_laguerreGammaDeriv A j hx).continuousAt.continuousWithinAt
  refine hI.mono' (hg.mul (hc.aestronglyMeasurable measurableSet_Ioi)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  exact norm_mul_laguerreGammaDeriv_le hK hC hx

/-- The boundary terms vanish at both ends of the positive axis when `re A - j > 0`. -/
theorem tendsto_mul_laguerreGammaDeriv {g : ℝ → ℂ} {ε C : ℝ} (hε : ε < 1)
    (hC : ∀ x : ℝ, 0 < x → ‖g x‖ ≤ C * Real.exp (ε * x)) (A : ℂ) (j : ℕ)
    (hA : 0 < A.re - j) :
    Tendsto (g * laguerreGammaDeriv A j) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (g * laguerreGammaDeriv A j) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_laguerreGammaDeriv_le A j
  have hb : 0 < 1 - ε := by linarith
  have hA' : 0 < A.re := by linarith [Nat.cast_nonneg (α := ℝ) j]
  set F : ℝ → ℝ := fun x => C * K * ((x ^ (A.re - j) + x ^ A.re) * Real.exp (-(1 - ε) * x))
  have hF : ∀ x : ℝ, 0 < x → ‖(g * laguerreGammaDeriv A j) x‖ ≤ F x := fun x hx =>
    norm_mul_laguerreGammaDeriv_le hK hC hx
  constructor
  · refine squeeze_zero_norm' ((eventually_mem_nhdsWithin).mono fun x hx => hF x hx) ?_
    have h0 : Tendsto F (𝓝 0) (𝓝 (F 0)) := by
      refine (tendsto_const_nhds.mul (((Real.continuousAt_rpow_const 0 _ (Or.inr hA.le)).add
        (Real.continuousAt_rpow_const 0 _ (Or.inr hA'.le))).mul
        (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul continuousAt_id))))
    have hF0 : F 0 = 0 := by
      simp only [F, Real.zero_rpow hA.ne', Real.zero_rpow hA'.ne']; ring
    rw [hF0] at h0
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  · refine squeeze_zero_norm' ((eventually_gt_atTop 0).mono fun x hx => hF x hx) ?_
    have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A.re - j) _ hb).add
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A.re _ hb)).const_mul (C * K)
    simp only [add_zero, mul_zero] at h
    refine h.congr fun x => ?_
    simp only [F]; ring

/-- **Theorem 7.9-3** (with unnormalized Euler measures): for `re β > -1` and a function `f`
whose derivatives up to order `n` grow at most like `e^{εx}` with `ε < 1` on the positive
axis, `∫₀^∞ f p̃ₙ x^β e^{-x} dx = ∫₀^∞ f⁽ⁿ⁾ x^(β+n) e^{-x} dx`. -/
theorem integral_mul_monicLaguerre_mul_cpow_mul_exp {f : ℝ → ℂ} {n : ℕ} {β : ℂ}
    (hβ : -1 < β.re)
    (hf : ∀ m < n, ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (iteratedDeriv m f) x) {ε C : ℝ}
    (hε : ε < 1) (hC : ∀ m ≤ n, ∀ x : ℝ, 0 < x → ‖iteratedDeriv m f x‖ ≤ C * Real.exp (ε * x)) :
    ∫ x in Ioi (0 : ℝ), f x * (monicLaguerre β n).eval (x : ℂ) * ((x : ℂ) ^ β * cexp (-(x : ℂ))) =
      ∫ x in Ioi (0 : ℝ), iteratedDeriv n f x * ((x : ℂ) ^ (β + n) * cexp (-(x : ℂ))) := by
  set A : ℂ := β + n with hAdef
  have hAre : A.re = β.re + n := by simp [A]
  have hmeas : ∀ m ≤ n, 0 < n →
      AEStronglyMeasurable (iteratedDeriv m f) (volume.restrict (Ioi 0)) := by
    intro m hm hn
    rcases hm.lt_or_eq with hm | rfl
    · exact (ContinuousOn.aestronglyMeasurable (fun x hx =>
        (hf m hm x hx).continuousAt.continuousWithinAt) measurableSet_Ioi)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
      rw [zero_add, iteratedDeriv_succ]
      exact (measurable_deriv _).aestronglyMeasurable
  have key : ∀ k ≤ n, ∫ x in Ioi (0 : ℝ), f x * laguerreGammaDeriv A n x =
      (-1 : ℂ) ^ k * ∫ x in Ioi (0 : ℝ), iteratedDeriv k f x * laguerreGammaDeriv A (n - k) x := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hkn : k < n := by omega
      have hsplit : n - k = n - (k + 1) + 1 := by omega
      have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
      have hcast : ((n - (k + 1) : ℕ) : ℝ) = n - k - 1 := by
        rw [Nat.cast_sub hkn]; push_cast; ring
      have hcast' : ((n - (k + 1) + 1 : ℕ) : ℝ) = n - k := by
        rw [Nat.cast_add, hcast]; push_cast; ring
      rw [ih (by omega), hsplit]
      have hlim := tendsto_mul_laguerreGammaDeriv hε (hC k hkn.le) A (n - (k + 1))
        (by rw [hcast, hAre]; linarith)
      have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
        (u := iteratedDeriv k f) (u' := iteratedDeriv (k + 1) f)
        (v := laguerreGammaDeriv A (n - (k + 1)))
        (v' := laguerreGammaDeriv A (n - (k + 1) + 1))
        (fun x hx => by
          rw [iteratedDeriv_succ]
          exact (hf k hkn x hx).hasDerivAt)
        (fun x hx => hasDerivAt_laguerreGammaDeriv A _ hx)
        (integrableOn_mul_laguerreGammaDeriv (hmeas k hkn.le (by omega)) hε (hC k hkn.le) A _
          (by rw [hcast', hAre]; linarith [Nat.cast_nonneg (α := ℝ) k]))
        (integrableOn_mul_laguerreGammaDeriv (hmeas (k + 1) hk (by omega)) hε (hC (k + 1) hk)
          A _ (by rw [hcast, hAre]; linarith [Nat.cast_nonneg (α := ℝ) k]))
        hlim.1 hlim.2
      rw [hibp, pow_succ]
      ring
  have h := key n le_rfl
  rw [Nat.sub_self] at h
  have hn : ∀ x ∈ Ioi (0 : ℝ), f x * laguerreGammaDeriv A n x = (-1 : ℂ) ^ n *
      (f x * (monicLaguerre β n).eval (x : ℂ) * ((x : ℂ) ^ β * cexp (-(x : ℂ)))) := by
    intro x hx
    rw [laguerreGammaDeriv, show laguerreGamma A = fun w => w ^ (β + n) * cexp (-w) from rfl,
      iteratedDeriv_cpow_mul_exp_neg β n (ofReal_mem_slitPlane.mpr hx)]
    ring
  have h0 : ∀ x ∈ Ioi (0 : ℝ), iteratedDeriv n f x * laguerreGammaDeriv A 0 x =
      iteratedDeriv n f x * ((x : ℂ) ^ (β + n) * cexp (-(x : ℂ))) := fun x _ => rfl
  rw [setIntegral_congr_fun measurableSet_Ioi hn, setIntegral_congr_fun measurableSet_Ioi h0,
    integral_const_mul] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h

end Carlson.TwoVariable
