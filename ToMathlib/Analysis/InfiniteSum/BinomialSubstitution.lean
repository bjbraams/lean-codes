/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.InfiniteSum.FiniteFibers
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Absolute reassembly after a coupled binomial substitution

The substitution `X=x(1-y), Y=y(1-x)` expands a double series into four
indices. An absolute binomial majorant justifies collecting the resulting
coefficients by the powers of `x` and `y`. No parameter-specific facts are
needed for this summation step.
-/

open Finset
public noncomputable section

/-- A finite binomial expansion, viewed as an infinite series with zero tail. -/
theorem Nat.hasSum_choose_mul_pow {R : Type*} [CommSemiring R] [TopologicalSpace R]
    (u : R) (m : ℕ) :
    HasSum (fun k : ℕ => (m.choose k : R) * u ^ k) ((1 + u) ^ m) := by
  have h : HasSum (fun k : ℕ => (m.choose k : R) * u ^ k)
      (∑ k ∈ range (m + 1), (m.choose k : R) * u ^ k) :=
    hasSum_sum_of_ne_finset_zero (s := range (m + 1))
    (f := fun k : ℕ => (m.choose k : R) * u ^ k) (fun k hk => by
      rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]
      simp)
  convert h using 1
  simpa only [one_pow, mul_one, mul_comm, add_comm] using (add_pow u 1 m)

/-- The binomially weighted double geometric series converges on the positive diamond. -/
theorem summable_choose_mul_pow {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXY : X + Y < 1) :
    Summable (fun p : ℕ × ℕ => ((p.1 + p.2).choose p.1 : ℝ) * X ^ p.1 * Y ^ p.2) := by
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
  change Summable (fun v : Σ N : ℕ, ↥(antidiagonal N) =>
    ((v.2.val.1 + v.2.val.2).choose v.2.val.1 : ℝ) * X ^ v.2.val.1 * Y ^ v.2.val.2)
  apply (summable_sigma_of_nonneg (fun v => by positivity)).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  change Summable (fun N : ℕ => ∑' p : ↥(antidiagonal N),
    ((p.val.1 + p.val.2).choose p.val.1 : ℝ) * X ^ p.val.1 * Y ^ p.val.2)
  have he (N : ℕ) : (∑' p : ↥(antidiagonal N),
      ((p.val.1 + p.val.2).choose p.val.1 : ℝ) * X ^ p.val.1 * Y ^ p.val.2) =
        (X + Y) ^ N := by
    rw [tsum_fintype, Finset.sum_coe_sort (antidiagonal N) (fun p : ℕ × ℕ =>
      ((p.1 + p.2).choose p.1 : ℝ) * X ^ p.1 * Y ^ p.2)]
    trans ∑ p ∈ antidiagonal N, (N.choose p.1 : ℝ) * X ^ p.1 * Y ^ p.2
    · apply Finset.sum_congr rfl
      intro p hp
      rw [mem_antidiagonal.mp hp]
    · simpa only [nsmul_eq_mul, mul_assoc] using ((Commute.all X Y).add_pow' N).symm
  simpa only [he] using summable_geometric_of_lt_one (add_nonneg hX hY) hXY

/-- A second binomial expansion preserves convergence with its exact positive majorant. -/
theorem summable_choose_choose_mul_pow {X Y Z : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hXYZ : X * (1 + Z) + Y < 1) :
    Summable (fun v : (ℕ × ℕ) × ℕ =>
      ((v.1.1 + v.1.2).choose v.1.1 : ℝ) * (v.1.1.choose v.2 : ℝ) *
        X ^ v.1.1 * Y ^ v.1.2 * Z ^ v.2) := by
  have h (p : ℕ × ℕ) : HasSum (fun k : ℕ =>
      ((p.1 + p.2).choose p.1 : ℝ) * (p.1.choose k : ℝ) * X ^ p.1 * Y ^ p.2 * Z ^ k)
      (((p.1 + p.2).choose p.1 : ℝ) * (X * (1 + Z)) ^ p.1 * Y ^ p.2) := by
    convert (Nat.hasSum_choose_mul_pow Z p.1).mul_left
      (((p.1 + p.2).choose p.1 : ℝ) * X ^ p.1 * Y ^ p.2) using 1
    · funext k; ring
    · rw [mul_pow]; ring
  apply (summable_prod_of_nonneg (fun _ => by positivity)).mpr
  refine ⟨fun p => (h p).summable, ?_⟩
  simpa only [(h _).tsum_eq] using
    summable_choose_mul_pow (mul_nonneg hX (by positivity)) hY hXYZ

namespace Complex

/-- One term of the expanded binomial substitution, indexed by source and added degrees. -/
def binomialSubstitutionTerm (f : ℕ × ℕ → ℂ) (x y : ℂ)
    (v : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  f v.1 * (v.1.2.choose v.2.1 : ℂ) * (v.1.1.choose v.2.2 : ℂ) *
    (-1 : ℂ) ^ (v.2.1 + v.2.2) * x ^ (v.1.1 + v.2.1) * y ^ (v.1.2 + v.2.2)

/-- The norm sum over added degrees is exactly the absolute binomial majorant. -/
theorem hasSum_norm_binomialSubstitutionTerm (f : ℕ × ℕ → ℂ) (x y : ℂ) (p : ℕ × ℕ) :
    HasSum (fun q : ℕ × ℕ => ‖binomialSubstitutionTerm f x y (p, q)‖)
      (‖f p‖ * (‖x‖ * (1 + ‖y‖)) ^ p.1 * (‖y‖ * (1 + ‖x‖)) ^ p.2) := by
  have hx := Nat.hasSum_choose_mul_pow ‖x‖ p.2
  have hy := Nat.hasSum_choose_mul_pow ‖y‖ p.1
  have hp := hx.mul hy (hx.summable.mul_of_nonneg hy.summable
    (fun _ => by positivity) (fun _ => by positivity))
  convert hp.mul_left (‖f p‖ * ‖x‖ ^ p.1 * ‖y‖ ^ p.2) using 1
  · funext q
    simp only [binomialSubstitutionTerm, norm_mul, norm_pow, Complex.norm_natCast,
      norm_neg, norm_one, one_pow, mul_one, pow_add]
    ring
  · simp only [mul_pow]
    ring

/-- Summing over added degrees recovers the original substituted monomial. -/
theorem hasSum_binomialSubstitutionTerm (f : ℕ × ℕ → ℂ) (x y : ℂ) (p : ℕ × ℕ) :
    HasSum (fun q : ℕ × ℕ => binomialSubstitutionTerm f x y (p, q))
      (f p * (x * (1 - y)) ^ p.1 * (y * (1 - x)) ^ p.2) := by
  have hx := Nat.hasSum_choose_mul_pow (-x) p.2
  have hy := Nat.hasSum_choose_mul_pow (-y) p.1
  have hxn : Summable (fun k : ℕ => ‖(p.2.choose k : ℂ) * (-x) ^ k‖) := by
    simpa only [norm_mul, Complex.norm_natCast, norm_pow, norm_neg] using
      (Nat.hasSum_choose_mul_pow ‖x‖ p.2).summable
  have hyn : Summable (fun k : ℕ => ‖(p.1.choose k : ℂ) * (-y) ^ k‖) := by
    simpa only [norm_mul, Complex.norm_natCast, norm_pow, norm_neg] using
      (Nat.hasSum_choose_mul_pow ‖y‖ p.1).summable
  have hp := hx.mul hy (summable_mul_of_summable_norm hxn hyn)
  convert hp.mul_left (f p * x ^ p.1 * y ^ p.2) using 1
  · funext q
    simp only [binomialSubstitutionTerm, pow_add]
    rw [neg_pow, neg_pow]
    ring
  · simp only [sub_eq_add_neg, mul_pow]
    ring

/-- An absolute binomial majorant makes all four expanded indices summable. -/
theorem summable_norm_binomialSubstitutionTerm {f : ℕ × ℕ → ℂ} {x y : ℂ}
    (hf : Summable (fun p : ℕ × ℕ =>
      ‖f p‖ * (‖x‖ * (1 + ‖y‖)) ^ p.1 * (‖y‖ * (1 + ‖x‖)) ^ p.2)) :
    Summable (fun v : (ℕ × ℕ) × (ℕ × ℕ) => ‖binomialSubstitutionTerm f x y v‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun p => (hasSum_norm_binomialSubstitutionTerm f x y p).summable,
    by simpa only [(hasSum_norm_binomialSubstitutionTerm f x y _).tsum_eq] using hf⟩

/-- Regroup the expanded series by its two output degrees. -/
private theorem hasSum_binomialSubstitution_collect (f : ℕ × ℕ → ℂ) (x y : ℂ) {z : ℂ}
    (hf : HasSum (binomialSubstitutionTerm f x y) z) :
    HasSum (fun v : ℕ × ℕ =>
      (∑ p ∈ antidiagonal v.1, ∑ q ∈ antidiagonal v.2,
        f (p.1, q.1) * (q.1.choose p.2 : ℂ) * (p.1.choose q.2 : ℂ) *
          (-1 : ℂ) ^ (p.2 + q.2)) * x ^ v.1 * y ^ v.2) z := by
  classical
  let e := Equiv.prodProdProdComm ℕ ℕ ℕ ℕ
  let s (v : ℕ × ℕ) := (antidiagonal v.1 ×ˢ antidiagonal v.2).map e.toEmbedding
  have hs : ∀ i v, i ∈ s v ↔ (i.1.1 + i.2.1, i.1.2 + i.2.2) = v := by
    intro i v
    simp only [s, Finset.mem_map, Finset.mem_product, mem_antidiagonal]
    constructor
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      exact Prod.ext h1 h2
    · intro h
      refine ⟨((i.1.1, i.2.1), (i.1.2, i.2.2)), ?_, ?_⟩
      · exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · rfl
  have h := hf.sum_finite_fibers (fun i => (i.1.1 + i.2.1, i.1.2 + i.2.2)) s hs
  convert h using 1
  funext v
  simp only [s, Finset.sum_map, Finset.sum_product]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  dsimp [binomialSubstitutionTerm, e, Equiv.prodProdProdComm]
  rw [mem_antidiagonal.mp hp, mem_antidiagonal.mp hq]

/-- Absolute convergence justifies reassembling the coupled binomial substitution. -/
theorem hasSum_binomialSubstitution {f : ℕ × ℕ → ℂ} {x y : ℂ}
    (hf : Summable (fun p : ℕ × ℕ =>
      ‖f p‖ * (‖x‖ * (1 + ‖y‖)) ^ p.1 * (‖y‖ * (1 + ‖x‖)) ^ p.2)) :
    HasSum (fun v : ℕ × ℕ =>
      (∑ p ∈ antidiagonal v.1, ∑ q ∈ antidiagonal v.2,
        f (p.1, q.1) * (q.1.choose p.2 : ℂ) * (p.1.choose q.2 : ℂ) *
          (-1 : ℂ) ^ (p.2 + q.2)) * x ^ v.1 * y ^ v.2)
      (∑' p : ℕ × ℕ, f p * (x * (1 - y)) ^ p.1 * (y * (1 - x)) ^ p.2) := by
  have h := (summable_norm_binomialSubstitutionTerm hf).of_norm
  have hv := h.hasSum.prod_fiberwise (hasSum_binomialSubstitutionTerm f x y)
  apply hasSum_binomialSubstitution_collect f x y
  simpa only [← hv.tsum_eq] using h.hasSum

end Complex
