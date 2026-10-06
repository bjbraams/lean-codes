/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.Binomial
public import Carlson.RPolynomial.Differential
public import Carlson.RPolynomial.Generating
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The binomial theorem for Pochhammer numerators

Theorem 6.4-1 in a form without exceptional parameters:
`Nₙ(b, z + λ) = ∑ₘ (n choose m) λ^(n-m) (c + m)_(n-m) Nₘ(b, z)`, `c = ∑ b`. It is obtained from the
regularized binomial theorem on `re c > 0` and extended by the identity theorem in `b`.

## Main results

* `Carlson.carlsonRPolynomialNumerator_add_const`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.4.
-/

open Dirichlet
open Complex Finset
@[expose] public noncomputable section
namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- With no nodes, the Pochhammer numerator is `1` in degree zero and `0` otherwise. -/
theorem carlsonRPolynomialNumerator_of_isEmpty [IsEmpty ι] (n : ℕ) (b z : ι → ℂ) :
    carlsonRPolynomialNumerator n b z = if n = 0 then 1 else 0 := by
  classical
  rw [carlsonRPolynomialNumerator_eq_sum_piAntidiag, univ_eq_empty,
    carlsonGeneratingCoeff_empty]

/-- **Theorem 6.4-1 in division-free form**, valid for all parameters:
`Nₙ(b, z + λ) = ∑ₘ (n choose m) λ^(n-m) (c + m)_(n-m) Nₘ(b, z)` with `c = ∑ b`. -/
theorem carlsonRPolynomialNumerator_add_const (n : ℕ) (a : ℂ) (b z : ι → ℂ) :
    carlsonRPolynomialNumerator n b (fun i => z i + a) =
      ∑ m ∈ range (n + 1), (n.choose m : ℂ) * a ^ (n - m) *
        (ascPochhammer ℂ (n - m)).eval ((∑ i, b i) + m) * carlsonRPolynomialNumerator m b z := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [carlsonRPolynomialNumerator_of_isEmpty, univ_eq_empty, sum_empty, zero_add]
    rw [sum_eq_single 0 (fun m _ hm => by simp [hm]) (by simp)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [hn.ne']
  -- First on the half-space `re (∑ b) > 0`, from the regularized binomial theorem.
  have hpos : ∀ b : ι → ℂ, 0 < (∑ i, b i).re →
      carlsonRPolynomialNumerator n b (fun i => z i + a) =
        ∑ m ∈ range (n + 1), (n.choose m : ℂ) * a ^ (n - m) *
          (ascPochhammer ℂ (n - m)).eval ((∑ i, b i) + m) *
            carlsonRPolynomialNumerator m b z := by
    intro b hb
    set c := ∑ i, b i
    have hG : ∀ m : ℕ, Gamma (c + m) ≠ 0 := fun m =>
      Gamma_ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have h := regCarlsonRPolynomial_add_const n a z b
    simp only [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma] at h
    have h' := congrArg (· * Gamma (c + n)) h
    simp only [sum_mul] at h'
    rw [inv_mul_cancel_right₀ (hG n)] at h'
    rw [h']
    refine sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
    have hP := Gamma_add_nat_div_Gamma_eq (n := n - m) (c + m) fun k h => by
      have := congrArg re h
      simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [show c + (m : ℂ) + ((n - m : ℕ) : ℂ) = c + n by push_cast [hmn]; ring] at hP
    rw [← hP]
    simp only [show ∑ i, b i = c from rfl]
    field_simp [hG m]
  -- Both sides are entire in the parameters; extend by the identity theorem.
  have hL : AnalyticOnNhd ℂ (fun b : ι → ℂ =>
      carlsonRPolynomialNumerator n b (fun i => z i + a)) Set.univ := by
    intro b _
    have hpair : AnalyticAt ℂ (fun b : ι → ℂ => (b, fun i => z i + a)) b :=
      analyticAt_id.prod analyticAt_const
    have hj := analyticOnNhd_carlsonRPolynomialNumerator_joint (ι := ι) n
      (b, fun i => z i + a) (Set.mem_univ _)
    exact AnalyticAt.comp_of_eq (g := fun p : (ι → ℂ) × (ι → ℂ) =>
      carlsonRPolynomialNumerator n p.1 p.2) (f := fun b : ι → ℂ => (b, fun i => z i + a))
      hj hpair rfl
  have hR : AnalyticOnNhd ℂ (fun b : ι → ℂ => ∑ m ∈ range (n + 1), (n.choose m : ℂ) *
      a ^ (n - m) * (ascPochhammer ℂ (n - m)).eval ((∑ i, b i) + m) *
        carlsonRPolynomialNumerator m b z) Set.univ := by
    intro b _
    refine Finset.analyticAt_fun_sum _ fun m _ => ?_
    have hsum : AnalyticAt ℂ (fun b : ι → ℂ => (∑ i, b i) + (m : ℂ)) b :=
      (Finset.analyticAt_fun_sum _ fun i _ =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt b).add
        analyticAt_const
    have hpoly : AnalyticAt ℂ (fun s : ℂ => (ascPochhammer ℂ (n - m)).eval s)
        ((∑ i, b i) + m) := (Polynomial.differentiable _).analyticAt _
    have hpair : AnalyticAt ℂ (fun b : ι → ℂ => (b, z)) b := analyticAt_id.prod analyticAt_const
    exact (analyticAt_const.mul (AnalyticAt.comp_of_eq (g := fun s : ℂ =>
      (ascPochhammer ℂ (n - m)).eval s) hpoly hsum rfl)).mul
      (AnalyticAt.comp_of_eq (g := fun p : (ι → ℂ) × (ι → ℂ) =>
        carlsonRPolynomialNumerator m p.1 p.2) (f := fun b : ι → ℂ => (b, z))
        (analyticOnNhd_carlsonRPolynomialNumerator_joint m (b, z) (Set.mem_univ _)) hpair rfl)
  have hev : (fun b : ι → ℂ => carlsonRPolynomialNumerator n b (fun i => z i + a)) =ᶠ[nhds
      (fun _ => 1)] fun b => ∑ m ∈ range (n + 1), (n.choose m : ℂ) * a ^ (n - m) *
        (ascPochhammer ℂ (n - m)).eval ((∑ i, b i) + m) * carlsonRPolynomialNumerator m b z := by
    have hopen : IsOpen {b : ι → ℂ | 0 < (∑ i, b i).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_finsetSum _ fun i _ => continuous_apply i))
    have hmem : (fun _ => (1 : ℂ)) ∈ {b : ι → ℂ | 0 < (∑ i, b i).re} := by
      simp [Fintype.card_pos]
    filter_upwards [hopen.mem_nhds hmem] with b hb using hpos b hb
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR isPreconnected_univ (Set.mem_univ _) hev
    (Set.mem_univ b)

end Carlson
