/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.Generating
public import Carlson.RPolynomial.Growth
public import Carlson.RPolynomial.Transform
public import Dirichlet.ParameterShift
public import Dirichlet.Average.RealNodes
public import Carlson.RPolynomial.Differential
public import Carlson.RPolynomial.NumeratorBinomial
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Identities from the generating relation 6.6-1

Exercises of Chapter 6 obtained by comparing coefficients in the generating relation
`∏ (1 - t zᵢ)^(-bᵢ) = ∑ Nₙ(b; z) tⁿ/n!`, stated for the Pochhammer numerators
`Nₙ(b; z) = (c)ₙ Rₙ(b, z)` so that no parameter is excluded.

## Main results

* `Carlson.carlsonRPolynomialNumerator_eq_circleIntegral`: the contour form, Exercise 6.6-1.
* `Carlson.carlsonRPolynomialNumerator_sumElim`, `_sumElim_unit`: Exercises 6.6-6 and 6.2-2.
* `Carlson.carlsonRPolynomialNumerator_add_params`: Exercise 6.6-7.
* `Carlson.carlsonRPolynomialNumerator_sq_nodes`: Exercise 6.6-8.
* `Carlson.carlsonRPolynomialNumerator_addDirichletUnit`: Exercise 6.6-12.
* `Carlson.carlsonRPolynomialNumerator_succ_eq_sum`, `_tobey`: Tobey's relation, Exercise 6.6-13.
* `Carlson.carlsonRPolynomialNumerator_two`, `sum_mul_carlsonRPolynomialNumerator_two`:
  Exercise 6.2-13; `Carlson.sum_mul_sub_mean_sq`: the identity of Exercise 6.2-14.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.6.
-/

open Dirichlet
open Complex Finset
@[expose] public noncomputable section
namespace Carlson

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Coefficients of a Cauchy product: if two absolutely convergent power series have sums `F`
and `G` on a disk, and a third has sum `F * G` there, its coefficients are the convolutions. -/
theorem coeff_eq_sum_mul_of_hasSum {A B C : ℕ → ℂ} {F G : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hA : ∀ t : ℂ, ‖t‖ < δ → HasSum (fun n => A n * t ^ n) (F t) ∧
      Summable fun n => ‖A n * t ^ n‖)
    (hB : ∀ t : ℂ, ‖t‖ < δ → HasSum (fun n => B n * t ^ n) (G t) ∧
      Summable fun n => ‖B n * t ^ n‖)
    (hC : ∀ t : ℂ, ‖t‖ < δ → HasSum (fun n => C n * t ^ n) (F t * G t)) (n : ℕ) :
    C n = ∑ k ∈ range (n + 1), A k * B (n - k) := by
  have h := coeff_eq_of_hasSum_pow hδ hC (b := fun n => ∑ k ∈ range (n + 1), A k * B (n - k))
    (fun t ht => by
      obtain ⟨hA1, hA2⟩ := hA t ht
      obtain ⟨hB1, hB2⟩ := hB t ht
      have := hasSum_sum_range_mul_of_summable_norm hA2 hB2
      rw [hA1.tsum_eq, hB1.tsum_eq] at this
      refine this.congr_fun fun m => ?_
      rw [sum_mul]
      refine sum_congr rfl fun k hk => ?_
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
      rw [show t ^ m = t ^ k * t ^ (m - k) by rw [← pow_add, Nat.add_sub_cancel' hk']]
      ring)
  exact congrFun h n

/-- The generating series 6.6-1 with absolute convergence, for `‖t‖ < δ` whenever
`δ ‖zᵢ‖ ≤ 1`. -/
theorem hasSum_carlsonRPolynomialNumerator_of_lt {b z : ι → ℂ} {δ : ℝ}
    (hδz : ∀ i, δ * ‖z i‖ ≤ 1) {t : ℂ} (ht : ‖t‖ < δ) :
    HasSum (fun n => carlsonRPolynomialNumerator n b z / (n.factorial : ℂ) * t ^ n)
      (carlsonRGeneratingKernel b z t) ∧
    Summable fun n => ‖carlsonRPolynomialNumerator n b z / (n.factorial : ℂ) * t ^ n‖ := by
  classical
  have htz : ∀ i ∈ (univ : Finset ι), ‖t * z i‖ < 1 := fun i _ => by
    rw [norm_mul]
    rcases eq_or_ne (z i) 0 with h0 | h0
    · simp [h0]
    · calc ‖t‖ * ‖z i‖ < δ * ‖z i‖ := mul_lt_mul_of_pos_right ht (norm_pos_iff.mpr h0)
        _ ≤ 1 := hδz i
  have h := hasSum_carlsonGeneratingCoeff (univ : Finset ι) b z t htz
  simp only [← carlsonRPolynomialNumerator_eq_sum_piAntidiag] at h
  exact ⟨by simpa [carlsonRGeneratingKernel] using h.1, h.2⟩

/-- A radius `δ > 0` with `δ ‖zᵢ‖ ≤ 1` for all nodes. -/
theorem exists_radius (z : ι → ℂ) : ∃ δ > 0, ∀ i, δ * ‖z i‖ ≤ 1 := by
  refine ⟨1 / (1 + ∑ i, ‖z i‖), by positivity, fun i => ?_⟩
  rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
  have := Finset.single_le_sum (f := fun i => ‖z i‖) (fun j _ => norm_nonneg _) (mem_univ i)
  linarith

/-- The Pochhammer numerator is homogeneous of degree `n` in the nodes. -/
theorem carlsonRPolynomialNumerator_smul (n : ℕ) (b z : ι → ℂ) (c : ℂ) :
    carlsonRPolynomialNumerator n b (fun i => c * z i) =
      c ^ n * carlsonRPolynomialNumerator n b z := by
  classical
  simp only [carlsonRPolynomialNumerator_eq_multinomial_sum, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hm' : ∑ i, m i = n := (mem_piAntidiag.mp hm).1
  simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hm']
  ring

/-- `(uv)ᵇ = uᵇ vᵇ` for `u`, `v` in the right half-plane. -/
theorem mul_cpow_of_re_pos {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (b : ℂ) :
    (u * v) ^ b = u ^ b * v ^ b := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  have hau := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu))
  have hav := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv))
  have hlog : log (u * v) = log u + log v := (log_mul_eq_add_log_iff hu0 hv0).mpr
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [cpow_def_of_ne_zero (mul_ne_zero hu0 hv0), cpow_def_of_ne_zero hu0, cpow_def_of_ne_zero hv0,
    hlog, add_mul, exp_add]

/-- **Exercise 6.6-6** (juxtaposition of node sets), in numerator form:
`Nₙ(b, β; z, ζ)/n! = ∑ₘ Nₘ(b; z)/m! · N_(n-m)(β; ζ)/(n-m)!`. In Carlson's normalization this is
`(c + γ)ₙ Rₙ(b, β; z, ζ)/n! = ∑ₘ (c)ₘ (γ)_(n-m) Rₘ(b; z) R_(n-m)(β; ζ)/(m! (n-m)!)`. -/
theorem carlsonRPolynomialNumerator_sumElim (n : ℕ) (b z : ι → ℂ) (β ζ : κ → ℂ) :
    carlsonRPolynomialNumerator n (Sum.elim b β) (Sum.elim z ζ) / (n.factorial : ℂ) =
      ∑ m ∈ range (n + 1), carlsonRPolynomialNumerator m b z / (m.factorial : ℂ) *
        (carlsonRPolynomialNumerator (n - m) β ζ / ((n - m).factorial : ℂ)) := by
  obtain ⟨δ, hδ, hδz⟩ := exists_radius (Sum.elim z ζ)
  refine coeff_eq_sum_mul_of_hasSum hδ (F := carlsonRGeneratingKernel b z)
    (A := fun m => carlsonRPolynomialNumerator m b z / (m.factorial : ℂ))
    (B := fun m => carlsonRPolynomialNumerator m β ζ / (m.factorial : ℂ))
    (C := fun m => carlsonRPolynomialNumerator m (Sum.elim b β) (Sum.elim z ζ) /
      (m.factorial : ℂ))
    (G := carlsonRGeneratingKernel β ζ)
    (fun t ht => hasSum_carlsonRPolynomialNumerator_of_lt (fun i => hδz (Sum.inl i)) ht)
    (fun t ht => hasSum_carlsonRPolynomialNumerator_of_lt (fun i => hδz (Sum.inr i)) ht)
    (fun t ht => ?_) n
  have h := (hasSum_carlsonRPolynomialNumerator_of_lt (b := Sum.elim b β) hδz ht).1
  simpa [carlsonRGeneratingKernel, Fintype.prod_sum_type, mul_comm] using h

/-- **Exercise 6.2-2**, in numerator form: adjoining one node `ζ` with parameter `β`,
`Nₙ(b, β; z, ζ)/n! = ∑ₘ Nₘ(b; z)/m! · (β)_(n-m) ζ^(n-m)/(n-m)!`. -/
theorem carlsonRPolynomialNumerator_sumElim_unit (n : ℕ) (b z : ι → ℂ) (β ζ : ℂ) :
    carlsonRPolynomialNumerator n (Sum.elim b fun _ : Unit => β) (Sum.elim z fun _ => ζ) /
        (n.factorial : ℂ) =
      ∑ m ∈ range (n + 1), carlsonRPolynomialNumerator m b z / (m.factorial : ℂ) *
        ((ascPochhammer ℂ (n - m)).eval β * ζ ^ (n - m) / ((n - m).factorial : ℂ)) := by
  rw [carlsonRPolynomialNumerator_sumElim]
  refine sum_congr rfl fun m _ => ?_
  rw [carlsonRPolynomialNumerator_const]
  simp

/-- **Exercise 6.6-7** (addition of parameters), in numerator form:
`Nₙ(b + β; z)/n! = ∑ₘ Nₘ(b; z)/m! · N_(n-m)(β; z)/(n-m)!`. -/
theorem carlsonRPolynomialNumerator_add_params (n : ℕ) (b β z : ι → ℂ) :
    carlsonRPolynomialNumerator n (b + β) z / (n.factorial : ℂ) =
      ∑ m ∈ range (n + 1), carlsonRPolynomialNumerator m b z / (m.factorial : ℂ) *
        (carlsonRPolynomialNumerator (n - m) β z / ((n - m).factorial : ℂ)) := by
  obtain ⟨δ, hδ, hδz⟩ := exists_radius z
  refine coeff_eq_sum_mul_of_hasSum hδ (F := carlsonRGeneratingKernel b z)
    (A := fun m => carlsonRPolynomialNumerator m b z / (m.factorial : ℂ))
    (B := fun m => carlsonRPolynomialNumerator m β z / (m.factorial : ℂ))
    (C := fun m => carlsonRPolynomialNumerator m (b + β) z / (m.factorial : ℂ))
    (G := carlsonRGeneratingKernel β z)
    (fun t ht => hasSum_carlsonRPolynomialNumerator_of_lt hδz ht)
    (fun t ht => hasSum_carlsonRPolynomialNumerator_of_lt hδz ht) (fun t ht => ?_) n
  have h := (hasSum_carlsonRPolynomialNumerator_of_lt (b := b + β) hδz ht).1
  convert h using 1
  simp only [carlsonRGeneratingKernel, ← prod_mul_distrib, Pi.add_apply]
  refine prod_congr rfl fun i _ => ?_
  have hne : 1 - t * z i ≠ 0 := by
    intro h0
    have h1 : ‖t * z i‖ < 1 := by
      rw [norm_mul]
      rcases eq_or_ne (z i) 0 with hz | hz
      · simp [hz]
      · calc ‖t‖ * ‖z i‖ < δ * ‖z i‖ := mul_lt_mul_of_pos_right ht (norm_pos_iff.mpr hz)
          _ ≤ 1 := hδz i
    rw [sub_eq_zero] at h0
    rw [← h0] at h1; simp at h1
  rw [cpow_add _ _ hne]
  field_simp

/-- **Exercise 6.6-12**, in numerator form: raising one parameter by one,
`Nₙ(b + eᵢ; z)/n! = ∑ₘ Nₘ(b; z)/m! · zᵢ^(n-m)`. -/
theorem carlsonRPolynomialNumerator_addDirichletUnit (n : ℕ) (b z : ι → ℂ) (i : ι) :
    carlsonRPolynomialNumerator n (addDirichletUnit b i) z / (n.factorial : ℂ) =
      ∑ m ∈ range (n + 1),
        carlsonRPolynomialNumerator m b z / (m.factorial : ℂ) * z i ^ (n - m) := by
  classical
  obtain ⟨δ, hδ, hδz⟩ := exists_radius z
  have hlt : ∀ t : ℂ, ‖t‖ < δ → ∀ j, ‖t * z j‖ < 1 := fun t ht j => by
    rw [norm_mul]
    rcases eq_or_ne (z j) 0 with hz | hz
    · simp [hz]
    · calc ‖t‖ * ‖z j‖ < δ * ‖z j‖ := mul_lt_mul_of_pos_right ht (norm_pos_iff.mpr hz)
        _ ≤ 1 := hδz j
  refine coeff_eq_sum_mul_of_hasSum hδ (F := carlsonRGeneratingKernel b z)
    (A := fun m => carlsonRPolynomialNumerator m b z / (m.factorial : ℂ))
    (B := fun m => z i ^ m)
    (C := fun m => carlsonRPolynomialNumerator m (addDirichletUnit b i) z / (m.factorial : ℂ))
    (G := fun t => (1 - t * z i)⁻¹)
    (fun t ht => hasSum_carlsonRPolynomialNumerator_of_lt hδz ht)
    (fun t ht => ?_) (fun t ht => ?_) n
  · have h := hlt t ht i
    refine ⟨?_, ?_⟩
    · simpa [mul_pow, mul_comm] using hasSum_geometric_of_norm_lt_one h
    · simpa [mul_pow, mul_comm, norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) h
  · have h := (hasSum_carlsonRPolynomialNumerator_of_lt (b := addDirichletUnit b i) hδz ht).1
    convert h using 1
    simp only [carlsonRGeneratingKernel]
    rw [← prod_mul_prod_compl {i}, ← prod_mul_prod_compl {i} (f := fun j =>
      1 / (1 - t * z j) ^ addDirichletUnit b i j)]
    have hcompl : ∏ j ∈ ({i} : Finset ι)ᶜ, 1 / (1 - t * z j) ^ addDirichletUnit b i j =
        ∏ j ∈ ({i} : Finset ι)ᶜ, 1 / (1 - t * z j) ^ b j :=
      prod_congr rfl fun j hj => by
        rw [addDirichletUnit, Function.update_of_ne (by simpa using hj)]
    have hne : 1 - t * z i ≠ 0 := by
      intro h0
      have h1 := hlt t ht i
      rw [sub_eq_zero] at h0
      rw [← h0] at h1; simp at h1
    rw [hcompl, prod_singleton, prod_singleton, addDirichletUnit, Function.update_self,
      cpow_add _ _ hne, cpow_one]
    field_simp

/-- **Exercise 6.6-8**, in numerator form: with squared nodes,
`Nₙ(b; z²)/n! = ∑_{m ≤ 2n} (-1)ᵐ Nₘ(b; z)/m! · N_(2n-m)(b; z)/(2n-m)!`. -/
theorem carlsonRPolynomialNumerator_sq_nodes (n : ℕ) (b z : ι → ℂ) :
    carlsonRPolynomialNumerator n b (fun i => z i ^ 2) / (n.factorial : ℂ) =
      ∑ m ∈ range (2 * n + 1), (-1) ^ m * (carlsonRPolynomialNumerator m b z / (m.factorial : ℂ)) *
        (carlsonRPolynomialNumerator (2 * n - m) b z / ((2 * n - m).factorial : ℂ)) := by
  classical
  obtain ⟨δ, hδ, hδz⟩ := exists_radius z
  have hneg : ∀ i, δ * ‖(fun i => -z i) i‖ ≤ 1 := fun i => by simpa using hδz i
  have hsq : ∀ i, δ ^ 2 * ‖(fun i => z i ^ 2) i‖ ≤ 1 := fun i => by
    simp only [norm_pow]
    have h0 : 0 ≤ δ * ‖z i‖ := by positivity
    calc δ ^ 2 * ‖z i‖ ^ 2 = (δ * ‖z i‖) ^ 2 := by ring
      _ ≤ 1 := by nlinarith [hδz i]
  set C : ℕ → ℂ := fun k => if Even k then
    carlsonRPolynomialNumerator (k / 2) b (fun i => z i ^ 2) / ((k / 2).factorial : ℂ) else 0
  have key := coeff_eq_sum_mul_of_hasSum hδ (F := carlsonRGeneratingKernel b z)
    (G := carlsonRGeneratingKernel b fun i => -z i)
    (A := fun m => carlsonRPolynomialNumerator m b z / (m.factorial : ℂ))
    (B := fun m => carlsonRPolynomialNumerator m b (fun i => -z i) / (m.factorial : ℂ)) (C := C)
    (fun t ht => hasSum_carlsonRPolynomialNumerator_of_lt hδz ht)
    (fun t ht => hasSum_carlsonRPolynomialNumerator_of_lt hneg ht) (fun t ht => ?_) (2 * n)
  · have hC2 : C (2 * n) = carlsonRPolynomialNumerator n b (fun i => z i ^ 2) /
        (n.factorial : ℂ) := by
      simp [C, Nat.mul_div_cancel_left n two_pos]
    rw [← hC2, key]
    refine sum_congr rfl fun m hm => ?_
    have hmn : m ≤ 2 * n := Nat.lt_succ_iff.mp (mem_range.mp hm)
    have hs := carlsonRPolynomialNumerator_smul (2 * n - m) b z (-1)
    simp only [neg_one_mul] at hs
    rw [hs]
    have : ((-1 : ℂ)) ^ (2 * n - m) = (-1) ^ m := by
      rw [← mul_right_inj' (pow_ne_zero m (by norm_num : (-1 : ℂ) ≠ 0)), ← pow_add,
        Nat.add_sub_cancel' hmn, pow_mul, ← pow_add, ← two_mul, pow_mul]; norm_num
    rw [this]
    ring
  · -- the product of the two kernels is the squared-node kernel at `t²`
    have htz : ∀ i, ‖t * z i‖ < 1 := fun i => by
      rw [norm_mul]
      rcases eq_or_ne (z i) 0 with hz | hz
      · simp [hz]
      · calc ‖t‖ * ‖z i‖ < δ * ‖z i‖ := mul_lt_mul_of_pos_right ht (norm_pos_iff.mpr hz)
          _ ≤ 1 := hδz i
    have ht2 : ‖t ^ 2‖ < δ ^ 2 := by
      rw [norm_pow]; exact pow_lt_pow_left₀ ht (norm_nonneg _) two_ne_zero
    have h2 := (hasSum_carlsonRPolynomialNumerator_of_lt (b := b) hsq ht2).1
    have hkernel : carlsonRGeneratingKernel b z t * carlsonRGeneratingKernel b (fun i => -z i) t =
        carlsonRGeneratingKernel b (fun i => z i ^ 2) (t ^ 2) := by
      simp only [carlsonRGeneratingKernel, ← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      have hre : ∀ w : ℂ, ‖w‖ < 1 → 0 < (1 - w).re := fun w hw => by
        have := (abs_re_le_norm w).trans_lt hw
        simp only [sub_re, one_re]; linarith [le_abs_self w.re]
      have h1 := hre _ (htz i)
      have h2' := hre (-(t * z i)) (by rw [norm_neg]; exact htz i)
      rw [show 1 - t ^ 2 * z i ^ 2 = (1 - t * z i) * (1 - -(t * z i)) by ring,
        mul_cpow_of_re_pos h1 h2', show t * -z i = -(t * z i) by ring]
      field_simp
    rw [hkernel]
    have hinj : Function.Injective fun k : ℕ => 2 * k := fun a b h => by simpa using h
    refine (hinj.hasSum_iff (f := fun k => C k * t ^ k) fun k hk => ?_).mp ?_
    · have hodd : ¬ Even k := by
        rintro ⟨r, rfl⟩; exact hk ⟨r, by ring⟩
      simp [C, hodd]
    · refine h2.congr_fun fun k => ?_
      simp [C, Function.comp, Nat.mul_div_cancel_left k two_pos, pow_mul]

/-- Raising the degree by one: `N_(n+1)(b; z) = ∑ᵢ bᵢ zᵢ Nₙ(b + eᵢ; z)` for all parameters. -/
theorem carlsonRPolynomialNumerator_succ_eq_sum (n : ℕ) (b z : ι → ℂ) :
    carlsonRPolynomialNumerator (n + 1) b z =
      ∑ i, b i * z i * carlsonRPolynomialNumerator n (addDirichletUnit b i) z := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [carlsonRPolynomialNumerator_of_isEmpty]
  have hmap (i : ι) (b : ι → ℂ) : AnalyticAt ℂ (fun b => (addDirichletUnit b i, z)) b := by
    apply AnalyticAt.prod _ analyticAt_const
    apply AnalyticAt.pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa [addDirichletUnit] using!
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt b).add analyticAt_const
    · simpa [addDirichletUnit, hji] using! (ContinuousLinearMap.proj (R := ℂ) j).analyticAt b
  have hL : AnalyticOnNhd ℂ (fun b => carlsonRPolynomialNumerator (n + 1) b z) Set.univ := by
    intro b _
    have hpair : AnalyticAt ℂ (fun b : ι → ℂ => (b, z)) b := analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp_of_eq (g := fun p : (ι → ℂ) × (ι → ℂ) =>
      carlsonRPolynomialNumerator (n + 1) p.1 p.2) (f := fun b : ι → ℂ => (b, z))
      (analyticOnNhd_carlsonRPolynomialNumerator_joint _ (b, z) (Set.mem_univ _)) hpair rfl
  have hR : AnalyticOnNhd ℂ (fun b => ∑ i, b i * z i *
      carlsonRPolynomialNumerator n (addDirichletUnit b i) z) Set.univ := by
    intro b _
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    refine (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt b).mul
      analyticAt_const).mul ?_
    exact AnalyticAt.comp_of_eq (g := fun p : (ι → ℂ) × (ι → ℂ) =>
      carlsonRPolynomialNumerator n p.1 p.2) (f := fun b : ι → ℂ => (addDirichletUnit b i, z))
      (analyticOnNhd_carlsonRPolynomialNumerator_joint _ _ (Set.mem_univ _)) (hmap i b) rfl
  refine congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent hL hR fun b hb => ?_) b
  set c := ∑ i, b i
  have hc : 0 < c.re := by simpa [c] using Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hG : Gamma (c + ((n + 1 : ℕ) : ℂ)) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hnum (k : ℕ) (b' : ι → ℂ) (hb' : b' ∈ mvBetaConvergent) :
      carlsonRPolynomialNumerator k b' z = regDirichletIntegral b'
        (fun u => carlsonAffineForm z u ^ k) * Gamma ((∑ i, b' i) + k) := by
    have hG' : Gamma ((∑ i, b' i) + k) ≠ 0 := Gamma_ne_zero_of_re_pos (by
      have : 0 < ∑ i, (b' i).re := Finset.sum_pos (fun i _ => hb' i) Finset.univ_nonempty
      simp; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have := regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma k b' z
    rw [← regCarlsonDirichletAverage_pow k z hb', regCarlsonDirichletAverage] at this
    rw [this]; field_simp
  have hcont (i : ι) : ContinuousOn (fun u : ι → ℝ => (u i : ℂ) * (z i * carlsonAffineForm z u ^ n))
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    ((continuous_ofReal.comp (continuous_apply i)).mul
      (continuous_const.mul ((continuous_carlsonAffineForm z).pow n))).continuousOn
  rw [hnum (n + 1) b hb]
  have hexp : (fun u : ι → ℝ => carlsonAffineForm z u ^ (n + 1)) =
      fun u => ∑ i, (u i : ℂ) * (z i * carlsonAffineForm z u ^ n) := by
    funext u
    rw [pow_succ, carlsonAffineForm, mul_comm, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, regDirichletIntegral_sum hb fun i _ => hcont i, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hbi := addDirichletUnit_mem_mvBetaConvergent hb i
  rw [← mul_regDirichletIntegral_addDirichletUnit hb i, regDirichletIntegral_smul,
    hnum n _ hbi, sum_addDirichletUnit]
  rw [show c + 1 + (n : ℂ) = c + ((n + 1 : ℕ) : ℂ) by push_cast; ring]
  ring

/-- **Exercise 6.6-13** (Tobey's relation), in numerator form: with the weighted power sums
`pₖ = ∑ᵢ bᵢ zᵢᵏ`, `N_(n+1)(b; z)/n! = ∑_{m ≤ n} Nₘ(b; z)/m! · p_(n+1-m)`. -/
theorem carlsonRPolynomialNumerator_tobey (n : ℕ) (b z : ι → ℂ) :
    carlsonRPolynomialNumerator (n + 1) b z / (n.factorial : ℂ) =
      ∑ m ∈ range (n + 1), carlsonRPolynomialNumerator m b z / (m.factorial : ℂ) *
        ∑ i, b i * z i ^ (n + 1 - m) := by
  rw [carlsonRPolynomialNumerator_succ_eq_sum, Finset.sum_div]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_div_assoc, carlsonRPolynomialNumerator_addDirichletUnit, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [show n + 1 - m = (n - m) + 1 by omega, pow_succ]
  ring

/-- **Exercise 6.2-13, first relation**: `c(c + 1) R₂(b, z) = N₂(b; z) = ∑ bᵢ zᵢ² + (∑ bᵢ zᵢ)²`. -/
theorem carlsonRPolynomialNumerator_two (b z : ι → ℂ) :
    carlsonRPolynomialNumerator 2 b z = ∑ i, b i * z i ^ 2 + (∑ i, b i * z i) ^ 2 := by
  classical
  rw [carlsonRPolynomialNumerator_succ_eq_sum]
  simp only [carlsonRPolynomialNumerator_one]
  have h (i : ι) : ∑ j, addDirichletUnit b i j * z j = (∑ j, b j * z j) + z i := by
    rw [show (fun j => addDirichletUnit b i j * z j) = fun j => b j * z j +
        if j = i then z i else 0 by
      funext j; by_cases hj : j = i
      · subst hj; simp [addDirichletUnit]; ring
      · simp [addDirichletUnit, hj]]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp
  simp_rw [h, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [show (fun i => b i * z i * z i) = fun i => b i * z i ^ 2 by funext i; ring]
  ring

/-- `∑ᵢ ∑ⱼ bᵢ bⱼ (zᵢ - zⱼ)² = 2 (∑ bᵢ)(∑ bᵢ zᵢ²) - 2 (∑ bᵢ zᵢ)²`. -/
theorem sum_sum_mul_sub_sq (b z : ι → ℂ) :
    ∑ i, ∑ j, b i * b j * (z i - z j) ^ 2 =
      2 * (∑ i, b i) * ∑ i, b i * z i ^ 2 - 2 * (∑ i, b i * z i) ^ 2 := by
  have e : ∀ i j, b i * b j * (z i - z j) ^ 2 = (b i * z i ^ 2) * b j + b i * (b j * z j ^ 2) -
      (2 * (b i * z i)) * (b j * z j) := fun i j => by ring
  simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Finset.mul_sum]
  ring

/-- **Exercise 6.2-13, second relation**: with `c = ∑ bᵢ`,
`c² (c + 1) R₂(b, z) = c N₂(b; z) = (c + 1)(∑ bᵢ zᵢ)² + ½ ∑ᵢ ∑ⱼ bᵢ bⱼ (zᵢ - zⱼ)²`. -/
theorem sum_mul_carlsonRPolynomialNumerator_two (b z : ι → ℂ) :
    (∑ i, b i) * carlsonRPolynomialNumerator 2 b z =
      ((∑ i, b i) + 1) * (∑ i, b i * z i) ^ 2 +
        (1 / 2) * ∑ i, ∑ j, b i * b j * (z i - z j) ^ 2 := by
  rw [carlsonRPolynomialNumerator_two, sum_sum_mul_sub_sq]; ring

/-- **Exercise 6.2-14, first relation** (the weighted variance): if `∑ wᵢ = 1` and
`z̄ = ∑ wᵢ zᵢ`, then `∑ wᵢ (zᵢ - z̄)² = ½ ∑ᵢ ∑ⱼ wᵢ wⱼ (zᵢ - zⱼ)²`. -/
theorem sum_mul_sub_mean_sq {w z : ι → ℂ} (hw : ∑ i, w i = 1) :
    ∑ i, w i * (z i - ∑ j, w j * z j) ^ 2 = (1 / 2) * ∑ i, ∑ j, w i * w j * (z i - z j) ^ 2 := by
  set m := ∑ j, w j * z j
  have e : ∀ i, w i * (z i - m) ^ 2 = w i * z i ^ 2 - (2 * m) * (w i * z i) + m ^ 2 * w i :=
    fun i => by ring
  simp_rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_sum_mul_sub_sq, hw]
  ring

/-- **Exercise 6.6-1** (Cauchy's formula for the generating relation): for `0 < r` with
`r ‖zᵢ‖ < 1`, `(c)ₙ Rₙ(b, z) = Nₙ(b; z) = n!/(2πi) ∮_{|t| = r} t^(-n-1) ∏ (1 - t zᵢ)^(-bᵢ) dt`. -/
theorem carlsonRPolynomialNumerator_eq_circleIntegral (n : ℕ) (b z : ι → ℂ) {r : ℝ}
    (hr : 0 < r) (hrz : ∀ i, r * ‖z i‖ < 1) :
    carlsonRPolynomialNumerator n b z = (n.factorial : ℂ) * ((2 * Real.pi * I : ℂ)⁻¹ *
      ∮ t in C(0, r), (1 / t) ^ n * t⁻¹ * carlsonRGeneratingKernel b z t) := by
  have hlt : ∀ t : ℂ, ‖t‖ ≤ r → ∀ i, ‖t * z i‖ < 1 := fun t ht i => by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans_lt (hrz i)
  have hd : DifferentiableOn ℂ (carlsonRGeneratingKernel b z) (Metric.closedBall 0 r) := by
    intro t ht
    have ht' : ‖t‖ ≤ r := by simpa using ht
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold carlsonRGeneratingKernel
    refine DifferentiableAt.fun_finsetProd fun i _ => ?_
    have hre : 0 < (1 - t * z i).re := by
      have := (abs_re_le_norm (t * z i)).trans_lt (hlt t ht' i)
      simp only [sub_re, one_re]; linarith [le_abs_self (t * z i).re]
    have hslit : 1 - t * z i ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hre)
    have hne : (1 - t * z i) ^ b i ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; exact fun h => slitPlane_ne_zero hslit h.1
    simp only [one_div]
    have hl : DifferentiableAt ℂ (fun s : ℂ => 1 - s * z i) t := by fun_prop
    exact (hl.cpow (differentiableAt_const (b i)) hslit).inv hne
  set R : NNReal := ⟨r, hr.le⟩
  have hps := hd.hasFPowerSeriesOnBall (R := R) (by exact_mod_cast hr)
  have hRr : ((R : NNReal) : ℝ) = r := rfl
  rw [hRr] at hps
  set p := cauchyPowerSeries (carlsonRGeneratingKernel b z) 0 r
  have hcoeff := coeff_eq_of_hasSum_pow hr
    (a := fun n => carlsonRPolynomialNumerator n b z / (n.factorial : ℂ))
    (b := fun n => p.coeff n)
    (fun t ht => hasSum_carlsonRPolynomialNumerator_div_factorial b z t (hlt t ht.le))
    (fun t ht => by
      have hmem : t ∈ Metric.eball (0 : ℂ) R := by
        rw [Metric.mem_eball, edist_zero_right]; exact_mod_cast ht
      have := hps.hasSum hmem
      simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff, mul_comm] using this)
  have hn := congrFun hcoeff n
  have hc : p.coeff n = (2 * Real.pi * I : ℂ)⁻¹ *
      ∮ t in C(0, r), (1 / t) ^ n * t⁻¹ * carlsonRGeneratingKernel b z t := by
    have h1 := p.apply_eq_pow_smul_coeff (n := n) (z := (1 : ℂ))
    rw [one_pow, one_smul] at h1
    rw [← h1, cauchyPowerSeries_apply]
    simp [smul_eq_mul, mul_assoc]
  rw [← hc, ← hn]
  field_simp [Nat.cast_ne_zero.mpr n.factorial_ne_zero]

end Carlson
