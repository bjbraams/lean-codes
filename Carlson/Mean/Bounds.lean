/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.StrictOrder

/-!
# Carlson's elementary bounds and their Euler transforms

Strict bounds compare R with arithmetic powers, weighted power sums, geometric
powers, and the Euler transforms of the first two expressions. The exponent here
is `t`, the negative of the parameter `a` in Carlson's 1966 paper.

All statements assume positive nodes and parameters. Strict inequalities require
nonconstant nodes; the exceptional exponents have explicit formulas.

## References

* B. C. Carlson, *Some inequalities for hypergeometric functions*, Proc. AMS 17
  (1966), Theorem 2, equations (2.12)–(2.17).
-/

open ProbabilityTheory Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι] {b x : ι → ℝ}

omit [Fintype ι] [Nonempty ι] in
/-- Inverting positive nodes preserves nonconstancy. -/
private theorem nonconstant_inv (hne : ∃ i j, x i ≠ x j) :
    ∃ i j, (x i)⁻¹ ≠ (x j)⁻¹ := by
  obtain ⟨i, j, hij⟩ := hne
  exact ⟨i, j, fun h => hij (inv_injective h)⟩

/-- Euler's multiplicative factor is the geometric mean to minus the total parameter. -/
theorem prod_rpow_neg_eq_geometric (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    (∏ i, x i ^ (-b i)) =
      (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ (-(∑ i, b i)) := by
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  rw [← carlsonRReal_neg_sum hb hx, ← carlsonMeanReal_rpow (neg_ne_zero.mpr hc.ne') hb hx,
    carlsonMeanReal_neg_sum hb hx]

/-- Every nonzero weighted power sum strictly exceeds the corresponding geometric power
on nonconstant positive nodes. -/
theorem geometric_rpow_lt_weightedPower {t : ℝ} (ht : t ≠ 0)
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ t <
      ∑ i, (b i / ∑ j, b j) * x i ^ t := by
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hw : ∑ i, b i / ∑ j, b j = 1 := by rw [← Finset.sum_div, div_self hc.ne']
  obtain ⟨i, j, hij⟩ := hne
  have hn : t * Real.log (x i) ≠ t * Real.log (x j) := by
    intro h
    exact hij (Real.log_injOn_pos (hx i) (hx j) (mul_left_cancel₀ ht h))
  have h := strictConvexOn_exp.map_sum_lt (fun i _ => div_pos (hb i) hc) hw
    (fun i _ => mem_univ (t * Real.log (x i)))
    ⟨i, Finset.mem_univ i, j, Finset.mem_univ j, hn⟩
  simp only [smul_eq_mul] at h
  have he : (∑ i, (b i / ∑ j, b j) * (t * Real.log (x i))) =
      (∑ i, (b i / ∑ j, b j) * Real.log (x i)) * t := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, Real.exp_mul] at h
  simpa only [Real.rpow_def_of_pos (hx _), mul_comm t] using h

/-- A positive arithmetic power strictly exceeds the geometric power for nonconstant nodes. -/
theorem geometric_rpow_lt_arithmetic_rpow {t : ℝ} (ht : 0 < t)
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ t <
      (∑ i, (b i / ∑ j, b j) * x i) ^ t := by
  have h := geometric_rpow_lt_weightedPower (by norm_num : (1 : ℝ) ≠ 0) hb hx hne
  simp only [Real.rpow_one] at h
  exact Real.rpow_lt_rpow (Real.exp_pos _).le h ht

/-- A negative arithmetic power lies strictly below the geometric power for nonconstant nodes. -/
theorem arithmetic_rpow_lt_geometric_rpow {t : ℝ} (ht : t < 0)
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (∑ i, (b i / ∑ j, b j) * x i) ^ t <
      (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ t := by
  have h := geometric_rpow_lt_weightedPower (by norm_num : (1 : ℝ) ≠ 0) hb hx hne
  simp only [Real.rpow_one] at h
  exact Real.rpow_lt_rpow_of_neg (Real.exp_pos _) h ht

/-- The geometric-power bound is unchanged by Euler inversion. -/
theorem euler_geometric_rpow (t : ℝ)
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    (∏ i, x i ^ (-b i)) *
      (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log ((x i)⁻¹))) ^ (-(∑ i, b i) - t) =
      (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ t := by
  rw [prod_rpow_neg_eq_geometric hb hx]
  simp_rw [Real.log_inv, mul_neg, Finset.sum_neg_distrib, Real.exp_neg,
    Real.inv_rpow (Real.exp_pos _).le, ← Real.rpow_neg (Real.exp_pos _).le]
  rw [← Real.rpow_add (Real.exp_pos _)]
  congr 1
  ring

/-- For orders above minus the total parameter, the Euler arithmetic bound is below
 the geometric power. -/
theorem euler_arithmetic_rpow_lt_geometric {t : ℝ}
    (ht : -(∑ i, b i) < t) (hb : b ∈ mvRealBetaDomain)
    (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (∏ i, x i ^ (-b i)) * (∑ i, (b i / ∑ j, b j) * (x i)⁻¹) ^ (-(∑ i, b i) - t) <
      (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ t := by
  have h := arithmetic_rpow_lt_geometric_rpow (sub_neg.mpr ht) hb
    (fun i => inv_pos.mpr (hx i)) (nonconstant_inv hne)
  have hp : 0 < ∏ i, x i ^ (-b i) := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hx i) _)
  simpa only [euler_geometric_rpow t hb hx] using mul_lt_mul_of_pos_left h hp

/-- For orders below minus the total parameter, the geometric power is below
 the Euler arithmetic bound. -/
theorem geometric_lt_euler_arithmetic_rpow {t : ℝ}
    (ht : t < -(∑ i, b i)) (hb : b ∈ mvRealBetaDomain)
    (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ t <
      (∏ i, x i ^ (-b i)) * (∑ i, (b i / ∑ j, b j) * (x i)⁻¹) ^ (-(∑ i, b i) - t) := by
  have h := geometric_rpow_lt_arithmetic_rpow (sub_pos.mpr ht) hb
    (fun i => inv_pos.mpr (hx i)) (nonconstant_inv hne)
  have hp : 0 < ∏ i, x i ^ (-b i) := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hx i) _)
  simpa only [euler_geometric_rpow t hb hx] using mul_lt_mul_of_pos_left h hp

/-- Except at the geometric order, the Euler power-sum bound exceeds the geometric power. -/
theorem geometric_lt_euler_weightedPower {t : ℝ}
    (ht : t ≠ -(∑ i, b i)) (hb : b ∈ mvRealBetaDomain)
    (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ t <
      (∏ i, x i ^ (-b i)) *
        (∑ i, (b i / ∑ j, b j) * ((x i)⁻¹) ^ (-(∑ i, b i) - t)) := by
  have h := geometric_rpow_lt_weightedPower (sub_ne_zero.mpr ht.symm) hb
    (fun i => inv_pos.mpr (hx i)) (nonconstant_inv hne)
  have hp : 0 < ∏ i, x i ^ (-b i) := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hx i) _)
  simpa only [euler_geometric_rpow t hb hx] using mul_lt_mul_of_pos_left h hp

/-- A positive increase in power raises a nonconstant weighted power sum by more than
 the corresponding geometric power. -/
theorem geometric_rpow_mul_weightedPower_lt {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ s *
      (∑ i, (b i / ∑ j, b j) * x i ^ t) <
      ∑ i, (b i / ∑ j, b j) * x i ^ (t + s) := by
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hw : ∑ i, b i / ∑ j, b j = 1 := by rw [← Finset.sum_div, div_self hc.ne']
  have hJ : 0 < ∑ i, (b i / ∑ j, b j) * x i ^ t :=
    Finset.sum_pos (fun i _ => mul_pos (div_pos (hb i) hc)
      (Real.rpow_pos_of_pos (hx i) t)) Finset.univ_nonempty
  have hg := Real.rpow_lt_rpow (Real.rpow_pos_of_pos (Real.exp_pos _) t).le
    (geometric_rpow_lt_weightedPower ht.ne' hb hx hne) (div_pos hs ht)
  rw [← Real.rpow_mul (Real.exp_pos _).le, mul_div_cancel₀ _ ht.ne'] at hg
  have hj := (strictConvexOn_rpow (by linarith [div_pos hs ht] : 1 < 1 + s / t)).convexOn.map_sum_le
    (fun i _ => (div_pos (hb i) hc).le) hw
    (fun i _ => (Real.rpow_pos_of_pos (hx i) t).le)
  simp only [smul_eq_mul] at hj
  have he (i : ι) : (x i ^ t) ^ (1 + s / t) = x i ^ (t + s) := by
    rw [← Real.rpow_mul (hx i).le]
    congr 1
    field_simp
  simp_rw [he] at hj
  calc
    _ < (∑ i, (b i / ∑ j, b j) * x i ^ t) ^ (s / t) *
        (∑ i, (b i / ∑ j, b j) * x i ^ t) := mul_lt_mul_of_pos_right hg hJ
    _ = (∑ i, (b i / ∑ j, b j) * x i ^ t) ^ (1 + s / t) := by
      rw [Real.rpow_add hJ, Real.rpow_one, mul_comm]
    _ ≤ _ := hj

/-- At positive orders, the power-sum bound is smaller than its Euler transform. -/
theorem weightedPower_lt_euler_weightedPower {t : ℝ} (ht : 0 < t)
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (∑ i, (b i / ∑ j, b j) * x i ^ t) <
      (∏ i, x i ^ (-b i)) *
        (∑ i, (b i / ∑ j, b j) * ((x i)⁻¹) ^ (-(∑ i, b i) - t)) := by
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have h := geometric_rpow_mul_weightedPower_lt hc ht hb hx hne
  have hg : 0 < (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ (∑ i, b i) :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
  rw [prod_rpow_neg_eq_geometric hb hx, Real.rpow_neg (Real.exp_pos _).le]
  have he (i : ι) : ((x i)⁻¹) ^ (-(∑ i, b i) - t) = x i ^ (t + ∑ i, b i) := by
    rw [Real.inv_rpow (hx i).le, ← Real.rpow_neg (hx i).le]
    congr 1
    ring
  simp_rw [he]
  exact (lt_inv_mul_iff₀ hg).mpr h

/-- Below minus the total parameter, the Euler power-sum bound is smaller than the
 original power-sum bound. -/
theorem euler_weightedPower_lt_weightedPower {t : ℝ} (ht : t < -(∑ i, b i))
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (∏ i, x i ^ (-b i)) *
        (∑ i, (b i / ∑ j, b j) * ((x i)⁻¹) ^ (-(∑ i, b i) - t)) <
      ∑ i, (b i / ∑ j, b j) * x i ^ t := by
  have h := weightedPower_lt_euler_weightedPower (sub_pos.mpr ht) hb
    (fun i => inv_pos.mpr (hx i)) (nonconstant_inv hne)
  have hp : 0 < ∏ i, x i ^ (-b i) := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hx i) _)
  have he : (∏ i, x i ^ (-b i)) * (∏ i, ((x i)⁻¹) ^ (-b i)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    rw [Real.inv_rpow (hx i).le, mul_inv_cancel₀ (Real.rpow_pos_of_pos (hx i) _).ne']
  have he' : -(∑ i, b i) - (-(∑ i, b i) - t) = t := by ring
  simpa only [inv_inv, he', ← mul_assoc, he, one_mul] using mul_lt_mul_of_pos_left h hp

/-- When `t + C ≥ 1`, the arithmetic-power bound is smaller than the Euler power sum.
This resolves the minimum in Carlson's bound (2.13) under its additional hypothesis. -/
theorem arithmetic_rpow_lt_euler_weightedPower {t : ℝ} (ht : 1 ≤ t + ∑ i, b i)
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (∑ i, (b i / ∑ j, b j) * x i) ^ t <
      (∏ i, x i ^ (-b i)) *
        (∑ i, (b i / ∑ j, b j) * ((x i)⁻¹) ^ (-(∑ i, b i) - t)) := by
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hw : ∑ i, b i / ∑ j, b j = 1 := by rw [← Finset.sum_div, div_self hc.ne']
  have hA : 0 < ∑ i, (b i / ∑ j, b j) * x i :=
    Finset.sum_pos (fun i _ => mul_pos (div_pos (hb i) hc) (hx i)) Finset.univ_nonempty
  have h := mul_lt_mul_of_pos_right (geometric_rpow_lt_arithmetic_rpow hc hb hx hne)
    (Real.rpow_pos_of_pos hA t)
  rw [← Real.rpow_add hA, add_comm (∑ i, b i)] at h
  have hj := (convexOn_rpow ht).map_sum_le (fun i _ => (div_pos (hb i) hc).le) hw
    (fun i _ => (hx i).le)
  simp only [smul_eq_mul] at hj
  have hg : 0 < (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ (∑ i, b i) :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
  rw [prod_rpow_neg_eq_geometric hb hx, Real.rpow_neg (Real.exp_pos _).le]
  have he (i : ι) : ((x i)⁻¹) ^ (-(∑ i, b i) - t) = x i ^ (t + ∑ i, b i) := by
    rw [Real.inv_rpow (hx i).le, ← Real.rpow_neg (hx i).le]
    congr 1
    ring
  simp_rw [he]
  exact (lt_inv_mul_iff₀ hg).mpr (h.trans_le hj)

/-- At orders at most minus one, the Euler arithmetic-power bound is smaller than
 the power sum. This resolves the minimum in Carlson's bound (2.15). -/
theorem euler_arithmetic_rpow_lt_weightedPower {t : ℝ} (ht : t ≤ -1)
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (∏ i, x i ^ (-b i)) * (∑ i, (b i / ∑ j, b j) * (x i)⁻¹) ^ (-(∑ i, b i) - t) <
      ∑ i, (b i / ∑ j, b j) * x i ^ t := by
  have h := arithmetic_rpow_lt_euler_weightedPower
    (by linarith : 1 ≤ (-(∑ i, b i) - t) + ∑ i, b i) hb
    (fun i => inv_pos.mpr (hx i)) (nonconstant_inv hne)
  have hp : 0 < ∏ i, x i ^ (-b i) := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hx i) _)
  have he : (∏ i, x i ^ (-b i)) * (∏ i, ((x i)⁻¹) ^ (-b i)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    rw [Real.inv_rpow (hx i).le, mul_inv_cancel₀ (Real.rpow_pos_of_pos (hx i) _).ne']
  have he' : -(∑ i, b i) - (-(∑ i, b i) - t) = t := by ring
  simpa only [inv_inv, he', ← mul_assoc, he, one_mul] using mul_lt_mul_of_pos_left h hp

/-- The Euler-transformed Jensen bounds when the transformed order is negative. -/
theorem carlsonRReal_euler_strict_bounds_of_neg {t : ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j)
    (ht : -(∑ i, b i) < t) :
    (∏ i, x i ^ (-b i)) * (∑ i, (b i / ∑ j, b j) * (x i)⁻¹) ^ (-(∑ i, b i) - t) <
        carlsonRReal t b x ∧
      carlsonRReal t b x < (∏ i, x i ^ (-b i)) *
        (∑ i, (b i / ∑ j, b j) * ((x i)⁻¹) ^ (-(∑ i, b i) - t)) := by
  have h := carlsonRReal_strict_bounds_of_neg (sub_neg.mpr ht) hb
    (fun i => inv_pos.mpr (hx i)) (nonconstant_inv hne)
  have hp : 0 < ∏ i, x i ^ (-b i) := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hx i) _)
  rw [carlsonRReal_euler t hb hx]
  exact ⟨mul_lt_mul_of_pos_left h.1 hp, mul_lt_mul_of_pos_left h.2 hp⟩

/-- The Euler-transformed Jensen bounds when the transformed order lies between zero and one. -/
theorem carlsonRReal_euler_strict_bounds_of_pos_of_lt_one {t : ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j)
    (ht0 : t < -(∑ i, b i)) (ht1 : -(∑ i, b i) - 1 < t) :
    (∏ i, x i ^ (-b i)) * (∑ i, (b i / ∑ j, b j) * ((x i)⁻¹) ^ (-(∑ i, b i) - t)) <
        carlsonRReal t b x ∧
      carlsonRReal t b x < (∏ i, x i ^ (-b i)) *
        (∑ i, (b i / ∑ j, b j) * (x i)⁻¹) ^ (-(∑ i, b i) - t) := by
  have h := carlsonRReal_strict_bounds_of_pos_of_lt_one (sub_pos.mpr ht0) (by linarith) hb
    (fun i => inv_pos.mpr (hx i)) (nonconstant_inv hne)
  have hp : 0 < ∏ i, x i ^ (-b i) := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hx i) _)
  rw [carlsonRReal_euler t hb hx]
  exact ⟨mul_lt_mul_of_pos_left h.2 hp, mul_lt_mul_of_pos_left h.1 hp⟩

/-- The Euler-transformed Jensen bounds when the transformed order exceeds one. -/
theorem carlsonRReal_euler_strict_bounds_of_one_lt {t : ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j)
    (ht : t < -(∑ i, b i) - 1) :
    (∏ i, x i ^ (-b i)) * (∑ i, (b i / ∑ j, b j) * (x i)⁻¹) ^ (-(∑ i, b i) - t) <
        carlsonRReal t b x ∧
      carlsonRReal t b x < (∏ i, x i ^ (-b i)) *
        (∑ i, (b i / ∑ j, b j) * ((x i)⁻¹) ^ (-(∑ i, b i) - t)) := by
  have h := carlsonRReal_strict_bounds_of_one_lt (by linarith : 1 < -(∑ i, b i) - t) hb
    (fun i => inv_pos.mpr (hx i)) (nonconstant_inv hne)
  have hp : 0 < ∏ i, x i ^ (-b i) := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hx i) _)
  rw [carlsonRReal_euler t hb hx]
  exact ⟨mul_lt_mul_of_pos_left h.1 hp, mul_lt_mul_of_pos_left h.2 hp⟩

/-- The fourth exceptional exponent in Carlson's table has an explicit reciprocal-mean formula. -/
theorem carlsonRReal_neg_sum_sub_one (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonRReal (-(∑ i, b i) - 1) b x =
      (∏ i, x i ^ (-b i)) * (∑ i, (b i / ∑ j, b j) * (x i)⁻¹) := by
  rw [carlsonRReal_euler _ hb hx, show -(∑ i, b i) - (-(∑ i, b i) - 1) = 1 by ring,
    carlsonRReal_one hb]

/-- In the classical Euler convergence strip, both arithmetic-power lower bounds are
strict and the geometric power is a strict upper bound. -/
theorem carlsonRReal_bounds_between_neg_sum_zero {t : ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j)
    (ht0 : t < 0) (htc : -(∑ i, b i) < t) :
    max ((∑ i, (b i / ∑ j, b j) * x i) ^ t)
      ((∏ i, x i ^ (-b i)) * (∑ i, (b i / ∑ j, b j) * (x i)⁻¹) ^ (-(∑ i, b i) - t)) <
        carlsonRReal t b x ∧
      carlsonRReal t b x < (Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))) ^ t := by
  constructor
  · exact max_lt (carlsonRReal_strict_bounds_of_neg ht0 hb hx hne).1
      (carlsonRReal_euler_strict_bounds_of_neg hb hx hne htc).1
  · have h := Real.rpow_lt_rpow_of_neg (Real.exp_pos _)
      (geometric_lt_carlsonMeanReal hb hx hne htc) ht0
    rwa [carlsonMeanReal_rpow ht0.ne hb hx] at h

/-- Carlson's 1966 bound chain (2.12), for orders greater than one. -/
theorem carlsonRReal_bound_chain_of_one_lt {t : ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j)
    (ht : 1 < t) :
    let C := ∑ i, b i
    let w := fun i => b i / C
    let H := (∑ i, w i * x i) ^ t
    let J := ∑ i, w i * x i ^ t
    let K := (Real.exp (∑ i, w i * Real.log (x i))) ^ t
    let H' := (∏ i, x i ^ (-b i)) * (∑ i, w i * (x i)⁻¹) ^ (-C - t)
    let J' := (∏ i, x i ^ (-b i)) * (∑ i, w i * ((x i)⁻¹) ^ (-C - t))
    H' < K ∧ K < H ∧ H < carlsonRReal t b x ∧ carlsonRReal t b x < J ∧ J < J' := by
  dsimp only
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  exact ⟨euler_arithmetic_rpow_lt_geometric (by linarith) hb hx hne,
    geometric_rpow_lt_arithmetic_rpow ht0 hb hx hne,
    (carlsonRReal_strict_bounds_of_one_lt ht hb hx hne).1,
    (carlsonRReal_strict_bounds_of_one_lt ht hb hx hne).2,
    weightedPower_lt_euler_weightedPower ht0 hb hx hne⟩

/-- Carlson's 1966 bound chain (2.13), for orders between zero and one. -/
theorem carlsonRReal_bound_chain_of_pos_of_lt_one {t : ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j)
    (ht0 : 0 < t) (ht1 : t < 1) :
    let C := ∑ i, b i
    let w := fun i => b i / C
    let H := (∑ i, w i * x i) ^ t
    let J := ∑ i, w i * x i ^ t
    let K := (Real.exp (∑ i, w i * Real.log (x i))) ^ t
    let H' := (∏ i, x i ^ (-b i)) * (∑ i, w i * (x i)⁻¹) ^ (-C - t)
    let J' := (∏ i, x i ^ (-b i)) * (∑ i, w i * ((x i)⁻¹) ^ (-C - t))
    H' < K ∧ K < J ∧ J < carlsonRReal t b x ∧ carlsonRReal t b x < min H J' := by
  dsimp only
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  exact ⟨euler_arithmetic_rpow_lt_geometric (by linarith) hb hx hne,
    geometric_rpow_lt_weightedPower ht0.ne' hb hx hne,
    (carlsonRReal_strict_bounds_of_pos_of_lt_one ht0 ht1 hb hx hne).2,
    lt_min (carlsonRReal_strict_bounds_of_pos_of_lt_one ht0 ht1 hb hx hne).1
      (carlsonRReal_euler_strict_bounds_of_neg hb hx hne (by linarith)).2⟩

/-- Carlson's 1966 bound chain (2.14), throughout the classical Euler convergence strip. -/
theorem carlsonRReal_bound_chain_between_neg_sum_zero {t : ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j)
    (ht0 : t < 0) (htc : -(∑ i, b i) < t) :
    let C := ∑ i, b i
    let w := fun i => b i / C
    let H := (∑ i, w i * x i) ^ t
    let J := ∑ i, w i * x i ^ t
    let K := (Real.exp (∑ i, w i * Real.log (x i))) ^ t
    let H' := (∏ i, x i ^ (-b i)) * (∑ i, w i * (x i)⁻¹) ^ (-C - t)
    let J' := (∏ i, x i ^ (-b i)) * (∑ i, w i * ((x i)⁻¹) ^ (-C - t))
    max H H' < carlsonRReal t b x ∧ carlsonRReal t b x < K ∧ K < min J J' := by
  dsimp only
  exact ⟨(carlsonRReal_bounds_between_neg_sum_zero hb hx hne ht0 htc).1,
    (carlsonRReal_bounds_between_neg_sum_zero hb hx hne ht0 htc).2,
    lt_min (geometric_rpow_lt_weightedPower ht0.ne hb hx hne)
      (geometric_lt_euler_weightedPower htc.ne' hb hx hne)⟩

/-- Carlson's 1966 bound chain (2.15), for orders between minus the total parameter
 minus one and minus the total parameter. -/
theorem carlsonRReal_bound_chain_of_lt_neg_sum {t : ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j)
    (ht0 : t < -(∑ i, b i)) (ht1 : -(∑ i, b i) - 1 < t) :
    let C := ∑ i, b i
    let w := fun i => b i / C
    let H := (∑ i, w i * x i) ^ t
    let J := ∑ i, w i * x i ^ t
    let K := (Real.exp (∑ i, w i * Real.log (x i))) ^ t
    let H' := (∏ i, x i ^ (-b i)) * (∑ i, w i * (x i)⁻¹) ^ (-C - t)
    let J' := (∏ i, x i ^ (-b i)) * (∑ i, w i * ((x i)⁻¹) ^ (-C - t))
    H < K ∧ K < J' ∧ J' < carlsonRReal t b x ∧ carlsonRReal t b x < min H' J := by
  dsimp only
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  exact ⟨arithmetic_rpow_lt_geometric_rpow (by linarith) hb hx hne,
    geometric_lt_euler_weightedPower ht0.ne hb hx hne,
    (carlsonRReal_euler_strict_bounds_of_pos_of_lt_one hb hx hne ht0 ht1).1,
    lt_min (carlsonRReal_euler_strict_bounds_of_pos_of_lt_one hb hx hne ht0 ht1).2
      (carlsonRReal_strict_bounds_of_neg (by linarith) hb hx hne).2⟩

/-- Carlson's 1966 bound chain (2.16), for orders below minus the total parameter minus one. -/
theorem carlsonRReal_bound_chain_of_lt_neg_sum_sub_one {t : ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j)
    (ht : t < -(∑ i, b i) - 1) :
    let C := ∑ i, b i
    let w := fun i => b i / C
    let H := (∑ i, w i * x i) ^ t
    let J := ∑ i, w i * x i ^ t
    let K := (Real.exp (∑ i, w i * Real.log (x i))) ^ t
    let H' := (∏ i, x i ^ (-b i)) * (∑ i, w i * (x i)⁻¹) ^ (-C - t)
    let J' := (∏ i, x i ^ (-b i)) * (∑ i, w i * ((x i)⁻¹) ^ (-C - t))
    H < K ∧ K < H' ∧ H' < carlsonRReal t b x ∧ carlsonRReal t b x < J' ∧ J' < J := by
  dsimp only
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  exact ⟨arithmetic_rpow_lt_geometric_rpow (by linarith) hb hx hne,
    geometric_lt_euler_arithmetic_rpow (by linarith) hb hx hne,
    (carlsonRReal_euler_strict_bounds_of_one_lt hb hx hne ht).1,
    (carlsonRReal_euler_strict_bounds_of_one_lt hb hx hne ht).2,
    euler_weightedPower_lt_weightedPower (by linarith) hb hx hne⟩

end Carlson
