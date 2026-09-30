/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SlitRelations

/-!
# Further associated-function relations (Carlson's Exercises 5.9-6 to 5.9-9)

Relations between associated `R` functions that Carlson's reduction tables (Section 9.3) use,
in regularized form on the whole slit domain. Regularization `R_t(b; z)/Γ(c)` absorbs Carlson's
factors `c - 1` and the weights `wᵢ = bᵢ/c`.

* Zill's relation (the second relation of Exercise 5.9-6):
  `(c + t - 1)(zᵢ - zⱼ) R_t(b) + zⱼ R_t(b - eᵢ) - zᵢ R_t(b - eⱼ) = 0`.
  The first relation of Exercise 5.9-6 is `Carlson.regCarlsonR_tangent_sub`.
* Exercise 5.9-7: `t R_{t-1}(b) = ∑ bᵢ zᵢ⁻¹ [(c + t) R_t(b + eᵢ) - R_t(b)]` and
  `(t + 1) ∑ bᵢ zᵢ² R_t(b + eᵢ) = (c + t + 1) R_{t+2}(b) - (∑ bᵢ zᵢ) R_{t+1}(b)`.
* Exercises 5.9-8 and 5.9-9: the analogues for three variables of the two-variable relations
  (5.9-24) and (5.9-25).

## Main results

* `Carlson.regCarlsonR_zill`, `Carlson.regCarlsonR_exercise_5_9_7_left`,
  `Carlson.regCarlsonR_exercise_5_9_7_right`, `Carlson.regCarlsonR_three_contiguous`,
  `Carlson.regCarlsonR_three_recurrence`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.9.
-/

open Complex Set Dirichlet
@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- **Zill's relation** (Carlson's Exercise 5.9-6, second relation), regularized:
`(c + t - 1)(zᵢ - zⱼ) R_t(b) + zⱼ R_t(b - eᵢ) - zᵢ R_t(b - eⱼ) = 0`. -/
theorem regCarlsonR_zill (t : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain)
    (i j : ι) :
    ((∑ l, b l) + t - 1) * (z i - z j) * regCarlsonR t b z +
      z j * regCarlsonR t (b - Pi.single i 1) z - z i * regCarlsonR t (b - Pi.single j 1) z =
        0 := by
  rw [regCarlsonR_sub_dirichletUnit t b hz i, regCarlsonR_sub_dirichletUnit t b hz j]
  ring

/-- **Carlson's Exercise 5.9-7, first relation**, regularized:
`t R_{t-1}(b) = ∑ bᵢ zᵢ⁻¹ [(c + t) R_t(b + eᵢ) - R_t(b)]`. -/
theorem regCarlsonR_exercise_5_9_7_left (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    t * regCarlsonR (t - 1) b z =
      ∑ i, b i * (z i)⁻¹ * (((∑ l, b l) + t) * regCarlsonR t (addDirichletUnit b i) z -
        regCarlsonR t b z) := by
  rw [regCarlsonR_eq_sum_addDirichletUnit (t - 1) b hz, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hzi : z i ≠ 0 := slitPlane_ne_zero (hz i)
  have h := regCarlsonR_eq_addDirichletUnit t b hz i
  rw [show ((∑ l, b l) + t) * regCarlsonR t (addDirichletUnit b i) z - regCarlsonR t b z =
    t * z i * regCarlsonR (t - 1) (addDirichletUnit b i) z by rw [h]; ring]
  field_simp

/-- **Carlson's Exercise 5.9-7, second relation**, regularized:
`(t + 1) ∑ bᵢ zᵢ² R_t(b + eᵢ) = (c + t + 1) R_{t+2}(b) - (∑ bᵢ zᵢ) R_{t+1}(b)`. -/
theorem regCarlsonR_exercise_5_9_7_right (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    (t + 1) * ∑ i, b i * z i ^ 2 * regCarlsonR t (addDirichletUnit b i) z =
      ((∑ l, b l) + t + 1) * regCarlsonR (t + 2) b z -
        (∑ i, b i * z i) * regCarlsonR (t + 1) b z := by
  have h6 := regCarlsonR_add_one_eq_sum_mul_addDirichletUnit (t + 1) b hz
  rw [show t + 1 + 1 = t + 2 by ring] at h6
  rw [h6, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := regCarlsonR_eq_addDirichletUnit (t + 1) b hz i
  rw [show t + 1 - 1 = t by ring] at h
  linear_combination (b i * z i) * h

/-- **Carlson's Exercise 5.9-8** (the three-variable analogue of (5.9-24)), regularized:
`t b₀ (z₀ - z₁)(z₀ - z₂) R_{t-1}(b + e₀) =
  t z₁ z₂ R_{t-1}(b) - (∑ bₛ zₛ + t (z₁ + z₂)) R_t(b) + (c + t) R_{t+1}(b)`.
By permutation symmetry the same holds for every permutation of the indices. -/
theorem regCarlsonR_three_contiguous (t : ℂ) (b : Fin 3 → ℂ) {z : Fin 3 → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    t * b 0 * (z 0 - z 1) * (z 0 - z 2) * regCarlsonR (t - 1) (addDirichletUnit b 0) z =
      t * z 1 * z 2 * regCarlsonR (t - 1) b z -
        ((∑ s, b s * z s) + t * (z 1 + z 2)) * regCarlsonR t b z +
        ((∑ s, b s) + t) * regCarlsonR (t + 1) b z := by
  have hA := regCarlsonR_eq_sum_addDirichletUnit (t - 1) b hz
  have hB := regCarlsonR_add_one_eq_sum_mul_addDirichletUnit (t - 1) b hz
  have hC := regCarlsonR_exercise_5_9_7_right (t - 1) b hz
  rw [show t - 1 + 1 = t by ring] at hB hC
  rw [show t - 1 + 2 = t + 1 by ring, show (∑ l, b l) + (t - 1) + 1 = (∑ l, b l) + t by ring]
    at hC
  simp only [Fin.sum_univ_three] at hA hB hC ⊢
  linear_combination hC + t * (z 1 + z 2) * hB - t * z 1 * z 2 * hA

/-- **Carlson's Exercise 5.9-9** (the three-variable analogue of (5.9-25)), regularized:
`(c + t)(c + t + 1) R_{t+2} - (c + t) ∑ (t + 1 + bᵢ) zᵢ R_{t+1}
  + (t + 1) ∑ (c + t - bᵢ) zⱼ zₖ R_t - t (t + 1) z₁ z₂ z₃ R_{t-1} = 0`,
where `{i, j, k} = {0, 1, 2}` in the middle sum. -/
theorem regCarlsonR_three_recurrence (t : ℂ) (b : Fin 3 → ℂ) {z : Fin 3 → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    ((∑ s, b s) + t) * ((∑ s, b s) + t + 1) * regCarlsonR (t + 2) b z -
      ((∑ s, b s) + t) * (∑ s, (t + 1 + b s) * z s) * regCarlsonR (t + 1) b z +
      (t + 1) * (((∑ s, b s) + t - b 0) * z 1 * z 2 + ((∑ s, b s) + t - b 1) * z 0 * z 2 +
        ((∑ s, b s) + t - b 2) * z 0 * z 1) * regCarlsonR t b z -
      t * (t + 1) * z 0 * z 1 * z 2 * regCarlsonR (t - 1) b z = 0 := by
  set c := ∑ s, b s with hc
  -- `Xₛ = bₛ R_{t-1}(b + eₛ)` and `Yₛ = bₛ R_t(b + eₛ)`
  have hA := regCarlsonR_eq_sum_addDirichletUnit (t - 1) b hz
  have hB := regCarlsonR_add_one_eq_sum_mul_addDirichletUnit (t - 1) b hz
  have hC := regCarlsonR_exercise_5_9_7_right (t - 1) b hz
  have hC' := regCarlsonR_exercise_5_9_7_right t b hz
  rw [show t - 1 + 1 = t by ring] at hB hC
  rw [show t - 1 + 2 = t + 1 by ring, show c + (t - 1) + 1 = c + t by ring] at hC
  have hY : ∀ s, b s * regCarlsonR t b z =
      (c + t) * (b s * regCarlsonR t (addDirichletUnit b s) z) -
        t * z s * (b s * regCarlsonR (t - 1) (addDirichletUnit b s) z) := by
    intro s
    rw [regCarlsonR_eq_addDirichletUnit t b hz s]
    ring
  have hY0 := hY 0
  have hY1 := hY 1
  have hY2 := hY 2
  simp only [Fin.sum_univ_three] at hA hB hC hC' hc ⊢
  set X0 := b 0 * regCarlsonR (t - 1) (addDirichletUnit b 0) z
  set X1 := b 1 * regCarlsonR (t - 1) (addDirichletUnit b 1) z
  set X2 := b 2 * regCarlsonR (t - 1) (addDirichletUnit b 2) z
  set Y0 := b 0 * regCarlsonR t (addDirichletUnit b 0) z
  set Y1 := b 1 * regCarlsonR t (addDirichletUnit b 1) z
  set Y2 := b 2 * regCarlsonR t (addDirichletUnit b 2) z
  -- rewrite the hypotheses in terms of the `X` and `Y`
  have hA' : regCarlsonR (t - 1) b z = X0 + X1 + X2 := by rw [hA]
  have hB' : regCarlsonR t b z = z 0 * X0 + z 1 * X1 + z 2 * X2 := by
    rw [hB]; simp only [X0, X1, X2]; ring
  have hC2 : t * (z 0 ^ 2 * X0 + z 1 ^ 2 * X1 + z 2 ^ 2 * X2) =
      (c + t) * regCarlsonR (t + 1) b z -
        (b 0 * z 0 + b 1 * z 1 + b 2 * z 2) * regCarlsonR t b z := by
    rw [← hC]; simp only [X0, X1, X2]; ring
  have hC2' : (t + 1) * (z 0 ^ 2 * Y0 + z 1 ^ 2 * Y1 + z 2 ^ 2 * Y2) =
      (c + t + 1) * regCarlsonR (t + 2) b z -
        (b 0 * z 0 + b 1 * z 1 + b 2 * z 2) * regCarlsonR (t + 1) b z := by
    rw [hc, ← hC']; simp only [Y0, Y1, Y2]; ring
  linear_combination -(c + t) * hC2' - (t + 1) * z 0 ^ 2 * hY0 - (t + 1) * z 1 ^ 2 * hY1 -
    (t + 1) * z 2 ^ 2 * hY2 + (t + 1) * (z 0 + z 1 + z 2) * hC2 +
    t * (t + 1) * (z 0 * z 1 + z 0 * z 2 + z 1 * z 2) * hB' -
    t * (t + 1) * (z 0 * z 1 * z 2) * hA' +
    (t + 1) * (z 0 * z 1 + z 0 * z 2 + z 1 * z 2) * regCarlsonR t b z * hc

end Carlson
