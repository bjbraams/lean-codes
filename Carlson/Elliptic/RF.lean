/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Aggregation
public import Carlson.TwoVariable.QuadraticHybrid
public import Carlson.R.SingleIntegral.PositiveRay
public import Carlson.R.SmallVariableContinuation

/-!
# Carlson's symmetric elliptic integral of the first kind

Carlson's (8.2-6) introduces `R_F(x, y, z) = R_{-1/2}(1/2, 1/2, 1/2; x, y, z)`, which is
`(1/2) ∫₀^∞ [(t + x)(t + y)(t + z)]^{-1/2} dt` (8.2-5) and reduces to `R_C` when two arguments
coincide (8.2-13). The symmetry and the reduction come from equal-node aggregation on the slit
plane.

## Main definitions

* `Carlson.carlsonRF`: `R_F`.

## Main results

* `Carlson.carlsonRF_perm`, `Carlson.carlsonRF_comm_left`, `Carlson.carlsonRF_comm_right`:
  symmetry.
* `Carlson.carlsonRF_self_right`: (8.2-13), `R_F(x, y, y) = R_C(x, y)`.
* `Carlson.carlsonRF_self`: `R_F(x, x, x) = x^{-1/2}`.
* `Carlson.carlsonRF_eq_integral`: the integral (8.2-5).
* `Carlson.tendsto_carlsonRF_zero`: (8.3-17), `R_F(x, y, 0) = (π/2) R_K(x, y)`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.2.
-/

open Complex Set Filter Dirichlet
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

/-- Carlson's symmetric elliptic integral of the first kind (8.2-6),
`R_F(x, y, z) = R_{-1/2}(1/2, 1/2, 1/2; x, y, z)`. -/
def carlsonRF (x y z : ℂ) : ℂ :=
  carlsonR (-1 / 2) (fun _ : Fin 3 => 1 / 2) ![x, y, z]

/-- `R_F` in terms of the regularized `R` function. -/
theorem carlsonRF_eq (x y z : ℂ) :
    carlsonRF x y z = Gamma (3 / 2) * regCarlsonR (-1 / 2) (fun _ : Fin 3 => 1 / 2) ![x, y, z] := by
  unfold carlsonRF carlsonR
  congr 2
  simp; norm_num

/-- `R_F` is symmetric under every permutation of its arguments. -/
theorem carlsonRF_perm (σ : Equiv.Perm (Fin 3)) {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    carlsonR (-1 / 2) (fun _ : Fin 3 => 1 / 2) (![x, y, z] ∘ σ) = carlsonRF x y z := by
  have hs : ![x, y, z] ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  unfold carlsonRF carlsonR
  rw [regCarlsonR_aggregate_of_slit σ.surjective _ hs]
  congr 2
  funext k
  classical
  rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
  have : (Finset.univ.filter fun x => σ x = k) = {σ.symm k} := by
    ext j; simp [Equiv.eq_symm_apply]
  rw [this, Finset.sum_singleton]

/-- `R_F` is symmetric in its first two arguments. -/
theorem carlsonRF_comm_left {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : carlsonRF y x z = carlsonRF x y z := by
  rw [← carlsonRF_perm (Equiv.swap 0 1) hx hy hz]
  unfold carlsonRF; congr 1; funext i; fin_cases i <;> rfl

/-- `R_F` is symmetric in its last two arguments. -/
theorem carlsonRF_comm_right {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : carlsonRF x z y = carlsonRF x y z := by
  rw [← carlsonRF_perm (Equiv.swap 1 2) hx hy hz]
  unfold carlsonRF; congr 1; funext i; fin_cases i <;> rfl

/-- **Carlson's (8.2-13)**: `R_F(x, y, y) = R_C(x, y)`, by merging the equal nodes. -/
theorem carlsonRF_self_right {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    carlsonRF x y y = TwoVariable.carlsonRC x y := by
  have hs : TwoVariable.pair x y ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hx
    · exact hy
  have hq : Function.Surjective (![0, 1, 1] : Fin 3 → Fin 2) := by
    intro k; fin_cases k
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  unfold carlsonRF TwoVariable.carlsonRC carlsonR
  have hcomp : (![x, y, y] : Fin 3 → ℂ) = TwoVariable.pair x y ∘ ![0, 1, 1] := by
    funext i; fin_cases i <;> rfl
  rw [hcomp, regCarlsonR_aggregate_of_slit hq _ hs]
  have hagg : stdSimplexAggregate (![0, 1, 1] : Fin 3 → Fin 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) =
      TwoVariable.pair (1 / 2) 1 := by
    classical
    funext k
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    fin_cases k
    · simp [TwoVariable.pair]; decide
    · simp [TwoVariable.pair]
      have : (Finset.univ.filter fun x : Fin 3 => (![0, 1, 1] : Fin 3 → Fin 2) x = 1).card = 2 := by
        decide
      rw [this]; norm_num
  rw [hagg]
  congr 1
  simp; norm_num

/-- `R_F(x, x, x) = x^{-1/2}` for `re x > 0`. -/
theorem carlsonRF_self {x : ℂ} (hx : 0 < x.re) : carlsonRF x x x = x ^ (-1 / 2 : ℂ) := by
  have hb : (fun _ : Fin 3 => (1 / 2 : ℂ)) ∈ mvBetaConvergent := fun _ => by norm_num
  have hxx : (![x, x, x] : Fin 3 → ℂ) = fun _ => x := by funext i; fin_cases i <;> rfl
  have hdom : (![x, x, x] : Fin 3 → ℂ) ∈ carlsonRVariableDomain := by
    rw [hxx]; exact fun _ => hx
  have hc : 0 < (∑ _i : Fin 3, (1 / 2 : ℂ)).re := by simp
  unfold carlsonRF carlsonR
  rw [regCarlsonR_eq_regCarlsonRIntegral _ hb hdom, regCarlsonRIntegral, hxx,
    Dirichlet.regCarlsonDirichletAverage_const _ _ hb,
    mul_div_cancel₀ _ (Gamma_ne_zero_of_re_pos hc)]

/-- **Carlson's (8.2-5)**: for slit-plane nodes,
`R_F(x, y, z) = (1/2) ∫₀^∞ (t + x)^{-1/2} (t + y)^{-1/2} (t + z)^{-1/2} dt`. -/
theorem carlsonRF_eq_integral {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    carlsonRF x y z = (1 / 2) * ∫ t in Ioi (0 : ℝ),
      (x + t) ^ (-1 / 2 : ℂ) * (y + t) ^ (-1 / 2 : ℂ) * (z + t) ^ (-1 / 2 : ℂ) := by
  have hs : ![x, y, z] ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> assumption
  have h := carlsonRPositiveRayIntegral_eq_gamma_mul_regCarlsonR (a := 1) (a' := 1 / 2)
    (b := fun _ : Fin 3 => (1 / 2 : ℂ)) (by norm_num) (by norm_num)
    (by simp; norm_num) hs
  unfold carlsonRPositiveRayIntegral at h
  simp only [sub_self, cpow_zero, one_mul, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Gamma_one,
    show -(1 / 2 : ℂ) = -1 / 2 by ring] at h
  rw [h, carlsonRF_eq, show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  ring

open TwoVariable in
/-- **Carlson's (8.3-17)**: `R_F(x, y, 0) = (π/2) R_K(x, y)`, as the limit when the third
argument tends to `0` through the right half-plane, for `re x, re y > 0`. -/
theorem tendsto_carlsonRF_zero {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Tendsto (fun z => carlsonRF x y z) (𝓝[{z : ℂ | 0 < z.re}] 0)
      (𝓝 ((π / 2 : ℂ) * carlsonRK x y)) := by
  have hz : (![x, y, 1] : Fin 3 → ℂ) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · exact hx
    · exact hy
    · simp [carlsonRightHalfPlane]
  have H := tendsto_regCarlsonR_update_zero (ι := Fin 3) 2 (a := 1 / 2) (a' := 1)
    (b := fun _ => 1 / 2) (z := ![x, y, 1]) (by simp; norm_num) (by norm_num) hz ⟨0, by decide⟩
    (E := ↥{z : ℂ | 0 < z.re}) (l := comap Subtype.val (𝓝 0)) (w := Subtype.val)
    (fun v => v.2) tendsto_comap
  -- the erased function is `R_K`
  set q : {j : Fin 3 // j ≠ 2} → Fin 2 := fun j => if j.1 = 0 then 0 else 1
  have hq : Function.Surjective q := by
    intro k; fin_cases k
    · exact ⟨⟨0, by decide⟩, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl⟩
  have hs : pair x y ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact mem_slitPlane_iff.mpr (Or.inl hx)
    · exact mem_slitPlane_iff.mpr (Or.inl hy)
  have hcomp : eraseCarlsonVariable 2 (![x, y, 1] : Fin 3 → ℂ) = pair x y ∘ q := by
    funext j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · rfl
    · rfl
    · exact absurd rfl hj
  have hagg : stdSimplexAggregate q (eraseCarlsonParameter 2 (fun _ : Fin 3 => (1 / 2 : ℂ))) =
      pair (1 / 2) (1 / 2) := by
    funext k
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    fin_cases k
    · have : (Finset.univ.filter fun j : {j : Fin 3 // j ≠ 2} => q j = 0) = {⟨0, by decide⟩} := by
        decide
      show (Finset.univ.filter fun j => q j = 0).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
    · have : (Finset.univ.filter fun j : {j : Fin 3 // j ≠ 2} => q j = 1) = {⟨1, by decide⟩} := by
        decide
      show (Finset.univ.filter fun j => q j = 1).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
  rw [hcomp, regCarlsonR_aggregate_of_slit hq _ hs, hagg] at H
  have hG : Gamma (3 / 2 : ℂ) * Gamma (1 / 2) = π / 2 := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num),
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal,
      Real.Gamma_one_half_eq]
    rw [mul_assoc, ← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
    push_cast; ring
  rw [nhdsWithin, ← Filter.subtype_coe_map_comap, tendsto_map'_iff]
  have H' := H.const_mul (Gamma (3 / 2))
  have hval : Gamma (3 / 2) * (Gamma (1 - 1 / 2) * ((Gamma 1)⁻¹ *
      regCarlsonR (-(1 / 2)) (pair (1 / 2) (1 / 2)) (pair x y))) = (π / 2 : ℂ) * carlsonRK x y := by
    unfold TwoVariable.carlsonRK carlsonR
    rw [sum_pair, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Gamma_one, inv_one, one_mul, one_mul,
      show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, ← mul_assoc, hG, show (-(1 / 2) : ℂ) = -1 / 2 by
        ring]
  rw [hval] at H'
  refine H'.congr fun v => ?_
  simp only [Function.comp_apply]
  rw [carlsonRF_eq, show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  congr 2
  funext i; fin_cases i <;> rfl

end Carlson
