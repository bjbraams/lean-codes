/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Inversion
public import Carlson.Aggregation

/-!
# Symmetric standard elliptic integrals (Carlson §9.2)

Carlson's standard functions (9.2-1), (9.2-2),

* `R_G(x, y, z) = R_{1/2}(1/2, 1/2, 1/2; x, y, z)`,
* `R_H(x, y, z, ρ) = R_{-1/2}(1/2, 1/2, 1/2, 1; x, y, z, ρ)`,
* `R_E(x, y) = R_{1/2}(1/2, 1/2; x, y)`,
* `R_L(x, y, ρ) = R_{-1/2}(1/2, 1/2, 1; x, y, ρ)`,

together with `R_F` (module `Carlson.Elliptic.RF`), `R_K` and `R_C`, and Legendre's integrals
`F(φ, k)`, `E(φ, k)`, `Π(φ, k, α²)` and `K(k) = F(π/2, k)`, `E(k) = E(π/2, k)`.

The module proves the permutation symmetries, the values (9.2-3) of `R_G` and `R_H` when one
variable tends to `0`, and Legendre's integrals of the first and second kinds as symmetric
standard functions (9.2-11), (9.3-2), with `K(k) = (π/2) R_K(1 - k², 1)` (9.2-14).

## Main results

* `Carlson.carlsonRG`, `Carlson.carlsonRH`, `Carlson.carlsonRE`, `Carlson.carlsonRL`: the
  standard functions.
* `Carlson.carlsonRG_perm`, `Carlson.carlsonRH_comm_left`, `Carlson.carlsonRH_comm_right`,
  `Carlson.carlsonRE_comm`, `Carlson.carlsonRL_comm`: symmetries.
* `Carlson.tendsto_carlsonRG_zero`, `Carlson.tendsto_carlsonRH_zero`: (9.2-3).
* `Carlson.legendreF_eq`, `Carlson.legendreE_eq`, `Carlson.legendreK_eq`: (9.2-11), (9.3-2),
  (9.2-14).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §9.2.
-/

open Complex Set Filter MeasureTheory Dirichlet
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

open TwoVariable (pair sum_pair carlsonRK carlsonRC)

/-! ### Definitions -/

/-- Carlson's symmetric elliptic integral of the second kind (9.2-1),
`R_G(x, y, z) = R_{1/2}(1/2, 1/2, 1/2; x, y, z)`. -/
def carlsonRG (x y z : ℂ) : ℂ :=
  carlsonR (1 / 2) (fun _ : Fin 3 => 1 / 2) ![x, y, z]

/-- Carlson's symmetric elliptic integral of the third kind (9.2-1),
`R_H(x, y, z, ρ) = R_{-1/2}(1/2, 1/2, 1/2, 1; x, y, z, ρ)`. -/
def carlsonRH (x y z ρ : ℂ) : ℂ :=
  carlsonR (-1 / 2) ![1 / 2, 1 / 2, 1 / 2, 1] ![x, y, z, ρ]

/-- The complete elliptic integral of the second kind (9.2-2),
`R_E(x, y) = R_{1/2}(1/2, 1/2; x, y)`. -/
def carlsonRE (x y : ℂ) : ℂ :=
  carlsonR (1 / 2) (pair (1 / 2) (1 / 2)) (pair x y)

/-- The complete elliptic integral of the third kind (9.2-2),
`R_L(x, y, ρ) = R_{-1/2}(1/2, 1/2, 1; x, y, ρ)`. -/
def carlsonRL (x y ρ : ℂ) : ℂ :=
  carlsonR (-1 / 2) ![1 / 2, 1 / 2, 1] ![x, y, ρ]

/-- Legendre's incomplete elliptic integral of the first kind,
`F(φ, k) = ∫₀^φ (1 - k² sin² θ)^{-1/2} dθ`. -/
def legendreF (φ k : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * Real.sin θ ^ 2) ^ (-1 / 2 : ℝ)

/-- Legendre's incomplete elliptic integral of the second kind,
`E(φ, k) = ∫₀^φ (1 - k² sin² θ)^{1/2} dθ`. -/
def legendreE (φ k : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * Real.sin θ ^ 2) ^ (1 / 2 : ℝ)

/-- Legendre's incomplete elliptic integral of the third kind,
`Π(φ, k, α²) = ∫₀^φ (1 - α² sin² θ)^{-1} (1 - k² sin² θ)^{-1/2} dθ`. -/
def legendrePi (φ k α2 : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ, (1 - α2 * Real.sin θ ^ 2)⁻¹ * (1 - k ^ 2 * Real.sin θ ^ 2) ^ (-1 / 2 : ℝ)

/-- Legendre's complete integral of the first kind, `K(k) = F(π/2, k)`. -/
def legendreK (k : ℝ) : ℝ := legendreF (π / 2) k

/-- Legendre's complete integral of the second kind, `E(k) = E(π/2, k)`. -/
def legendreEc (k : ℝ) : ℝ := legendreE (π / 2) k

/-! ### Symmetries -/

private theorem slit3 {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : (![x, y, z] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
  intro i; fin_cases i <;> assumption

/-- `R_G` is symmetric in its three variables. -/
theorem carlsonRG_perm (σ : Equiv.Perm (Fin 3)) {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    carlsonR (1 / 2) (fun _ : Fin 3 => 1 / 2) (![x, y, z] ∘ σ) = carlsonRG x y z := by
  unfold carlsonRG carlsonR
  rw [regCarlsonR_comp_perm σ _ (slit3 hx hy hz)]
  rfl

theorem carlsonRG_comm_left {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : carlsonRG y x z = carlsonRG x y z := by
  rw [← carlsonRG_perm (Equiv.swap 0 1) hx hy hz, carlsonRG]
  congr 1
  funext i; fin_cases i <;> rfl

theorem carlsonRG_comm_right {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) : carlsonRG x z y = carlsonRG x y z := by
  rw [← carlsonRG_perm (Equiv.swap 1 2) hx hy hz, carlsonRG]
  congr 1
  funext i; fin_cases i <;> rfl

private theorem slit4 {x y z ρ : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hρ : ρ ∈ slitPlane) :
    (![x, y, z, ρ] : Fin 4 → ℂ) ∈ carlsonRSlitDomain := by
  intro i; fin_cases i <;> assumption

/-- `R_H` is symmetric in its first two variables. -/
theorem carlsonRH_comm_left {x y z ρ : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hρ : ρ ∈ slitPlane) : carlsonRH y x z ρ = carlsonRH x y z ρ := by
  have h := regCarlsonR_comp_perm (Equiv.swap (0 : Fin 4) 1) (-1 / 2) (slit4 hx hy hz hρ)
    ![1 / 2, 1 / 2, 1 / 2, 1]
  unfold carlsonRH carlsonR
  have hb : (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ) ∘ (Equiv.swap (0 : Fin 4) 1).symm =
      ![1 / 2, 1 / 2, 1 / 2, 1] := by
    funext i; fin_cases i <;> rfl
  have hz' : (![x, y, z, ρ] : Fin 4 → ℂ) ∘ Equiv.swap (0 : Fin 4) 1 = ![y, x, z, ρ] := by
    funext i; fin_cases i <;> rfl
  rw [hb, hz'] at h
  rw [h]

/-- `R_H` is symmetric in its second and third variables. -/
theorem carlsonRH_comm_right {x y z ρ : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hρ : ρ ∈ slitPlane) : carlsonRH x z y ρ = carlsonRH x y z ρ := by
  have h := regCarlsonR_comp_perm (Equiv.swap (1 : Fin 4) 2) (-1 / 2) (slit4 hx hy hz hρ)
    ![1 / 2, 1 / 2, 1 / 2, 1]
  unfold carlsonRH carlsonR
  have hb : (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ) ∘ (Equiv.swap (1 : Fin 4) 2).symm =
      ![1 / 2, 1 / 2, 1 / 2, 1] := by
    funext i; fin_cases i <;> rfl
  have hz' : (![x, y, z, ρ] : Fin 4 → ℂ) ∘ Equiv.swap (1 : Fin 4) 2 = ![x, z, y, ρ] := by
    funext i; fin_cases i <;> rfl
  rw [hb, hz'] at h
  rw [h]

/-- `R_E` is symmetric. -/
theorem carlsonRE_comm {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    carlsonRE y x = carlsonRE x y := by
  have hs : pair x y ∈ carlsonRSlitDomain := by intro i; fin_cases i <;> assumption
  have h := regCarlsonR_comp_perm (Equiv.swap (0 : Fin 2) 1) (1 / 2) hs (pair (1 / 2) (1 / 2))
  unfold carlsonRE carlsonR
  have hb : pair (1 / 2 : ℂ) (1 / 2) ∘ (Equiv.swap (0 : Fin 2) 1).symm = pair (1 / 2) (1 / 2) := by
    funext i; fin_cases i <;> rfl
  have hz' : pair x y ∘ Equiv.swap (0 : Fin 2) 1 = pair y x := by
    funext i; fin_cases i <;> rfl
  rw [hb, hz'] at h
  rw [h]

/-- `R_L` is symmetric in its first two variables. -/
theorem carlsonRL_comm {x y ρ : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) : carlsonRL y x ρ = carlsonRL x y ρ := by
  have h := regCarlsonR_comp_perm (Equiv.swap (0 : Fin 3) 1) (-1 / 2) (slit3 hx hy hρ)
    ![1 / 2, 1 / 2, 1]
  unfold carlsonRL carlsonR
  have hb : (![1 / 2, 1 / 2, 1] : Fin 3 → ℂ) ∘ (Equiv.swap (0 : Fin 3) 1).symm =
      ![1 / 2, 1 / 2, 1] := by
    funext i; fin_cases i <;> rfl
  have hz' : (![x, y, ρ] : Fin 3 → ℂ) ∘ Equiv.swap (0 : Fin 3) 1 = ![y, x, ρ] := by
    funext i; fin_cases i <;> rfl
  rw [hb, hz'] at h
  rw [h]

/-! ### One variable tending to zero (9.2-3) -/

private theorem Gamma_three_halves_sq : Gamma (3 / 2 : ℂ) * Gamma (3 / 2) = π / 4 := by
  rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num),
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal,
    Real.Gamma_one_half_eq]
  have : ((Real.sqrt π : ℝ) : ℂ) * (Real.sqrt π : ℝ) = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  push_cast
  linear_combination (1 / 4 : ℂ) * this

private theorem Gamma_two' : Gamma (2 : ℂ) = 1 := by
  rw [show (2 : ℂ) = 1 + 1 by norm_num, Gamma_add_one _ one_ne_zero, Gamma_one, mul_one]

/-- **Carlson's (9.2-3) for `R_G`**: `R_G(x, y, z) → (π/4) R_E(x, y)` as `z → 0` in the right
half-plane. -/
theorem tendsto_carlsonRG_zero {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Tendsto (fun z => carlsonRG x y z) (𝓝[{z : ℂ | 0 < z.re}] 0)
      (𝓝 ((π / 4 : ℂ) * carlsonRE x y)) := by
  have hz : (![x, y, 1] : Fin 3 → ℂ) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · exact hx
    · exact hy
    · simp [carlsonRightHalfPlane]
  have H := tendsto_regCarlsonR_update_zero (ι := Fin 3) 2 (a := -(1 / 2)) (a' := 2)
    (b := fun _ => 1 / 2) (z := ![x, y, 1]) (by simp; norm_num) (by norm_num) hz ⟨0, by decide⟩
    (E := ↥{z : ℂ | 0 < z.re}) (l := comap Subtype.val (𝓝 0)) (w := Subtype.val)
    (fun v => v.2) tendsto_comap
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
  rw [nhdsWithin, ← Filter.subtype_coe_map_comap, tendsto_map'_iff]
  have H' := H.const_mul (Gamma (3 / 2))
  have hval : Gamma (3 / 2) * (Gamma (2 - 1 / 2) * ((Gamma 2)⁻¹ *
      regCarlsonR (-(-(1 / 2))) (pair (1 / 2) (1 / 2)) (pair x y))) =
        (π / 4 : ℂ) * carlsonRE x y := by
    unfold carlsonRE carlsonR
    rw [sum_pair, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Gamma_one, Gamma_two', inv_one,
      one_mul, one_mul, show (2 : ℂ) - 1 / 2 = 3 / 2 by norm_num, ← mul_assoc,
      Gamma_three_halves_sq, neg_neg]
  rw [hval] at H'
  refine H'.congr fun v => ?_
  simp only [Function.comp_apply]
  unfold carlsonRG carlsonR
  rw [show (∑ _i : Fin 3, (1 / 2 : ℂ)) = 3 / 2 by simp; norm_num, neg_neg]
  congr 2
  funext i; fin_cases i <;> rfl

/-- **Carlson's (9.2-3) for `R_H`**: `R_H(x, y, z, ρ) → (3π/8) R_L(x, y, ρ)` as `z → 0` in the
right half-plane. -/
theorem tendsto_carlsonRH_zero {x y ρ : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (hρ : 0 < ρ.re) :
    Tendsto (fun z => carlsonRH x y z ρ) (𝓝[{z : ℂ | 0 < z.re}] 0)
      (𝓝 ((3 * π / 8 : ℂ) * carlsonRL x y ρ)) := by
  have hz : (![x, y, 1, ρ] : Fin 4 → ℂ) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · exact hx
    · exact hy
    · simp [carlsonRightHalfPlane]
    · exact hρ
  have H := tendsto_regCarlsonR_update_zero (ι := Fin 4) 2 (a := 1 / 2) (a' := 2)
    (b := ![1 / 2, 1 / 2, 1 / 2, 1]) (z := ![x, y, 1, ρ])
    (by simp [Fin.sum_univ_four]; norm_num) (by simp; norm_num) hz ⟨0, by decide⟩
    (E := ↥{z : ℂ | 0 < z.re}) (l := comap Subtype.val (𝓝 0)) (w := Subtype.val)
    (fun v => v.2) tendsto_comap
  set q : {j : Fin 4 // j ≠ 2} → Fin 3 := fun j => if j.1 = 0 then 0 else if j.1 = 1 then 1 else 2
  have hq : Function.Surjective q := by
    intro k; fin_cases k
    · exact ⟨⟨0, by decide⟩, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl⟩
    · exact ⟨⟨3, by decide⟩, rfl⟩
  have hs : (![x, y, ρ] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact mem_slitPlane_iff.mpr (Or.inl hx)
    · exact mem_slitPlane_iff.mpr (Or.inl hy)
    · exact mem_slitPlane_iff.mpr (Or.inl hρ)
  have hcomp : eraseCarlsonVariable 2 (![x, y, 1, ρ] : Fin 4 → ℂ) = ![x, y, ρ] ∘ q := by
    funext j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · rfl
    · rfl
    · exact absurd rfl hj
    · rfl
  have hagg : stdSimplexAggregate q
      (eraseCarlsonParameter 2 (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ)) = ![1 / 2, 1 / 2, 1] := by
    funext k
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    fin_cases k
    · have : (Finset.univ.filter fun j : {j : Fin 4 // j ≠ 2} => q j = 0) = {⟨0, by decide⟩} := by
        decide
      show (Finset.univ.filter fun j => q j = 0).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
    · have : (Finset.univ.filter fun j : {j : Fin 4 // j ≠ 2} => q j = 1) = {⟨1, by decide⟩} := by
        decide
      show (Finset.univ.filter fun j => q j = 1).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
    · have : (Finset.univ.filter fun j : {j : Fin 4 // j ≠ 2} => q j = 2) = {⟨3, by decide⟩} := by
        decide
      show (Finset.univ.filter fun j => q j = 2).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
  rw [hcomp, regCarlsonR_aggregate_of_slit hq _ hs, hagg] at H
  rw [nhdsWithin, ← Filter.subtype_coe_map_comap, tendsto_map'_iff]
  have H' := H.const_mul (Gamma (5 / 2))
  have hval : Gamma (5 / 2) * (Gamma (2 - (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ) 2) *
      ((Gamma 2)⁻¹ * regCarlsonR (-(1 / 2)) ![1 / 2, 1 / 2, 1] ![x, y, ρ])) =
        (3 * π / 8 : ℂ) * carlsonRL x y ρ := by
    unfold carlsonRL carlsonR
    have hs3 : (∑ i, (![1 / 2, 1 / 2, 1] : Fin 3 → ℂ) i) = 2 := by
      simp [Fin.sum_univ_three]; norm_num
    rw [hs3, Gamma_two', inv_one, one_mul, show (-(1 / 2) : ℂ) = -1 / 2 by ring]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [show (2 : ℂ) - 1 / 2 = 3 / 2 by norm_num, show (5 / 2 : ℂ) = 3 / 2 + 1 by norm_num,
      Gamma_add_one _ (by norm_num)]
    have := Gamma_three_halves_sq
    linear_combination (3 / 2 : ℂ) * regCarlsonR (-1 / 2) ![1 / 2, 1 / 2, 1] ![x, y, ρ] * this
  rw [hval] at H'
  refine H'.congr fun v => ?_
  simp only [Function.comp_apply]
  unfold carlsonRH carlsonR
  rw [show (∑ i, (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ) i) = 5 / 2 by
    simp [Fin.sum_univ_four]; norm_num, show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  congr 2
  funext i; fin_cases i <;> rfl

/-! ### Legendre's integrals -/

/-- The substitution `t = sin θ` on `(0, φ)`, `0 < φ ≤ π/2`. -/
theorem integral_Ioo_comp_sin {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) (g : ℝ → ℝ) :
    ∫ t in Ioo (0 : ℝ) (Real.sin φ), g t = ∫ θ in Ioo (0 : ℝ) φ, Real.cos θ * g (Real.sin θ) := by
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) φ, HasDerivWithinAt Real.sin (Real.cos θ) (Ioo 0 φ) θ :=
    fun θ _ => (Real.hasDerivAt_sin θ).hasDerivWithinAt
  have hsub : Ioo (0 : ℝ) φ ⊆ Icc (-(π / 2)) (π / 2) := fun θ hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hinj : InjOn Real.sin (Ioo 0 φ) := Real.injOn_sin.mono hsub
  have himg : Real.sin '' Ioo 0 φ = Ioo 0 (Real.sin φ) := by
    ext t; constructor
    · rintro ⟨θ, hθ, rfl⟩
      exact ⟨Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]),
        Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hθ.1, Real.pi_pos]) h1 hθ.2⟩
    · rintro ⟨ht0, htφ⟩
      have hsφ : Real.sin φ ≤ 1 := Real.sin_le_one φ
      refine ⟨Real.arcsin t, ⟨Real.arcsin_pos.mpr ht0, ?_⟩, Real.sin_arcsin (by linarith)
        (by linarith)⟩
      have := Real.arcsin_lt_arcsin (by linarith) htφ hsφ
      rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) h1] at this
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  rw [abs_of_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩),
    smul_eq_mul]

private theorem cos_mul_rpow_neg_half {θ : ℝ} (hc : 0 < Real.cos θ) :
    Real.cos θ * (1 - Real.sin θ ^ 2) ^ (-1 / 2 : ℝ) = 1 := by
  rw [← Real.cos_sq', show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (sq_nonneg _),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hc.le, mul_inv_cancel₀ hc.ne']

private theorem integral_legendre_eq {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 2) (f : ℝ → ℝ) :
    ∫ θ in (0 : ℝ)..φ, f (Real.sin θ) =
      ∫ t in Ioo (0 : ℝ) (Real.sin φ), (1 - t ^ 2) ^ (-1 / 2 : ℝ) * f t := by
  rw [integral_Ioo_comp_sin h0 h1, intervalIntegral.integral_of_le h0.le,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    (show θ ∈ Ioo (-(π / 2)) (π / 2) from ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  rw [← mul_assoc, cos_mul_rpow_neg_half hc, one_mul]

/-- **Carlson's (9.2-11), (9.3-2), first kind**: for `0 < φ < π/2` and `k² < 1`,
`F(φ, k) = sin φ R_F(cos² φ, 1 - k² sin² φ, 1)`. -/
theorem legendreF_eq {φ k : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) (hk : k ^ 2 < 1) :
    (legendreF φ k : ℂ) = Real.sin φ *
      carlsonRF ((Real.cos φ ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1 := by
  have hs0 : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hs1 : Real.sin φ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl h1
  have h := integral_legendre_eq h0 h1.le (fun t => (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ))
  unfold legendreF
  rw [h, Real.cos_sq', ← integral_Ioo_rsqrt_sn_incomplete hk hs0 hs1]
  refine congrArg ofReal (setIntegral_congr_fun measurableSet_Ioo
    fun t (ht : t ∈ Ioo 0 (Real.sin φ)) => ?_)
  have h1t : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have h2t : 0 ≤ 1 - k ^ 2 * t ^ 2 := by nlinarith [ht.1, ht.2, sq_nonneg k, sq_nonneg t]
  rw [Real.mul_rpow h1t h2t]

/-- **Carlson's (9.2-14), first kind**: `K(k) = (π/2) R_K(1 - k², 1)` for `0 < k < 1`. -/
theorem legendreK_eq {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    (legendreK k : ℂ) = π / 2 * carlsonRK (1 - k ^ 2 : ℝ) 1 := by
  rw [← snK_eq hk0 hk1, legendreK, legendreF,
    integral_legendre_eq (by positivity) le_rfl (fun t => (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ)),
    Real.sin_pi_div_two, snK]
  refine congrArg ofReal (setIntegral_congr_fun measurableSet_Ioo
    fun t (ht : t ∈ Ioo (0 : ℝ) 1) => ?_)
  have h1t : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have h2t : 0 ≤ 1 - k ^ 2 * t ^ 2 := by nlinarith [ht.1, ht.2, sq_nonneg k, sq_nonneg t]
  rw [Real.mul_rpow h1t h2t]

/-- The incomplete integral of the second kind as an `R` function:
`∫₀^y (1 - t²)^{-1/2} (1 - k² t²)^{1/2} dt = y R_{-1/2}(-1/2, 1/2, 3/2; 1 - k² y², 1 - y², 1)`. -/
theorem integral_Ioo_sn_second {k y : ℝ} (hk : k ^ 2 < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    ((∫ t in Ioo (0 : ℝ) y, (1 - t ^ 2) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ) : ℝ) :
        ℂ) =
      y * carlsonR (-1 / 2) ![-1 / 2, 1 / 2, 3 / 2]
        ![((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ), ((1 - y ^ 2 : ℝ) : ℂ), 1] := by
  set g : ℝ → ℝ := fun t => (1 - t ^ 2) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ)
  set φ : ℝ → ℝ := fun s => y * Real.sqrt s
  set N : Fin 3 → ℂ := ![((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ), ((1 - y ^ 2 : ℝ) : ℂ), 1]
  set B : Fin 3 → ℂ := ![-1 / 2, 1 / 2, 3 / 2]
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt φ (y * (1 / (2 * Real.sqrt s)))
      (Ioo 0 1) s := fun s hs =>
    ((Real.hasDerivAt_sqrt hs.1.ne').const_mul y).hasDerivWithinAt
  have hinj : InjOn φ (Ioo 0 1) := by
    intro a ha b hb hab
    have := mul_left_cancel₀ hy0.ne' hab
    rwa [Real.sqrt_inj ha.1.le hb.1.le] at this
  have himg : φ '' Ioo 0 1 = Ioo 0 y := by
    ext t; constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨mul_pos hy0 (Real.sqrt_pos.mpr hs.1), ?_⟩
      have : Real.sqrt s < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hs.2
      show y * Real.sqrt s < y
      nlinarith
    · rintro ⟨ht0, hty⟩
      refine ⟨(t / y) ^ 2, ⟨by positivity, ?_⟩, ?_⟩
      · rw [sq_lt_one_iff_abs_lt_one, abs_of_pos (by positivity), div_lt_one hy0]; exact hty
      · show y * Real.sqrt ((t / y) ^ 2) = t
        rw [Real.sqrt_sq (by positivity)]; field_simp
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  rw [himg] at hsub
  rw [hsub]
  have hz : N ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · show ((1 - k ^ 2 * y ^ 2 : ℝ) : ℂ) ∈ slitPlane
      have hky := mul_nonneg (sq_nonneg k) (sq_nonneg y)
      have hy2 : y ^ 2 < 1 := by nlinarith
      exact ofReal_mem_slitPlane.mpr (by nlinarith)
    · show ((1 - y ^ 2 : ℝ) : ℂ) ∈ slitPlane
      exact ofReal_mem_slitPlane.mpr (by nlinarith)
    · simp [N]
  have h := carlsonRUnitIntervalIntegral_eq_gamma_mul_regCarlsonR (a := 1 / 2) (a' := 1)
    (b := B) (by norm_num) (by norm_num) (by simp [B, Fin.sum_univ_three]; norm_num) hz
  unfold carlsonRUnitIntervalIntegral at h
  rw [← integral_complex_ofReal]
  have hpt : ∀ s ∈ Ioo (0 : ℝ) 1, ((|y * (1 / (2 * Real.sqrt s))| • g (φ s) : ℝ) : ℂ) =
      (y / 2 : ℂ) * ((s : ℂ) ^ ((1 / 2 : ℂ) - 1) * (1 - s : ℂ) ^ ((1 : ℂ) - 1) *
        ∏ i, ((1 - s : ℂ) + (s : ℂ) * N i) ^ (-B i)) := by
    intro s hs
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.1.le
    have h1 : 0 < 1 - y ^ 2 * s := by nlinarith [hs.1, hs.2]
    have h2 : 0 < 1 - k ^ 2 * y ^ 2 * s := by
      nlinarith [hs.1, hs.2, sq_nonneg k, sq_nonneg y, mul_nonneg (sq_nonneg k) (sq_nonneg y)]
    have hg : g (φ s) =
        (1 - y ^ 2 * s) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * y ^ 2 * s) ^ (1 / 2 : ℝ) := by
      simp only [g, φ]
      rw [show (1 - (y * Real.sqrt s) ^ 2) = 1 - y ^ 2 * s by rw [mul_pow, hsq],
        show (1 - k ^ 2 * (y * Real.sqrt s) ^ 2) = 1 - k ^ 2 * y ^ 2 * s by rw [mul_pow, hsq]; ring]
    have habs : |y * (1 / (2 * Real.sqrt s))| = y / 2 * s ^ (-1 / 2 : ℝ) := by
      rw [abs_of_pos (by have := Real.sqrt_pos.mpr hs.1; positivity),
        show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow]
      ring
    rw [hg, habs, smul_eq_mul, ofReal_mul, ofReal_mul, ofReal_mul, ofReal_cpow hs.1.le,
      ofReal_cpow h1.le, ofReal_cpow h2.le]
    simp only [N, B, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    rw [show (1 : ℂ) - s + s * 1 = 1 by ring, one_cpow, mul_one, sub_self, cpow_zero, mul_one,
      show (1 : ℂ) - s + s * (1 - y ^ 2) = 1 - y ^ 2 * s by ring,
      show (1 : ℂ) - s + s * (1 - k ^ 2 * y ^ 2) = 1 - k ^ 2 * y ^ 2 * s by ring]
    norm_num
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul, h, carlsonR,
    Gamma_one, show (∑ i, B i) = 1 / 2 + 1 by simp [B, Fin.sum_univ_three]; norm_num,
    Gamma_add_one _ (by norm_num)]
  simp only [N, B]
  ring_nf

/-- **Carlson's (9.3-2), second kind**: for `0 < φ < π/2` and `k² < 1`,
`E(φ, k) = sin φ R_{-1/2}(-1/2, 1/2, 3/2; 1 - k² sin² φ, cos² φ, 1)`. -/
theorem legendreE_eq {φ k : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) (hk : k ^ 2 < 1) :
    (legendreE φ k : ℂ) = Real.sin φ * carlsonR (-1 / 2) ![-1 / 2, 1 / 2, 3 / 2]
      ![((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ), ((Real.cos φ ^ 2 : ℝ) : ℂ), 1] := by
  have hs0 : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hs1 : Real.sin φ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl h1
  have h := integral_legendre_eq h0 h1.le (fun t => (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ))
  unfold legendreE
  rw [h, integral_Ioo_sn_second hk hs0 hs1, Real.cos_sq']

end Carlson
