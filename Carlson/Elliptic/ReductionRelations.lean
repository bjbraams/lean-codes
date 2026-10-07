/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.LegendreThird
public import Carlson.R.IntegerParameters
public import Carlson.RPolynomial.Coefficients

/-!
# Contiguous relations of the regularized R-function in explicit coordinates

The contiguous relations of §5.9, on the whole slit domain, written for explicit parameter
vectors `![b₀, b₁, b₂]` and `![b₀, b₁, b₂, b₃]`. They are the building blocks of the
reduction formulas of Carlson's §9.3: each table row is a linear combination of finitely many
instances of these relations.

## Main results

* `Carlson.regR3_sum`, `Carlson.regR3_shift`, `Carlson.regR3_raise₀` (and `₁`, `₂`),
  `Carlson.regR3_closed`: the relations for three variables.
* `Carlson.regR4_sum`, `Carlson.regR4_shift`, `Carlson.regR4_raise₀` (to `₃`),
  `Carlson.regR4_closed`: the relations for four variables.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§5.9, 9.3.
-/

open Complex Dirichlet

@[expose] public noncomputable section

namespace Carlson

section Three

variable {x y z : ℂ}

private theorem slit3' (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    (![x, y, z] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
  intro i; fin_cases i <;> assumption

/-- `R̃_t(b) = ∑ bᵢ R̃_t(b + eᵢ)`, three variables. -/
theorem regR3_sum (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (t b₀ b₁ b₂ : ℂ) :
    regCarlsonR t ![b₀, b₁, b₂] ![x, y, z] =
      b₀ * regCarlsonR t ![b₀ + 1, b₁, b₂] ![x, y, z] +
        b₁ * regCarlsonR t ![b₀, b₁ + 1, b₂] ![x, y, z] +
          b₂ * regCarlsonR t ![b₀, b₁, b₂ + 1] ![x, y, z] := by
  rw [regCarlsonR_eq_sum_addDirichletUnit t _ (slit3' hx hy hz), Fin.sum_univ_three]
  have h0 : addDirichletUnit (![b₀, b₁, b₂] : Fin 3 → ℂ) 0 = ![b₀ + 1, b₁, b₂] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  have h1 : addDirichletUnit (![b₀, b₁, b₂] : Fin 3 → ℂ) 1 = ![b₀, b₁ + 1, b₂] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  have h2 : addDirichletUnit (![b₀, b₁, b₂] : Fin 3 → ℂ) 2 = ![b₀, b₁, b₂ + 1] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  rw [h0, h1, h2]
  simp

/-- `R̃_{t+1}(b) = ∑ bᵢ zᵢ R̃_t(b + eᵢ)`, three variables. -/
theorem regR3_shift (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (t b₀ b₁ b₂ : ℂ) :
    regCarlsonR (t + 1) ![b₀, b₁, b₂] ![x, y, z] =
      b₀ * x * regCarlsonR t ![b₀ + 1, b₁, b₂] ![x, y, z] +
        b₁ * y * regCarlsonR t ![b₀, b₁ + 1, b₂] ![x, y, z] +
          b₂ * z * regCarlsonR t ![b₀, b₁, b₂ + 1] ![x, y, z] := by
  rw [regCarlsonR_add_one_eq_sum_mul_addDirichletUnit t _ (slit3' hx hy hz), Fin.sum_univ_three]
  have h0 : addDirichletUnit (![b₀, b₁, b₂] : Fin 3 → ℂ) 0 = ![b₀ + 1, b₁, b₂] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  have h1 : addDirichletUnit (![b₀, b₁, b₂] : Fin 3 → ℂ) 1 = ![b₀, b₁ + 1, b₂] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  have h2 : addDirichletUnit (![b₀, b₁, b₂] : Fin 3 → ℂ) 2 = ![b₀, b₁, b₂ + 1] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  rw [h0, h1, h2]
  simp

/-- `R̃_t(b) = (c + t) R̃_t(b + e₀) - t x R̃_{t-1}(b + e₀)`. -/
theorem regR3_raise₀ (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (t b₀ b₁ b₂ : ℂ) :
    regCarlsonR t ![b₀, b₁, b₂] ![x, y, z] =
      (b₀ + b₁ + b₂ + t) * regCarlsonR t ![b₀ + 1, b₁, b₂] ![x, y, z] -
        t * x * regCarlsonR (t - 1) ![b₀ + 1, b₁, b₂] ![x, y, z] := by
  rw [regCarlsonR_eq_addDirichletUnit t _ (slit3' hx hy hz) 0, Fin.sum_univ_three]
  have h0 : addDirichletUnit (![b₀, b₁, b₂] : Fin 3 → ℂ) 0 = ![b₀ + 1, b₁, b₂] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  rw [h0]
  simp

/-- `R̃_t(b) = (c + t) R̃_t(b + e₁) - t y R̃_{t-1}(b + e₁)`. -/
theorem regR3_raise₁ (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (t b₀ b₁ b₂ : ℂ) :
    regCarlsonR t ![b₀, b₁, b₂] ![x, y, z] =
      (b₀ + b₁ + b₂ + t) * regCarlsonR t ![b₀, b₁ + 1, b₂] ![x, y, z] -
        t * y * regCarlsonR (t - 1) ![b₀, b₁ + 1, b₂] ![x, y, z] := by
  rw [regCarlsonR_eq_addDirichletUnit t _ (slit3' hx hy hz) 1, Fin.sum_univ_three]
  have h1 : addDirichletUnit (![b₀, b₁, b₂] : Fin 3 → ℂ) 1 = ![b₀, b₁ + 1, b₂] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  rw [h1]
  simp

/-- `R̃_t(b) = (c + t) R̃_t(b + e₂) - t z R̃_{t-1}(b + e₂)`. -/
theorem regR3_raise₂ (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (t b₀ b₁ b₂ : ℂ) :
    regCarlsonR t ![b₀, b₁, b₂] ![x, y, z] =
      (b₀ + b₁ + b₂ + t) * regCarlsonR t ![b₀, b₁, b₂ + 1] ![x, y, z] -
        t * z * regCarlsonR (t - 1) ![b₀, b₁, b₂ + 1] ![x, y, z] := by
  rw [regCarlsonR_eq_addDirichletUnit t _ (slit3' hx hy hz) 2, Fin.sum_univ_three]
  have h2 : addDirichletUnit (![b₀, b₁, b₂] : Fin 3 → ℂ) 2 = ![b₀, b₁, b₂ + 1] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  rw [h2]
  simp

/-- `R̃_{-c}(b) = x^{-b₀} y^{-b₁} z^{-b₂}/Γ(c)` with `c = b₀ + b₁ + b₂`. -/
theorem regR3_closed (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (b₀ b₁ b₂ : ℂ) :
    regCarlsonR (-(b₀ + b₁ + b₂)) ![b₀, b₁, b₂] ![x, y, z] =
      x ^ (-b₀) * y ^ (-b₁) * z ^ (-b₂) * (Gamma (b₀ + b₁ + b₂))⁻¹ := by
  have h := regCarlsonR_neg_sum_sub_nat 0 ![b₀, b₁, b₂] (slit3' hx hy hz)
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, regCarlsonRPolynomial_zero,
    Nat.cast_zero, sub_zero] at h
  simpa [add_assoc] using h

/-- The closed form at half-integer parameters `bᵢ = 1/2 + kᵢ`:
`R̃_{-c}(b; x, y, z) = x^{-1/2} y^{-1/2} z^{-1/2} (x^{k₀} y^{k₁} z^{k₂})⁻¹ / Γ(c)`. -/
theorem regR3_closed_half (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (k₀ k₁ k₂ : ℤ) :
    regCarlsonR (-(3 / 2 + k₀ + k₁ + k₂)) ![1 / 2 + k₀, 1 / 2 + k₁, 1 / 2 + k₂] ![x, y, z] =
      x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ) *
        (x ^ k₀ * y ^ k₁ * z ^ k₂)⁻¹ * (Gamma (3 / 2 + k₀ + k₁ + k₂))⁻¹ := by
  have key : ∀ {w : ℂ}, w ∈ slitPlane → ∀ k : ℤ,
      w ^ (-(1 / 2 + k : ℂ)) = w ^ (-1 / 2 : ℂ) * (w ^ k)⁻¹ := fun {w} hw k => by
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    rw [show -(1 / 2 + k : ℂ) = -1 / 2 + (-(k : ℂ)) by ring, cpow_add _ _ hw0, cpow_neg,
      cpow_intCast]
  have h := regR3_closed hx hy hz (1 / 2 + k₀) (1 / 2 + k₁) (1 / 2 + k₂)
  rw [show (1 / 2 + k₀ + (1 / 2 + k₁) + (1 / 2 + k₂) : ℂ) = 3 / 2 + k₀ + k₁ + k₂ by ring,
    key hx, key hy, key hz] at h
  rw [h]
  simp only [mul_inv]
  ring

/-- `Γ(1/2 + n)` as a rational multiple of `Γ(1/2)`, for the values used in §9.3. -/
theorem Gamma_three_halves : Gamma (3 / 2 : ℂ) = 1 / 2 * Gamma (1 / 2) := by
  rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]

/-- `Γ(5/2) = (3/4) Γ(1/2)`. -/
theorem Gamma_five_halves : Gamma (5 / 2 : ℂ) = 3 / 4 * Gamma (1 / 2) := by
  rw [show (5 / 2 : ℂ) = 3 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num),
    Gamma_three_halves]
  ring

/-- `Γ(7/2) = (15/8) Γ(1/2)`. -/
theorem Gamma_seven_halves : Gamma (7 / 2 : ℂ) = 15 / 8 * Gamma (1 / 2) := by
  rw [show (7 / 2 : ℂ) = 5 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num),
    Gamma_five_halves]
  ring

/-- `Γ(9/2) = (105/16) Γ(1/2)`. -/
theorem Gamma_nine_halves : Gamma (9 / 2 : ℂ) = 105 / 16 * Gamma (1 / 2) := by
  rw [show (9 / 2 : ℂ) = 7 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num),
    Gamma_seven_halves]
  ring

end Three

section Two

variable {x y : ℂ}

private theorem slit2' (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (![x, y] : Fin 2 → ℂ) ∈ carlsonRSlitDomain := by
  intro i; fin_cases i <;> assumption

/-- `R̃_t(b) = ∑ bᵢ R̃_t(b + eᵢ)`, two variables. -/
theorem regR2_sum (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (t b₀ b₁ : ℂ) :
    regCarlsonR t ![b₀, b₁] ![x, y] =
      b₀ * regCarlsonR t ![b₀ + 1, b₁] ![x, y] + b₁ * regCarlsonR t ![b₀, b₁ + 1] ![x, y] := by
  rw [regCarlsonR_eq_sum_addDirichletUnit t _ (slit2' hx hy), Fin.sum_univ_two]
  have h0 : addDirichletUnit (![b₀, b₁] : Fin 2 → ℂ) 0 = ![b₀ + 1, b₁] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  have h1 : addDirichletUnit (![b₀, b₁] : Fin 2 → ℂ) 1 = ![b₀, b₁ + 1] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  rw [h0, h1]
  simp

/-- `R̃_{t+1}(b) = ∑ bᵢ zᵢ R̃_t(b + eᵢ)`, two variables. -/
theorem regR2_shift (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (t b₀ b₁ : ℂ) :
    regCarlsonR (t + 1) ![b₀, b₁] ![x, y] =
      b₀ * x * regCarlsonR t ![b₀ + 1, b₁] ![x, y] +
        b₁ * y * regCarlsonR t ![b₀, b₁ + 1] ![x, y] := by
  rw [regCarlsonR_add_one_eq_sum_mul_addDirichletUnit t _ (slit2' hx hy), Fin.sum_univ_two]
  have h0 : addDirichletUnit (![b₀, b₁] : Fin 2 → ℂ) 0 = ![b₀ + 1, b₁] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  have h1 : addDirichletUnit (![b₀, b₁] : Fin 2 → ℂ) 1 = ![b₀, b₁ + 1] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  rw [h0, h1]
  simp

/-- `R̃_t(b) = (c + t) R̃_t(b + e₀) - t x R̃_{t-1}(b + e₀)`, two variables. -/
theorem regR2_raise₀ (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (t b₀ b₁ : ℂ) :
    regCarlsonR t ![b₀, b₁] ![x, y] =
      (b₀ + b₁ + t) * regCarlsonR t ![b₀ + 1, b₁] ![x, y] -
        t * x * regCarlsonR (t - 1) ![b₀ + 1, b₁] ![x, y] := by
  rw [regCarlsonR_eq_addDirichletUnit t _ (slit2' hx hy) 0, Fin.sum_univ_two]
  have h0 : addDirichletUnit (![b₀, b₁] : Fin 2 → ℂ) 0 = ![b₀ + 1, b₁] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  rw [h0]
  simp

/-- `R̃_t(b) = (c + t) R̃_t(b + e₁) - t y R̃_{t-1}(b + e₁)`, two variables. -/
theorem regR2_raise₁ (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (t b₀ b₁ : ℂ) :
    regCarlsonR t ![b₀, b₁] ![x, y] =
      (b₀ + b₁ + t) * regCarlsonR t ![b₀, b₁ + 1] ![x, y] -
        t * y * regCarlsonR (t - 1) ![b₀, b₁ + 1] ![x, y] := by
  rw [regCarlsonR_eq_addDirichletUnit t _ (slit2' hx hy) 1, Fin.sum_univ_two]
  have h1 : addDirichletUnit (![b₀, b₁] : Fin 2 → ℂ) 1 = ![b₀, b₁ + 1] := by
    ext i; fin_cases i <;> simp [addDirichletUnit]
  rw [h1]
  simp

end Two

/-- Reindexing the variables along an equivalence. -/
theorem regCarlsonR_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (t : ℂ)
    {z : κ → ℂ} (hz : z ∈ carlsonRSlitDomain) (b : ι → ℂ) :
    regCarlsonR t b (z ∘ e) = regCarlsonR t (b ∘ e.symm) z := by
  classical
  rw [regCarlsonR_aggregate_of_slit e.surjective t hz b]
  congr 1
  funext k
  rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
  have : (Finset.univ.filter fun i => e i = k) = {e.symm k} := by
    ext i; simp [Equiv.eq_symm_apply]
  rw [this, Finset.sum_singleton]
  rfl

/-- Deleting a zero last parameter, three variables to two. -/
theorem regR3_zero {x y ρ : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hρ : ρ ∈ slitPlane)
    (t b₀ b₁ : ℂ) :
    regCarlsonR t ![b₀, b₁, 0] ![x, y, ρ] = regCarlsonR t ![b₀, b₁] ![x, y] := by
  set w : Option (Fin 2) → ℂ := fun o => o.elim ρ ![x, y]
  have hw : w ∈ carlsonRSlitDomain := by
    intro o; cases o with
    | none => exact hρ
    | some i => fin_cases i <;> assumption
  have hcomp : (![x, y, ρ] : Fin 3 → ℂ) = w ∘ finSuccEquivLast := by
    funext i; fin_cases i <;> rfl
  rw [hcomp, regCarlsonR_comp_equiv _ t hw,
    regCarlsonR_option_zero t (by simp [finSuccEquivLast]) hw]
  congr 1
  · funext i; fin_cases i <;> rfl

section Four

variable {x y z ρ : ℂ}

private theorem slit4' (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) : (![x, y, z, ρ] : Fin 4 → ℂ) ∈ carlsonRSlitDomain := by
  intro i; fin_cases i <;> assumption

private theorem add4 (b₀ b₁ b₂ b₃ : ℂ) :
    addDirichletUnit (![b₀, b₁, b₂, b₃] : Fin 4 → ℂ) 0 = ![b₀ + 1, b₁, b₂, b₃] ∧
    addDirichletUnit (![b₀, b₁, b₂, b₃] : Fin 4 → ℂ) 1 = ![b₀, b₁ + 1, b₂, b₃] ∧
    addDirichletUnit (![b₀, b₁, b₂, b₃] : Fin 4 → ℂ) 2 = ![b₀, b₁, b₂ + 1, b₃] ∧
    addDirichletUnit (![b₀, b₁, b₂, b₃] : Fin 4 → ℂ) 3 = ![b₀, b₁, b₂, b₃ + 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (ext i; fin_cases i <;> simp [addDirichletUnit])

/-- `R̃_t(b) = ∑ bᵢ R̃_t(b + eᵢ)`, four variables. -/
theorem regR4_sum (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) (t b₀ b₁ b₂ b₃ : ℂ) :
    regCarlsonR t ![b₀, b₁, b₂, b₃] ![x, y, z, ρ] =
      b₀ * regCarlsonR t ![b₀ + 1, b₁, b₂, b₃] ![x, y, z, ρ] +
        b₁ * regCarlsonR t ![b₀, b₁ + 1, b₂, b₃] ![x, y, z, ρ] +
          b₂ * regCarlsonR t ![b₀, b₁, b₂ + 1, b₃] ![x, y, z, ρ] +
            b₃ * regCarlsonR t ![b₀, b₁, b₂, b₃ + 1] ![x, y, z, ρ] := by
  obtain ⟨h0, h1, h2, h3⟩ := add4 b₀ b₁ b₂ b₃
  rw [regCarlsonR_eq_sum_addDirichletUnit t _ (slit4' hx hy hz hρ), Fin.sum_univ_four, h0, h1,
    h2, h3]
  simp

/-- `R̃_{t+1}(b) = ∑ bᵢ zᵢ R̃_t(b + eᵢ)`, four variables. -/
theorem regR4_shift (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) (t b₀ b₁ b₂ b₃ : ℂ) :
    regCarlsonR (t + 1) ![b₀, b₁, b₂, b₃] ![x, y, z, ρ] =
      b₀ * x * regCarlsonR t ![b₀ + 1, b₁, b₂, b₃] ![x, y, z, ρ] +
        b₁ * y * regCarlsonR t ![b₀, b₁ + 1, b₂, b₃] ![x, y, z, ρ] +
          b₂ * z * regCarlsonR t ![b₀, b₁, b₂ + 1, b₃] ![x, y, z, ρ] +
            b₃ * ρ * regCarlsonR t ![b₀, b₁, b₂, b₃ + 1] ![x, y, z, ρ] := by
  obtain ⟨h0, h1, h2, h3⟩ := add4 b₀ b₁ b₂ b₃
  rw [regCarlsonR_add_one_eq_sum_mul_addDirichletUnit t _ (slit4' hx hy hz hρ),
    Fin.sum_univ_four, h0, h1, h2, h3]
  simp

/-- `R̃_t(b) = (c + t) R̃_t(b + e₀) - t z₀ R̃_{t-1}(b + e₀)`, four variables. -/
theorem regR4_raise₀ (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) (t b₀ b₁ b₂ b₃ : ℂ) :
    regCarlsonR t ![b₀, b₁, b₂, b₃] ![x, y, z, ρ] =
      (b₀ + b₁ + b₂ + b₃ + t) * regCarlsonR t ![b₀ + 1, b₁, b₂, b₃] ![x, y, z, ρ] -
        t * x * regCarlsonR (t - 1) ![b₀ + 1, b₁, b₂, b₃] ![x, y, z, ρ] := by
  obtain ⟨h0, h1, h2, h3⟩ := add4 b₀ b₁ b₂ b₃
  rw [regCarlsonR_eq_addDirichletUnit t _ (slit4' hx hy hz hρ) 0, Fin.sum_univ_four, h0]
  simp

/-- `R̃_t(b) = (c + t) R̃_t(b + e₁) - t z₁ R̃_{t-1}(b + e₁)`, four variables. -/
theorem regR4_raise₁ (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) (t b₀ b₁ b₂ b₃ : ℂ) :
    regCarlsonR t ![b₀, b₁, b₂, b₃] ![x, y, z, ρ] =
      (b₀ + b₁ + b₂ + b₃ + t) * regCarlsonR t ![b₀, b₁ + 1, b₂, b₃] ![x, y, z, ρ] -
        t * y * regCarlsonR (t - 1) ![b₀, b₁ + 1, b₂, b₃] ![x, y, z, ρ] := by
  obtain ⟨h0, h1, h2, h3⟩ := add4 b₀ b₁ b₂ b₃
  rw [regCarlsonR_eq_addDirichletUnit t _ (slit4' hx hy hz hρ) 1, Fin.sum_univ_four, h1]
  simp

/-- `R̃_t(b) = (c + t) R̃_t(b + e₂) - t z₂ R̃_{t-1}(b + e₂)`, four variables. -/
theorem regR4_raise₂ (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) (t b₀ b₁ b₂ b₃ : ℂ) :
    regCarlsonR t ![b₀, b₁, b₂, b₃] ![x, y, z, ρ] =
      (b₀ + b₁ + b₂ + b₃ + t) * regCarlsonR t ![b₀, b₁, b₂ + 1, b₃] ![x, y, z, ρ] -
        t * z * regCarlsonR (t - 1) ![b₀, b₁, b₂ + 1, b₃] ![x, y, z, ρ] := by
  obtain ⟨h0, h1, h2, h3⟩ := add4 b₀ b₁ b₂ b₃
  rw [regCarlsonR_eq_addDirichletUnit t _ (slit4' hx hy hz hρ) 2, Fin.sum_univ_four, h2]
  simp

/-- `R̃_t(b) = (c + t) R̃_t(b + e₃) - t z₃ R̃_{t-1}(b + e₃)`, four variables. -/
theorem regR4_raise₃ (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) (t b₀ b₁ b₂ b₃ : ℂ) :
    regCarlsonR t ![b₀, b₁, b₂, b₃] ![x, y, z, ρ] =
      (b₀ + b₁ + b₂ + b₃ + t) * regCarlsonR t ![b₀, b₁, b₂, b₃ + 1] ![x, y, z, ρ] -
        t * ρ * regCarlsonR (t - 1) ![b₀, b₁, b₂, b₃ + 1] ![x, y, z, ρ] := by
  obtain ⟨h0, h1, h2, h3⟩ := add4 b₀ b₁ b₂ b₃
  rw [regCarlsonR_eq_addDirichletUnit t _ (slit4' hx hy hz hρ) 3, Fin.sum_univ_four, h3]
  simp

/-- Deleting a zero last parameter, four variables to three. -/
theorem regR4_zero (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) (t b₀ b₁ b₂ : ℂ) :
    regCarlsonR t ![b₀, b₁, b₂, 0] ![x, y, z, ρ] = regCarlsonR t ![b₀, b₁, b₂] ![x, y, z] := by
  set w : Option (Fin 3) → ℂ := fun o => o.elim ρ ![x, y, z]
  have hw : w ∈ carlsonRSlitDomain := by
    intro o; cases o with
    | none => exact hρ
    | some i => fin_cases i <;> assumption
  have hcomp : (![x, y, z, ρ] : Fin 4 → ℂ) = w ∘ finSuccEquivLast := by
    funext i; fin_cases i <;> rfl
  rw [hcomp, regCarlsonR_comp_equiv _ t hw,
    regCarlsonR_option_zero t (by simp [finSuccEquivLast]) hw]
  congr 1
  funext i; fin_cases i <;> rfl

/-- The closed form `R̃_{-c}(b; x, y, z, ρ)` at `bᵢ = 1/2 + kᵢ` (`i < 3`) and `b₃ = m`. -/
theorem regR4_closed_half (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    (hρ : ρ ∈ slitPlane) (k₀ k₁ k₂ m : ℤ) :
    regCarlsonR (-(3 / 2 + k₀ + k₁ + k₂ + m)) ![1 / 2 + k₀, 1 / 2 + k₁, 1 / 2 + k₂, (m : ℂ)]
        ![x, y, z, ρ] =
      x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ) *
        (x ^ k₀ * y ^ k₁ * z ^ k₂ * ρ ^ m)⁻¹ * (Gamma (3 / 2 + k₀ + k₁ + k₂ + m))⁻¹ := by
  have key : ∀ {w : ℂ}, w ∈ slitPlane → ∀ k : ℤ,
      w ^ (-(1 / 2 + k : ℂ)) = w ^ (-1 / 2 : ℂ) * (w ^ k)⁻¹ := fun {w} hw k => by
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    rw [show -(1 / 2 + k : ℂ) = -1 / 2 + (-(k : ℂ)) by ring, cpow_add _ _ hw0, cpow_neg,
      cpow_intCast]
  have h := regCarlsonR_neg_sum_sub_nat 0 ![1 / 2 + (k₀ : ℂ), 1 / 2 + k₁, 1 / 2 + k₂, (m : ℂ)]
    (slit4' hx hy hz hρ)
  simp only [Fin.sum_univ_four, Fin.prod_univ_four, regCarlsonRPolynomial_zero,
    Nat.cast_zero, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  rw [show (1 / 2 + k₀ + (1 / 2 + k₁) + (1 / 2 + k₂) + m : ℂ) = 3 / 2 + k₀ + k₁ + k₂ + m by ring,
    key hx, key hy, key hz, cpow_neg, cpow_intCast] at h
  rw [h]
  simp only [mul_inv]
  ring

end Four

/-- `Γ(-1/2) = -2 Γ(1/2)`. -/
theorem Gamma_neg_half : Gamma (-(1 / 2) : ℂ) = -2 * Gamma (1 / 2) := by
  have h := Gamma_add_one (-(1 / 2) : ℂ) (by norm_num)
  rw [show (-(1 / 2) : ℂ) + 1 = 1 / 2 by norm_num] at h
  rw [h]; ring

/-- `Γ(2) = 1`. -/
theorem Gamma_two' : Gamma (2 : ℂ) = 1 := by
  rw [show (2 : ℂ) = 1 + 1 by norm_num, Gamma_add_one _ one_ne_zero, Gamma_one, mul_one]

/-- `Γ(3) = 2`. -/
theorem Gamma_three' : Gamma (3 : ℂ) = 2 := by
  rw [show (3 : ℂ) = 2 + 1 by norm_num, Gamma_add_one _ two_ne_zero, Gamma_two', mul_one]

end Carlson
