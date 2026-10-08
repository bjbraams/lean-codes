/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.LandenAlgorithm
public import Carlson.R.SmallVariableJoint

/-!
# Symmetric elliptic integrals with a vanishing variable

The joint small-variable limit (`Carlson.R.SmallVariableJoint`) makes `R_F(x, y, z)` continuous as
`(x, y, z) → (x₀, y₀, 0)` in the right half-plane, with limit `(π/2) R_K(x₀, y₀)` (8.3-17). This
extends the results of Chapter 9 to a vanishing variable.

* (9.2-4): `R_E(x, y) → (2/π) x^{1/2}` and `R_L(x, y, ρ) → (4/π) R_C(x, ρ)` as `y → 0`.
* Algorithm 9.5-2 started at `s₀ = 0`:
  `(π/2) R_K(c₀², a₀²) = R_C(S² + M², S²) = (1/M) arcsinh(M/S)`.
* The duplication theorem with one variable `0`, on the whole slit plane:
  `(π/2) R_K(x, y) = 2 R_F(x + λ, y + λ, λ)`, `λ = x^{1/2} y^{1/2}`.
* **Carlson's (9.7-17)**, the addition theorem with one variable `0`:
  `R_F(x + λ, y + λ, λ) + R_F(x + μ, y + μ, μ) = (π/2) R_K(x, y)` if `λμ = xy`.

## Main results

* `Carlson.tendsto_carlsonRF_nhdsWithin_zero`, `Carlson.tendsto_carlsonRF_zero_of_tendsto`.
* `Carlson.tendsto_carlsonRE_zero`, `Carlson.tendsto_carlsonRL_zero`: (9.2-4).
* `Carlson.tendsto_ascLanden_zero`: Algorithm 9.5-2 with `s₀ = 0`.
* `Carlson.carlsonRK_duplication`: duplication with a vanishing variable.
* `Carlson.carlsonRF_add_carlsonRF_zero`: (9.7-17).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.
-/

open Complex Set Filter Dirichlet
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

open TwoVariable (pair sum_pair carlsonRK carlsonRC)

private theorem Gamma_three_halves_mul_one_half : Gamma (3 / 2 : ℂ) * Gamma (1 / 2) = π / 2 := by
  rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num),
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal,
    Real.Gamma_one_half_eq]
  have : ((Real.sqrt π : ℝ) : ℂ) * (Real.sqrt π : ℝ) = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  push_cast
  linear_combination (1 / 2 : ℂ) * this

/-- **The joint limit (8.3-17)**: `R_F(x, y, z) → (π/2) R_K(x₀, y₀)` as `(x, y, z) → (x₀, y₀, 0)`
through the right half-plane. -/
theorem tendsto_carlsonRF_nhdsWithin_zero {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Tendsto (fun w : Fin 3 → ℂ => carlsonRF (w 0) (w 1) (w 2))
      (𝓝[carlsonRVariableDomain] ![x, y, 0]) (𝓝 ((π / 2 : ℂ) * carlsonRK x y)) := by
  have H := tendsto_regCarlsonR_nhdsWithin_zero (ι := Fin 3) 2 (a := 1 / 2) (a' := 1)
    (b := fun _ => 1 / 2) (z₀ := ![x, y, 0]) (by simp; norm_num) (by norm_num) rfl
    (fun j hj => by fin_cases j <;> simp_all) ⟨0, by decide⟩
  set q : {j : Fin 3 // j ≠ 2} → Fin 2 := fun j => if j.1 = 0 then 0 else 1
  have hq : Function.Surjective q := by
    intro k; fin_cases k
    · exact ⟨⟨0, by decide⟩, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl⟩
  have hs : pair x y ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact mem_slitPlane_iff.mpr (Or.inl hx)
    · exact mem_slitPlane_iff.mpr (Or.inl hy)
  have hcomp : eraseCarlsonVariable 2 (![x, y, 0] : Fin 3 → ℂ) = pair x y ∘ q := by
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
  have H' := H.const_mul (Gamma (3 / 2))
  have hval : Gamma (3 / 2) * (Gamma (1 - 1 / 2) * ((Gamma 1)⁻¹ *
      regCarlsonR (-(1 / 2)) (pair (1 / 2) (1 / 2)) (pair x y))) =
        (π / 2 : ℂ) * carlsonRK x y := by
    unfold TwoVariable.carlsonRK carlsonR
    rw [sum_pair, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Gamma_one, inv_one, one_mul, one_mul,
      show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, ← mul_assoc, Gamma_three_halves_mul_one_half,
      show (-(1 / 2) : ℂ) = -1 / 2 by ring]
  rw [hval] at H'
  refine H'.congr fun w => ?_
  rw [carlsonRF_eq, show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  congr 2
  funext i; fin_cases i <;> rfl

/-- The joint limit along an arbitrary filter. -/
theorem tendsto_carlsonRF_zero_of_tendsto {α : Type*} {l : Filter α} {f g h : α → ℂ}
    {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y))
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ a in l, 0 < (f a).re ∧ 0 < (g a).re ∧ 0 < (h a).re) :
    Tendsto (fun a => carlsonRF (f a) (g a) (h a)) l (𝓝 ((π / 2 : ℂ) * carlsonRK x y)) := by
  have hvec : Tendsto (fun a => (![f a, g a, h a] : Fin 3 → ℂ)) l
      (𝓝[carlsonRVariableDomain] ![x, y, 0]) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · rw [tendsto_pi_nhds]
      intro i; fin_cases i
      · exact hf
      · exact hg
      · exact hh
    · filter_upwards [hpos] with a ha i
      fin_cases i
      · exact ha.1
      · exact ha.2.1
      · exact ha.2.2
  exact (tendsto_carlsonRF_nhdsWithin_zero hx hy).comp hvec

/-- Real positive numbers tending to `0` from above approach `0` through the right half-plane. -/
theorem tendsto_ofReal_nhdsGT_zero :
    Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 0) (𝓝[{w : ℂ | 0 < w.re}] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa using (continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simpa using hs

/-! ### Carlson's (9.2-4) -/

private theorem tendsto_pair_zero {t b₁ b₂ : ℂ} {x : ℂ} (hx : 0 < x.re)
    (h : 0 < (b₁ + b₂ + t - b₂).re) :
    Tendsto (fun y => regCarlsonR t (pair b₁ b₂) (pair x y)) (𝓝[{w : ℂ | 0 < w.re}] 0)
      (𝓝 (Gamma (b₁ + t) * ((Gamma (b₁ + b₂ + t))⁻¹ * (x ^ t * (Gamma b₁)⁻¹)))) := by
  have hz : pair x 1 ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · exact hx
    · simp [carlsonRightHalfPlane, pair]
  have H := tendsto_regCarlsonR_update_zero (ι := Fin 2) 1 (a := -t) (a' := b₁ + b₂ + t)
    (b := pair b₁ b₂) (z := pair x 1) (by simp) (by simpa [pair] using h) hz
    ⟨0, by decide⟩ (E := ↥{z : ℂ | 0 < z.re}) (l := comap Subtype.val (𝓝 0)) (w := Subtype.val)
    (fun v => v.2) tendsto_comap
  have e1 : eraseCarlsonParameter 1 (pair b₁ b₂) = fun _ => b₁ := by
    funext j; obtain ⟨j, hj⟩ := j; fin_cases j
    · rfl
    · exact absurd rfl hj
  have e2 : eraseCarlsonVariable 1 (pair x 1) = fun _ => x := by
    funext j; obtain ⟨j, hj⟩ := j; fin_cases j
    · rfl
    · exact absurd rfl hj
  have hone : Fintype.card {j : Fin 2 // j ≠ 1} = 1 := by decide
  have eq1 : regCarlsonR (-(-t)) (eraseCarlsonParameter 1 (pair b₁ b₂))
      (eraseCarlsonVariable 1 (pair x 1)) = x ^ t * (Gamma b₁)⁻¹ := by
    rw [e1, e2, neg_neg, regCarlsonR_const_node t _ (carlsonRightHalfPlane_subset_slitPlane hx)]
    simp [Finset.sum_const, hone]
  rw [eq1, show b₁ + b₂ + t - pair b₁ b₂ 1 = b₁ + t by simp [pair]; ring] at H
  rw [nhdsWithin, ← Filter.subtype_coe_map_comap, tendsto_map'_iff]
  refine H.congr fun v => ?_
  simp only [Function.comp_apply, neg_neg]
  congr 1
  funext i; fin_cases i <;> rfl

/-- **Carlson's (9.2-4) for `R_E`**: `R_E(x, y) → (2/π) x^{1/2}` as `y → 0` in the right
half-plane. -/
theorem tendsto_carlsonRE_zero {x : ℂ} (hx : 0 < x.re) :
    Tendsto (fun y => carlsonRE x y) (𝓝[{w : ℂ | 0 < w.re}] 0)
      (𝓝 (2 / π * x ^ (1 / 2 : ℂ))) := by
  have H := tendsto_pair_zero (t := 1 / 2) (b₁ := 1 / 2) (b₂ := 1 / 2) hx (by norm_num)
  have hG := Gamma_three_halves_mul_one_half
  have hG1 : Gamma (1 / 2 + 1 / 2 : ℂ) = 1 := by norm_num
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hval : Gamma (1 / 2 + 1 / 2 : ℂ) * (Gamma (1 / 2 + 1 / 2 + 1 / 2))⁻¹ *
      (x ^ (1 / 2 : ℂ) * (Gamma (1 / 2))⁻¹) = 2 / π * x ^ (1 / 2 : ℂ) := by
    rw [hG1, show (1 / 2 + 1 / 2 + 1 / 2 : ℂ) = 3 / 2 by norm_num]
    have h3 : Gamma (3 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
    have h1 : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
    field_simp
    linear_combination (-2 * x ^ (1 / 2 : ℂ)) * hG
  rw [← hval, mul_assoc]
  refine H.congr fun y => ?_
  unfold carlsonRE carlsonR
  rw [sum_pair, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Gamma_one, one_mul]

/-- **Carlson's (9.2-4) for `R_L`**: `R_L(x, y, ρ) → (4/π) R_C(x, ρ)` as `y → 0` in the right
half-plane. -/
theorem tendsto_carlsonRL_zero {x ρ : ℂ} (hx : 0 < x.re) (hρ : 0 < ρ.re) :
    Tendsto (fun y => carlsonRL x y ρ) (𝓝[{w : ℂ | 0 < w.re}] 0)
      (𝓝 (4 / π * carlsonRC x ρ)) := by
  have hz : (![x, 1, ρ] : Fin 3 → ℂ) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · exact hx
    · simp [carlsonRightHalfPlane]
    · exact hρ
  have H := tendsto_regCarlsonR_update_zero (ι := Fin 3) 1 (a := 1 / 2) (a' := 3 / 2)
    (b := ![1 / 2, 1 / 2, 1]) (z := ![x, 1, ρ]) (by simp [Fin.sum_univ_three]; norm_num)
    (by simp; norm_num) hz ⟨0, by decide⟩ (E := ↥{z : ℂ | 0 < z.re})
    (l := comap Subtype.val (𝓝 0)) (w := Subtype.val) (fun v => v.2) tendsto_comap
  set q : {j : Fin 3 // j ≠ 1} → Fin 2 := fun j => if j.1 = 0 then 0 else 1
  have hq : Function.Surjective q := by
    intro k; fin_cases k
    · exact ⟨⟨0, by decide⟩, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl⟩
  have hs : pair x ρ ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact mem_slitPlane_iff.mpr (Or.inl hx)
    · exact mem_slitPlane_iff.mpr (Or.inl hρ)
  have hcomp : eraseCarlsonVariable 1 (![x, 1, ρ] : Fin 3 → ℂ) = pair x ρ ∘ q := by
    funext j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · rfl
    · exact absurd rfl hj
    · rfl
  have hagg : stdSimplexAggregate q
      (eraseCarlsonParameter 1 (![1 / 2, 1 / 2, 1] : Fin 3 → ℂ)) = pair (1 / 2) 1 := by
    funext k
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    fin_cases k
    · have : (Finset.univ.filter fun j : {j : Fin 3 // j ≠ 1} => q j = 0) = {⟨0, by decide⟩} := by
        decide
      show (Finset.univ.filter fun j => q j = 0).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
    · have : (Finset.univ.filter fun j : {j : Fin 3 // j ≠ 1} => q j = 1) = {⟨2, by decide⟩} := by
        decide
      show (Finset.univ.filter fun j => q j = 1).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
  rw [hcomp, regCarlsonR_aggregate_of_slit hq _ hs, hagg] at H
  have hG := Gamma_three_halves_mul_one_half
  have hval : Gamma (3 / 2 - (![1 / 2, 1 / 2, 1] : Fin 3 → ℂ) 1) * ((Gamma (3 / 2))⁻¹ *
      regCarlsonR (-(1 / 2)) (pair (1 / 2) 1) (pair x ρ)) = 4 / π * carlsonRC x ρ := by
    unfold TwoVariable.carlsonRC carlsonR
    rw [sum_pair, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [show (3 / 2 : ℂ) - 1 / 2 = 1 by norm_num, Gamma_one, one_mul,
      show (-(1 / 2) : ℂ) = -1 / 2 by ring]
    have h3 : Gamma (3 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
    have h1 : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    have hG' : Gamma (3 / 2 : ℂ) * Gamma (3 / 2) = π / 4 := by
      have : Gamma (3 / 2 : ℂ) = 1 / 2 * Gamma (1 / 2) := by
        rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
      rw [this] at hG ⊢
      linear_combination (1 / 2 : ℂ) * hG
    have e : (-1 / 2 : ℂ) = -(1 / 2) := by ring
    simp only [e]
    field_simp
    linear_combination (-4 * regCarlsonR (-(1 / 2)) (pair (1 / 2) 1) (pair x ρ)) * hG'
  rw [hval] at H
  rw [nhdsWithin, ← Filter.subtype_coe_map_comap, tendsto_map'_iff]
  refine H.congr fun v => ?_
  simp only [Function.comp_apply]
  unfold carlsonRL carlsonR
  rw [show (∑ i, (![1 / 2, 1 / 2, 1] : Fin 3 → ℂ) i) = 2 by simp [Fin.sum_univ_three]; norm_num,
    show Gamma (2 : ℂ) = 1 by rw [show (2 : ℂ) = 1 + 1 by norm_num, Gamma_add_one _ one_ne_zero,
      Gamma_one, mul_one], one_mul, show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  congr 1
  funext i; fin_cases i <;> rfl

/-! ### Algorithm 9.5-2 started at `s₀ = 0` -/

/-- One step of the ascending Landen algorithm, as a shift of the sequences. -/
theorem ascLanden_shift (s₀ a₀ c₀ : ℝ) (n : ℕ) :
    landenAC a₀ c₀ (n + 1) = landenAC (landenAC a₀ c₀ 1).1 (landenAC a₀ c₀ 1).2 n ∧
    ascLandenS s₀ a₀ c₀ (n + 1) =
      ascLandenS (ascLandenS s₀ a₀ c₀ 1) (landenAC a₀ c₀ 1).1 (landenAC a₀ c₀ 1).2 n := by
  have hAC : ∀ m, landenAC a₀ c₀ (m + 1) =
      landenAC (landenAC a₀ c₀ 1).1 (landenAC a₀ c₀ 1).2 m := by
    intro m
    simp only [landenAC, Prod.mk.eta]
    rw [Function.iterate_succ_apply, Function.iterate_one]
  refine ⟨hAC n, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    show (ascLandenS s₀ a₀ c₀ (n + 1) +
        √(ascLandenS s₀ a₀ c₀ (n + 1) ^ 2 + (landenAC a₀ c₀ (n + 1)).2 ^ 2)) / 2 = _
    rw [ih, hAC n]
    rfl

/-- **Carlson's Algorithm 9.5-2 with `s₀ = 0`**: for `a₀ > c₀ > 0`,
`(π/2) R_K(c₀², a₀²) = R_C(S² + M², S²) = (1/M) arcsinh(M/S)`, where `S = lim sₙ` and
`M = lim aₙ`. -/
theorem tendsto_ascLanden_zero {a₀ c₀ : ℝ} (hc : 0 < c₀) (hac : c₀ < a₀) :
    ∃ S M : ℝ, 0 < S ∧ 0 < M ∧ Tendsto (ascLandenS 0 a₀ c₀) atTop (𝓝 S) ∧
      Tendsto (fun n => (landenAC a₀ c₀ n).1) atTop (𝓝 M) ∧
      (π / 2 : ℂ) * carlsonRK ((c₀ ^ 2 : ℝ) : ℂ) ((a₀ ^ 2 : ℝ) : ℂ) =
        carlsonRC ((S ^ 2 + M ^ 2 : ℝ) : ℂ) ((S ^ 2 : ℝ) : ℂ) ∧
      (π / 2 : ℂ) * carlsonRK ((c₀ ^ 2 : ℝ) : ℂ) ((a₀ ^ 2 : ℝ) : ℂ) =
        ((Real.arsinh (M / S) / M : ℝ) : ℂ) := by
  set s₁ := ascLandenS 0 a₀ c₀ 1
  have hs₁ : s₁ = c₀ / 2 := by
    show (0 + √(0 ^ 2 + (landenAC a₀ c₀ 0).2 ^ 2)) / 2 = c₀ / 2
    simp [landenAC, Real.sqrt_sq hc.le]
  have hs₁pos : 0 < s₁ := by rw [hs₁]; positivity
  have h1 : landenAC a₀ c₀ 1 = landenACStep (a₀, c₀) := by simp [landenAC]
  have hlt := landenACStep_lt hc hac
  rw [← h1] at hlt
  obtain ⟨S, M, hS, hM, hSlim, hMlim, -, hRC, hash⟩ := tendsto_ascLanden hs₁pos hlt.1 hlt.2
  have hshift := ascLanden_shift 0 a₀ c₀
  have hsl : ∀ r : ℝ, 0 < r → ((r : ℂ)) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  have hcyc : ∀ u v w : ℂ, u ∈ slitPlane → v ∈ slitPlane → w ∈ slitPlane →
      carlsonRF u v w = carlsonRF w u v := fun u v w hu hv hw => by
    rw [carlsonRF_comm_right hu hw hv, carlsonRF_comm_left hw hu hv]
  -- the first step, as a limit `s → 0`
  have hkey : carlsonRF ((s₁ ^ 2 : ℝ) : ℂ) ((s₁ ^ 2 + (landenAC a₀ c₀ 1).2 ^ 2 : ℝ) : ℂ)
      ((s₁ ^ 2 + (landenAC a₀ c₀ 1).1 ^ 2 : ℝ) : ℂ) =
      (π / 2 : ℂ) * carlsonRK ((c₀ ^ 2 : ℝ) : ℂ) ((a₀ ^ 2 : ℝ) : ℂ) := by
    set sp : ℝ → ℝ := fun s => (s + √(s ^ 2 + c₀ ^ 2)) / 2
    have hsp : Continuous sp := by fun_prop
    have hsp0 : sp 0 = s₁ := by
      simp only [sp]; rw [hs₁]; simp [Real.sqrt_sq hc.le]
    have ht : Tendsto sp (𝓝[>] 0) (𝓝 s₁) := by
      rw [← hsp0]; exact (hsp.tendsto 0).mono_left nhdsWithin_le_nhds
    have hL := tendsto_carlsonRF_ofReal (pow_pos hs₁pos 2)
      (add_pos_of_pos_of_nonneg (pow_pos hs₁pos 2) (sq_nonneg (landenAC a₀ c₀ 1).2))
      (add_pos_of_pos_of_nonneg (pow_pos hs₁pos 2) (sq_nonneg (landenAC a₀ c₀ 1).1))
      (ht.pow 2) ((ht.pow 2).add_const _) ((ht.pow 2).add_const _)
    have hc0 : Continuous fun s : ℝ => ((s ^ 2 + c₀ ^ 2 : ℝ) : ℂ) := by fun_prop
    have ha0 : Continuous fun s : ℝ => ((s ^ 2 + a₀ ^ 2 : ℝ) : ℂ) := by fun_prop
    have hz0 : Continuous fun s : ℝ => ((s ^ 2 : ℝ) : ℂ) := by fun_prop
    have hR := tendsto_carlsonRF_zero_of_tendsto (l := 𝓝[>] (0 : ℝ))
      (f := fun s : ℝ => ((s ^ 2 + c₀ ^ 2 : ℝ) : ℂ))
      (g := fun s : ℝ => ((s ^ 2 + a₀ ^ 2 : ℝ) : ℂ)) (h := fun s : ℝ => ((s ^ 2 : ℝ) : ℂ))
      (x := ((c₀ ^ 2 : ℝ) : ℂ)) (y := ((a₀ ^ 2 : ℝ) : ℂ)) (by rw [ofReal_re]; exact pow_pos hc 2)
      (by rw [ofReal_re]; exact pow_pos (hc.trans hac) 2)
      (by simpa using (hc0.tendsto 0).mono_left nhdsWithin_le_nhds)
      (by simpa using (ha0.tendsto 0).mono_left nhdsWithin_le_nhds)
      (by simpa using (hz0.tendsto 0).mono_left nhdsWithin_le_nhds)
      (by
        filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
        simp only [ofReal_re]
        exact ⟨by positivity, by positivity, by positivity⟩)
    refine tendsto_nhds_unique hL (hR.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    have hstep := carlsonRF_ascStep hs hc hac
    rw [← h1] at hstep
    simp only [sp]
    rw [hstep, hcyc _ _ _ (hsl _ (by positivity)) (hsl _ (by positivity))
      (hsl _ (by positivity))]
  refine ⟨S, M, hS, hM, ?_, ?_, hkey.symm.trans hRC, hkey.symm.trans hash⟩
  · rw [← tendsto_add_atTop_iff_nat 1]
    exact hSlim.congr fun n => (hshift n).2.symm
  · rw [← tendsto_add_atTop_iff_nat 1]
    exact hMlim.congr fun n => by rw [(hshift n).1]

/-! ### Duplication with a vanishing variable -/

/-- Duplication with `z = 0` for positive reals:
`(π/2) R_K(x, y) = 2 R_F(x + √x√y, y + √x√y, √x√y)`. -/
theorem carlsonRK_duplication_ofReal {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (π / 2 : ℂ) * carlsonRK (x : ℂ) (y : ℂ) = 2 * carlsonRF
      ((x + √x * √y : ℝ) : ℂ) ((y + √x * √y : ℝ) : ℂ) ((√x * √y : ℝ) : ℂ) := by
  set L : ℝ → ℝ := fun z => √x * √y + √x * √z + √y * √z
  have hL : Continuous L := by fun_prop
  have hL0 : L 0 = √x * √y := by simp [L]
  have hLt : Tendsto L (𝓝[>] 0) (𝓝 (√x * √y)) := by
    rw [← hL0]; exact (hL.tendsto 0).mono_left nhdsWithin_le_nhds
  have hxy : 0 < √x * √y := by positivity
  have hleft : Tendsto (fun z : ℝ => carlsonRF (x : ℂ) (y : ℂ) (z : ℂ)) (𝓝[>] 0)
      (𝓝 ((π / 2 : ℂ) * carlsonRK x y)) :=
    (tendsto_carlsonRF_zero (by simpa using hx) (by simpa using hy)).comp
      tendsto_ofReal_nhdsGT_zero
  have hright : Tendsto (fun z : ℝ => 2 * carlsonRF ((x + L z : ℝ) : ℂ) ((y + L z : ℝ) : ℂ)
      ((z + L z : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (2 * carlsonRF ((x + √x * √y : ℝ) : ℂ)
        ((y + √x * √y : ℝ) : ℂ) ((√x * √y : ℝ) : ℂ))) := by
    refine Tendsto.const_mul _ ?_
    have hz : Tendsto (fun z : ℝ => z + L z) (𝓝[>] 0) (𝓝 (√x * √y)) := by
      simpa using (tendsto_id.mono_left nhdsWithin_le_nhds).add hLt
    exact tendsto_carlsonRF_ofReal (by positivity) (by positivity) hxy (hLt.const_add x)
      (hLt.const_add y) hz
  refine tendsto_nhds_unique hleft (hright.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with z (hz : 0 < z)
  exact (carlsonRF_duplication_ofReal hx hy hz).symm

private theorem mem_slit_add_sqrt {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    x + x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) ∈ slitPlane := by
  have := cpow_half_sq x
  rw [show x + x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) =
    x ^ (1 / 2 : ℂ) * (x ^ (1 / 2 : ℂ) + y ^ (1 / 2 : ℂ)) by linear_combination -this]
  refine mul_mem_slitPlane_of_re_pos (re_cpow_half_pos hx) ?_
  rw [add_re]; linarith [re_cpow_half_pos hx, re_cpow_half_pos hy]

/-- The duplication defect with a vanishing variable. -/
private def dupZeroDefect (x y : ℂ) : ℂ :=
  (π / 2 : ℂ) * carlsonRK x y - 2 * carlsonRF (x + x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ))
    (y + x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ)) (x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ))

private theorem analyticAt_carlsonRK_comp {f g : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hg : AnalyticAt ℂ g p) (mf : f p ∈ slitPlane) (mg : g p ∈ slitPlane) :
    AnalyticAt ℂ (fun q => carlsonRK (f q) (g q)) p := by
  unfold TwoVariable.carlsonRK carlsonR
  refine analyticAt_const.mul (analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const ?_ ?_)
  · refine analyticAt_pi_iff.mpr fun i => ?_
    fin_cases i
    · simpa [pair] using hf
    · simpa [pair] using hg
  · intro i; fin_cases i
    · simpa [pair] using mf
    · simpa [pair] using mg

private theorem analyticOnNhd_dupZeroDefect_left {y : ℂ} (hy : y ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun x => dupZeroDefect x y) slitPlane := by
  intro x hx
  have hs : AnalyticAt ℂ (fun w : ℂ => w ^ (1 / 2 : ℂ)) x := analyticAt_id.cpow analyticAt_const hx
  have hL : AnalyticAt ℂ (fun w : ℂ => w ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ)) x :=
    hs.mul analyticAt_const
  unfold dupZeroDefect
  refine (analyticAt_const.mul (analyticAt_carlsonRK_comp analyticAt_id analyticAt_const hx hy)).sub
    (analyticAt_const.mul
        (analyticAt_carlsonRF_comp (analyticAt_id.add hL) (analyticAt_const.add hL)
      hL (mem_slit_add_sqrt hx hy) ?_ ?_))
  · rw [mul_comm]; exact mem_slit_add_sqrt hy hx
  · exact mul_mem_slitPlane_of_re_pos (re_cpow_half_pos hx) (re_cpow_half_pos hy)

private theorem analyticOnNhd_dupZeroDefect_right {x : ℂ} (hx : x ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun y => dupZeroDefect x y) slitPlane := by
  intro y hy
  have hs : AnalyticAt ℂ (fun w : ℂ => w ^ (1 / 2 : ℂ)) y := analyticAt_id.cpow analyticAt_const hy
  have hL : AnalyticAt ℂ (fun w : ℂ => x ^ (1 / 2 : ℂ) * w ^ (1 / 2 : ℂ)) y :=
    analyticAt_const.mul hs
  unfold dupZeroDefect
  refine (analyticAt_const.mul (analyticAt_carlsonRK_comp analyticAt_const analyticAt_id hx hy)).sub
    (analyticAt_const.mul
        (analyticAt_carlsonRF_comp (analyticAt_const.add hL) (analyticAt_id.add hL)
      hL (mem_slit_add_sqrt hx hy) ?_ ?_))
  · rw [mul_comm]; exact mem_slit_add_sqrt hy hx
  · exact mul_mem_slitPlane_of_re_pos (re_cpow_half_pos hx) (re_cpow_half_pos hy)

/-- **The duplication theorem with a vanishing variable** (Carlson's Theorem 9.6-1 with
`z = 0`): for `x, y` in the slit plane and `λ = x^{1/2} y^{1/2}`,
`(π/2) R_K(x, y) = 2 R_F(x + λ, y + λ, λ)`. -/
theorem carlsonRK_duplication {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (π / 2 : ℂ) * carlsonRK x y = 2 * carlsonRF (x + x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ))
      (y + x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ)) (x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ)) := by
  have hpos : ∀ r : ℝ, 0 < r → ((r : ℂ)) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  have h1 : ∀ a b : ℝ, 0 < a → 0 < b → dupZeroDefect a b = 0 := by
    intro a b ha hb
    unfold dupZeroDefect
    rw [ofReal_cpow_half ha.le, ofReal_cpow_half hb.le, carlsonRK_duplication_ofReal ha hb]
    push_cast
    ring
  have hext : ∀ {F : ℂ → ℂ}, AnalyticOnNhd ℂ F slitPlane → (∀ r : ℝ, 0 < r → F r = 0) →
      ∀ w ∈ slitPlane, F w = 0 := by
    intro F hF h w hw
    have hEq : ∀ᶠ t : ℝ in 𝓝 1, F (t : ℂ) = (fun _ => (0 : ℂ)) (t : ℂ) := by
      filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact h t ht
    exact hF.eqOn_of_eventuallyEq_ofReal analyticOnNhd_const
      (starConvex_one_slitPlane.isPathConnected (by simp)).isConnected.isPreconnected
      (by simp) hEq hw
  have h2 : ∀ w ∈ slitPlane, ∀ b : ℝ, 0 < b → dupZeroDefect w b = 0 := fun w hw b hb =>
    hext (analyticOnNhd_dupZeroDefect_left (hpos b hb)) (fun a ha => h1 a b ha hb) w hw
  have h3 := hext (analyticOnNhd_dupZeroDefect_right hx) (fun b hb => h2 x hx b hb) y hy
  unfold dupZeroDefect at h3
  linear_combination h3

/-! ### The addition theorem with a vanishing variable -/

/-- **Carlson's (9.7-17)**: for positive `x, y, λ, μ` with `λμ = xy`,
`R_F(x + λ, y + λ, λ) + R_F(x + μ, y + μ, μ) = (π/2) R_K(x, y)`. It is the addition theorem with
`z = 0`. -/
theorem carlsonRF_add_carlsonRF_zero {x y l m : ℝ} (hx : 0 < x) (hy : 0 < y) (hl : 0 < l)
    (hm : 0 < m) (hlm : l * m = x * y) :
    carlsonRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) (l : ℂ) +
      carlsonRF ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) (m : ℂ) =
        (π / 2 : ℂ) * carlsonRK (x : ℂ) (y : ℂ) := by
  -- `μ(z)`, the partner of `λ` for the variables `(x, y, z)`
  set μ : ℝ → ℝ := fun z => ((x * y + x * z + y * z) * l + 2 * (x * y * z) +
    2 * (√(x * y * z) * √(l ^ 3 + (x + y + z) * l ^ 2 + (x * y + x * z + y * z) * l +
      x * y * z))) / l ^ 2
  have hμc : Continuous μ := by fun_prop
  have hμ0 : μ 0 = m := by
    simp only [μ]
    field_simp
    simp
    nlinarith
  have hμt : Tendsto μ (𝓝[>] 0) (𝓝 m) := by
    rw [← hμ0]; exact (hμc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hadd : ∀ z : ℝ, 0 < z → carlsonRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
      carlsonRF ((x + μ z : ℝ) : ℂ) ((y + μ z : ℝ) : ℂ) ((z + μ z : ℝ) : ℂ) =
        carlsonRF (x : ℂ) (y : ℂ) (z : ℂ) := by
    intro z hz
    have he : 0 ≤ x + y + z := by positivity
    have hf : 0 ≤ x * y + x * z + y * z := by positivity
    have hg : 0 < x * y * z := by positivity
    obtain ⟨hμpos, hpos, hQ⟩ := eulerMu_spec he hf hg hl
    have hμe : eulerMu (x + y + z) (x * y + x * z + y * z) (x * y * z) l = μ z := rfl
    rw [hμe] at hμpos hpos hQ
    refine carlsonRF_add_carlsonRF hx hy hz hl hμpos ?_
    have hsum : 0 ≤ l + μ z + (x + y + z) := by positivity
    rw [show l * μ z - x * y - x * z - y * z = l * μ z - (x * y + x * z + y * z) by ring,
      ← Real.sqrt_sq hpos.le, hQ, show 4 * (x * y * z) * (l + μ z + (x + y + z)) =
        2 ^ 2 * ((x * y * z) * (l + μ z + (x + y + z))) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num), Real.sqrt_mul hg.le,
      show l + μ z + (x + y + z) = l + μ z + x + y + z by ring]
    ring
  have hleft : Tendsto (fun z : ℝ =>
      carlsonRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) ((z + l : ℝ) : ℂ) +
      carlsonRF ((x + μ z : ℝ) : ℂ) ((y + μ z : ℝ) : ℂ) ((z + μ z : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (carlsonRF ((x + l : ℝ) : ℂ) ((y + l : ℝ) : ℂ) (l : ℂ) +
        carlsonRF ((x + m : ℝ) : ℂ) ((y + m : ℝ) : ℂ) (m : ℂ))) := by
    have hz : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    refine Tendsto.add ?_ ?_
    · exact tendsto_carlsonRF_ofReal (by positivity) (by positivity) hl tendsto_const_nhds
        tendsto_const_nhds (by simpa using hz.add_const l)
    · exact tendsto_carlsonRF_ofReal (by positivity) (by positivity) hm (hμt.const_add x)
        (hμt.const_add y) (by simpa using hz.add hμt)
  have hright : Tendsto (fun z : ℝ => carlsonRF (x : ℂ) (y : ℂ) (z : ℂ)) (𝓝[>] 0)
      (𝓝 ((π / 2 : ℂ) * carlsonRK x y)) :=
    (tendsto_carlsonRF_zero (by simpa using hx) (by simpa using hy)).comp
      tendsto_ofReal_nhdsGT_zero
  refine tendsto_nhds_unique hleft (hright.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with z (hz : 0 < z)
  exact (hadd z hz).symm

end Carlson
