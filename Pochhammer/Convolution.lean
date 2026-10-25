/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Pochhammer.Vandermonde
public import ToMathlib.Algebra.Polynomial.PochhammerIdentities
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Finite Pochhammer convolutions

A binomially weighted three-index sum can be reassociated without divisions.
Together with Chu–Vandermonde this gives the finite coefficient transformation
underlying the Burchnall–Chaundy substitution for Appell F₄. All identities
retain exceptional parameters and hold over arbitrary commutative rings.
-/

open Finset Polynomial
public noncomputable section
variable {R : Type*}

/-- Reassociation of a binomially weighted three-index convolution. -/
theorem Finset.Nat.sum_antidiagonal_choose_assoc [CommSemiring R]
    (f : ℕ → ℕ → ℕ → R) (N : ℕ) :
    ∑ p ∈ antidiagonal N, (N.choose p.1 : R) *
        ∑ q ∈ antidiagonal p.2, (p.2.choose q.1 : R) * f p.1 q.1 q.2 =
      ∑ p ∈ antidiagonal N, (N.choose p.1 : R) *
        ∑ q ∈ antidiagonal p.1, (p.1.choose q.1 : R) * f q.1 q.2 p.2 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  let e : (Σ _ : ℕ × ℕ, ℕ × ℕ) → (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
    fun v => ⟨(v.1.1 + v.2.1, v.2.2), (v.1.1, v.2.1)⟩
  let j : (Σ _ : ℕ × ℕ, ℕ × ℕ) → (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
    fun v => ⟨(v.2.1, v.2.2 + v.1.2), (v.2.2, v.1.2)⟩
  apply Finset.sum_nbij' e j
  · intro v hv
    simp only [Finset.mem_sigma, mem_antidiagonal] at hv ⊢
    dsimp [e]
    omega
  · intro v hv
    simp only [Finset.mem_sigma, mem_antidiagonal] at hv ⊢
    dsimp [j]
    omega
  · intro v hv
    simp only [Finset.mem_sigma, mem_antidiagonal] at hv
    apply Sigma.ext
    · apply Prod.ext <;> dsimp [j, e]
      exact hv.2
    · exact heq_of_eq rfl
  · intro v hv
    simp only [Finset.mem_sigma, mem_antidiagonal] at hv
    apply Sigma.ext
    · apply Prod.ext <;> dsimp [j, e]
      exact hv.2
    · exact heq_of_eq rfl
  · rintro ⟨⟨k, l⟩, ⟨s, t⟩⟩ hv
    simp only [Finset.mem_sigma, mem_antidiagonal] at hv
    dsimp only [e]
    have hc : N.choose k * l.choose s = N.choose (k + s) * (k + s).choose k := by
      simpa only [Nat.add_sub_cancel_left, show N - k = l by omega] using
        (Nat.choose_mul (n := N) (k := k + s) (Nat.le_add_right k s)).symm
    rw [← mul_assoc, ← Nat.cast_mul, hc, Nat.cast_mul, mul_assoc]

/-- A shifted product of rising factorials expanded in a common rising-factorial basis. -/
theorem ascPochhammer_eval_mul_shift_eq_sum [CommRing R] (b : R) (m k n : ℕ) :
    (ascPochhammer R m).eval b * (ascPochhammer R n).eval (b + k) =
      ∑ p ∈ antidiagonal n, (n.choose p.1 : R) *
        (ascPochhammer R p.1).eval ((k : R) - m) *
          (ascPochhammer R (m + p.2)).eval b := by
  have h := ascPochhammer_eval_add ((k : R) - m) (b + m) n
  rw [show (k : R) - m + (b + m) = b + k by ring] at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [ascPochhammer_add_eval]
  ring

/-- One expansion step in the finite Burchnall–Chaundy coefficient transformation. -/
private theorem pochhammer_convolution_step [CommRing R] (a b A : R) (M k n : ℕ) :
    (ascPochhammer R k).eval (-(M : R)) * (ascPochhammer R (M + n)).eval a *
        (ascPochhammer R k).eval A *
        ((ascPochhammer R M).eval b * (ascPochhammer R n).eval (b + k)) =
      ∑ q ∈ antidiagonal n, (n.choose q.1 : R) *
        ((ascPochhammer R (k + q.1)).eval (-(M : R)) *
          (ascPochhammer R (M + q.2)).eval a * (ascPochhammer R (M + q.2)).eval b *
          (ascPochhammer R k).eval A * (ascPochhammer R q.1).eval (a + (M + q.2 : ℕ))) := by
  rw [ascPochhammer_eval_mul_shift_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hneg : (ascPochhammer R k).eval (-(M : R)) *
      (ascPochhammer R q.1).eval ((k : R) - M) =
        (ascPochhammer R (k + q.1)).eval (-(M : R)) := by
    rw [ascPochhammer_add_eval]
    congr 2
    ring
  have ha : (ascPochhammer R (M + n)).eval a =
      (ascPochhammer R (M + q.2)).eval a *
        (ascPochhammer R q.1).eval (a + (M + q.2 : ℕ)) := by
    rw [← ascPochhammer_add_eval]
    congr 2
    have h := mem_antidiagonal.mp hq
    omega
  rw [ha, ← hneg]
  ring

/-- The finite Burchnall–Chaundy coefficient transformation, with all parameter denominators
cleared. It follows from two Chu–Vandermonde expansions and applies in every commutative ring. -/
theorem ascPochhammer_eval_burchnallChaundy [CommRing R] (a b A : R) (M N : ℕ) :
    ∑ p ∈ antidiagonal N, (N.choose p.1 : R) *
        (ascPochhammer R p.1).eval (-(M : R)) *
        (ascPochhammer R (M + p.2)).eval a * (ascPochhammer R p.1).eval A *
        ((ascPochhammer R M).eval b * (ascPochhammer R p.2).eval (b + p.1)) =
      ∑ p ∈ antidiagonal N, (N.choose p.1 : R) *
        (ascPochhammer R p.1).eval (-(M : R)) *
        (ascPochhammer R (M + p.2)).eval a * (ascPochhammer R (M + p.2)).eval b *
        (ascPochhammer R p.1).eval (A + a + (M + p.2 : ℕ)) := by
  let F : ℕ → ℕ → ℕ → R := fun k j t =>
    (ascPochhammer R (k + j)).eval (-(M : R)) *
      (ascPochhammer R (M + t)).eval a * (ascPochhammer R (M + t)).eval b *
      (ascPochhammer R k).eval A * (ascPochhammer R j).eval (a + (M + t : ℕ))
  calc
    _ = ∑ p ∈ antidiagonal N, (N.choose p.1 : R) *
        ∑ q ∈ antidiagonal p.2, (p.2.choose q.1 : R) * F p.1 q.1 q.2 := by
      apply Finset.sum_congr rfl
      intro p _
      calc
        _ = (N.choose p.1 : R) *
            ((ascPochhammer R p.1).eval (-(M : R)) *
              (ascPochhammer R (M + p.2)).eval a * (ascPochhammer R p.1).eval A *
              ((ascPochhammer R M).eval b * (ascPochhammer R p.2).eval (b + p.1))) := by ring
        _ = _ := by rw [pochhammer_convolution_step]
    _ = ∑ p ∈ antidiagonal N, (N.choose p.1 : R) *
        ∑ q ∈ antidiagonal p.1, (p.1.choose q.1 : R) * F q.1 q.2 p.2 :=
      Finset.Nat.sum_antidiagonal_choose_assoc F N
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      have hsum : ∑ q ∈ antidiagonal p.1, (p.1.choose q.1 : R) * F q.1 q.2 p.2 =
          ((ascPochhammer R p.1).eval (-(M : R)) *
            (ascPochhammer R (M + p.2)).eval a * (ascPochhammer R (M + p.2)).eval b) *
              (ascPochhammer R p.1).eval (A + (a + (M + p.2 : ℕ))) := by
        rw [ascPochhammer_eval_add, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        dsimp only [F]
        rw [mem_antidiagonal.mp hq]
        ring
      rw [hsum]
      simp only [← add_assoc]
      ring

/-- Reflected form of the finite Burchnall–Chaundy transformation, with no parameter
exclusions or divisions by Pochhammer factors. -/
theorem ascPochhammer_eval_burchnallChaundy_reflect [CommRing R] (a b A : R) (M N : ℕ) :
    ∑ p ∈ antidiagonal N, (N.choose p.1 : R) *
        (ascPochhammer R p.1).eval (-(M : R)) *
        (ascPochhammer R (M + p.2)).eval a * (ascPochhammer R p.1).eval A *
        ((ascPochhammer R M).eval b * (ascPochhammer R p.2).eval (b + p.1)) =
      ∑ p ∈ antidiagonal N, (N.choose p.1 : R) *
        (ascPochhammer R p.1).eval (-(M : R)) *
        (ascPochhammer R (M + p.2)).eval a * (ascPochhammer R (M + p.2)).eval b *
        (-1 : R) ^ p.1 * (ascPochhammer R p.1).eval (1 - a - A - M - N) := by
  rw [ascPochhammer_eval_burchnallChaundy]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := mem_antidiagonal.mp hp
  have harg : A + a + (M + p.2 : ℕ) = 1 - (1 - a - A - M - N) - (p.1 : R) := by
    rw [← hdeg]
    push_cast
    ring
  rw [harg, ascPochhammer_eval_reflect]
  ring

end
