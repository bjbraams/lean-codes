/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Algebra.Polynomial.PochhammerIdentities
import Mathlib.Tactic.FieldSimp

/-!
# Integer-order rising factorials

Carlson (1977), Definition 2.2-1 and Theorem 2.2-2. Natural orders are polynomial
evaluations, including their zeros. Negative orders are reciprocals of the corresponding
shifted polynomial; `intPochhammerDefined` records precisely when its denominator is
nonzero. Thus the API does not impose Gamma regularity on positive orders.

The algebraic proofs extend Mathlib's natural-order Pochhammer product identities.
-/

open Polynomial

public noncomputable section

variable {R : Type*} [Field R]

/-- Rising factorial with an arbitrary integer order. -/
def intPochhammer (a : R) (n : ℤ) : R :=
  if 0 ≤ n then (ascPochhammer R n.toNat).eval a
  else ((ascPochhammer R (-n).toNat).eval (a + n))⁻¹

/-- The integer-order rising factorial has no pole. Natural orders are always defined. -/
def intPochhammerDefined (a : R) (n : ℤ) : Prop :=
  0 ≤ n ∨ (ascPochhammer R (-n).toNat).eval (a + n) ≠ 0

/-- Natural orders agree with Mathlib's ascending Pochhammer polynomial. -/
@[simp] theorem intPochhammer_natCast (a : R) (n : ℕ) :
    intPochhammer a (n : ℤ) = (ascPochhammer R n).eval a := by
  simp [intPochhammer]

/-- Negative natural orders are reciprocals of the shifted rising factorial. -/
theorem intPochhammer_neg_natCast (a : R) (n : ℕ) :
    intPochhammer a (-(n : ℤ)) = ((ascPochhammer R n).eval (a - n))⁻¹ := by
  cases n with
  | zero => simp [intPochhammer]
  | succ n =>
    rw [intPochhammer, ite_eq_right (by omega)]
    simp only [neg_neg, Int.toNat_natCast, Int.cast_neg, Int.cast_natCast, sub_eq_add_neg]

/-- Every natural-order rising factorial is defined, including at its zeros. -/
@[simp] theorem intPochhammerDefined_natCast (a : R) (n : ℕ) :
    intPochhammerDefined a (n : ℤ) := Or.inl (Int.natCast_nonneg n)

/-- Negative orders are defined exactly when the denominator is nonzero. -/
@[simp] theorem intPochhammerDefined_neg_natCast (a : R) (n : ℕ) :
    intPochhammerDefined a (-(n : ℤ)) ↔ (ascPochhammer R n).eval (a - n) ≠ 0 := by
  cases n with
  | zero => simp [intPochhammerDefined]
  | succ n =>
    simp only [intPochhammerDefined, show ¬0 ≤ -((n + 1 : ℕ) : ℤ) by omega,
      false_or, neg_neg, Int.toNat_natCast, Int.cast_neg, Int.cast_natCast, sub_eq_add_neg]

/-- The order-zero value is one at every parameter. -/
@[simp] theorem intPochhammer_zero (a : R) : intPochhammer a 0 = 1 := by
  simpa using intPochhammer_natCast a 0

/-- The order-one value is the parameter. -/
@[simp] theorem intPochhammer_one (a : R) : intPochhammer a 1 = a := by
  simpa using intPochhammer_natCast a 1

/-- Negative orders add by multiplication of reciprocal finite products. -/
private theorem intPochhammer_add_neg_neg (a : R) (m n : ℕ) :
    intPochhammer a (-((m : ℤ) + n)) =
      intPochhammer a (-(m : ℤ)) * intPochhammer (a - m) (-(n : ℤ)) := by
  rw [← Nat.cast_add, intPochhammer_neg_natCast, intPochhammer_neg_natCast,
    intPochhammer_neg_natCast]
  have he := ascPochhammer_add_eval (a - (m + n : ℕ)) n m
  have ha : a - (m + n : ℕ) + n = a - m := by push_cast; ring
  rw [Nat.add_comm n m, ha] at he
  rw [he, mul_inv_rev]
  congr 2
  push_cast
  ring

/-- **Carlson (2.2-5).** Addition for arbitrary integer orders, whenever the
negative-order factors on the two sides have no poles. -/
theorem intPochhammer_add (a : R) (m n : ℤ)
    (hm : intPochhammerDefined a m)
    (hn : intPochhammerDefined (a + m) n)
    (_hmn : intPochhammerDefined a (m + n)) :
    intPochhammer a (m + n) = intPochhammer a m * intPochhammer (a + m) n := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [← Nat.cast_add, intPochhammer_natCast, intPochhammer_natCast,
        intPochhammer_natCast]
      simpa only [Int.cast_natCast] using ascPochhammer_add_eval a m n
    · rw [intPochhammerDefined_neg_natCast] at hn
      rcases le_total n m with h | h
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
        have hi : ((n + k : ℕ) : ℤ) + -(n : ℤ) = k := by omega
        have ha : a + ((n + k : ℕ) : ℤ) - n = a + k := by push_cast; ring
        rw [hi, intPochhammer_natCast, intPochhammer_natCast,
          intPochhammer_neg_natCast, ha]
        rw [ha] at hn
        rw [Nat.add_comm n k, ascPochhammer_add_eval a k n]
        exact (mul_inv_cancel_right₀ hn _).symm
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
        have hi : (m : ℤ) + -((m + k : ℕ) : ℤ) = -(k : ℤ) := by omega
        have ha : a + (m : ℤ) - (m + k : ℕ) = a - k := by push_cast; ring
        rw [hi, intPochhammer_natCast, intPochhammer_neg_natCast,
          intPochhammer_neg_natCast, ha]
        rw [ha] at hn
        have he := ascPochhammer_add_eval (a - k) k m
        rw [show a - (k : R) + k = a by ring, Nat.add_comm k m] at he
        rw [he] at hn ⊢
        have hz := (mul_ne_zero_iff.mp hn).2
        field_simp
  · obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [intPochhammerDefined_neg_natCast] at hm
      rcases le_total m n with h | h
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
        have hi : -(m : ℤ) + ((m + k : ℕ) : ℤ) = k := by omega
        rw [hi, intPochhammer_natCast, intPochhammer_neg_natCast,
          intPochhammer_natCast]
        simp only [Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg]
        rw [ascPochhammer_add_eval (a - m) m k, show a - (m : R) + m = a by ring]
        exact (inv_mul_cancel_left₀ hm _).symm
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
        have hi : -((n + k : ℕ) : ℤ) + (n : ℤ) = -(k : ℤ) := by omega
        rw [hi, intPochhammer_neg_natCast, intPochhammer_neg_natCast,
          intPochhammer_natCast]
        simp only [Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg]
        have he := ascPochhammer_add_eval (a - (n + k : ℕ)) n k
        rw [show a - (n + k : ℕ) + n = a - k by push_cast; ring] at he
        rw [he] at hm ⊢
        have hz := (mul_ne_zero_iff.mp hm).1
        field_simp
    · have hi : -(m : ℤ) + -(n : ℤ) = -((m : ℤ) + n) := by ring
      simpa only [hi, Int.cast_neg, Int.cast_natCast, ← sub_eq_add_neg] using
        intPochhammer_add_neg_neg a m n

/-- **Carlson (2.2-6).** Reflection for arbitrary integer orders. The totalized
identity also holds at poles, while `intPochhammerDefined` records the book's domain. -/
theorem intPochhammer_neg (a : R) (n : ℤ) :
    intPochhammer a (-n) = (-1 : R) ^ n / intPochhammer (1 - a) n := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [intPochhammer_neg_natCast, intPochhammer_natCast, zpow_natCast]
    have he := ascPochhammer_eval_reflect (1 - a) n
    rw [show 1 - (1 - a) - (n : R) = a - n by ring] at he
    rw [he, mul_inv_rev, ← inv_pow, inv_neg_one]
    ring
  · rw [neg_neg, intPochhammer_natCast, intPochhammer_neg_natCast,
      zpow_neg, zpow_natCast, div_inv_eq_mul, ← inv_pow, inv_neg_one,
      ascPochhammer_eval_reflect]
    rw [← mul_assoc, ← mul_pow]
    simp

/-- **Carlson (2.2-7).** Duplication for arbitrary integer orders, with the
same totalization convention as reflection. -/
theorem intPochhammer_double [CharZero R] (a : R) (n : ℤ) :
    intPochhammer (2 * a) (2 * n) =
      (4 : R) ^ n * intPochhammer a n * intPochhammer (a + 1 / 2) n := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [show (2 : ℤ) * n = ((2 * n : ℕ) : ℤ) by omega,
      intPochhammer_natCast, intPochhammer_natCast, intPochhammer_natCast, zpow_natCast]
    exact ascPochhammer_eval_double a n
  · rw [show (2 : ℤ) * -(n : ℤ) = -((2 * n : ℕ) : ℤ) by omega,
      intPochhammer_neg_natCast, intPochhammer_neg_natCast, intPochhammer_neg_natCast,
      zpow_neg, zpow_natCast]
    rw [show 2 * a - (2 * n : ℕ) = 2 * (a - n) by push_cast; ring,
      ascPochhammer_eval_double]
    simp only [mul_inv_rev]
    rw [show a - (n : R) + 1 / 2 = a + 1 / 2 - n by ring]
    ring

end
