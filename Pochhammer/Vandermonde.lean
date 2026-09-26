/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.Binomial

/-!
# Chu–Vandermonde identities for the ascending Pochhammer polynomial

The ascending Pochhammer polynomial satisfies binary and multinomial Chu–Vandermonde identities
over a commutative semiring. The binary formulas are given using polynomial evaluation and
scalar evaluation, and the finite-family formula sums over multi-indices of prescribed total
degree. These complement Mathlib’s falling-factorial identities in
`Mathlib.RingTheory.Binomial`.

## Main results

* `ascPochhammer_eval_add`: **Chu–Vandermonde identity** for the rising factorial.
* `ascPochhammer_smeval_add`: Smeval form of `ascPochhammer_eval_add`, matching the statement
  shape of `Ring.descPochhammer_smeval_add`.
* `ascPochhammer_eval_add_sum_range`: Range form of `ascPochhammer_eval_add`.
* `ascPochhammer_eval_sum`: **Multinomial Chu–Vandermonde identity** for the rising factorial.

## References

* `Mathlib.Algebra.Order.Antidiag.Pi`: formal background used by this module.
* `Mathlib.Data.Nat.Choose.Multinomial`: formal background used by this module.
* `Mathlib.RingTheory.Binomial`: formal background used by this module.
-/

open Finset Polynomial

public noncomputable section

variable {R : Type*}

/-- **Chu–Vandermonde identity** for the rising factorial.

This is the ascending counterpart of `Ring.descPochhammer_smeval_add`.  In Appell's notation
it is \((r+s,k)=\sum_m \binom{k}{m}(r,m)(s,k-m)\). -/
theorem ascPochhammer_eval_add [CommSemiring R] (r s : R) (k : ℕ) :
    (ascPochhammer R k).eval (r + s) =
      ∑ ij ∈ antidiagonal k,
        (k.choose ij.1 : R) *
          ((ascPochhammer R ij.1).eval r * (ascPochhammer R ij.2).eval s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ih,
      sum_antidiagonal_choose_succ_mul
        (fun i j ↦ (ascPochhammer R i).eval r * (ascPochhammer R j).eval s),
      ← sum_add_distrib, sum_mul]
    refine sum_congr rfl fun ij hij ↦ ?_
    have hijsum : ij.1 + ij.2 = k := mem_antidiagonal.mp hij
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ← hijsum, Nat.choose_symm_add]
    push_cast
    ring

/-- Smeval form of `ascPochhammer_eval_add`, matching the statement shape of
`Ring.descPochhammer_smeval_add`. -/
theorem ascPochhammer_smeval_add [CommSemiring R] (r s : R) (k : ℕ) :
    (ascPochhammer ℕ k).smeval (r + s) =
      ∑ ij ∈ antidiagonal k,
        (k.choose ij.1 : R) *
          ((ascPochhammer ℕ ij.1).smeval r * (ascPochhammer ℕ ij.2).smeval s) := by
  simpa [ascPochhammer_smeval_eq_eval] using ascPochhammer_eval_add r s k

/-- Range form of `ascPochhammer_eval_add`. -/
theorem ascPochhammer_eval_add_sum_range [CommSemiring R] (r s : R) (k : ℕ) :
    (ascPochhammer R k).eval (r + s) =
      ∑ m ∈ range (k + 1),
        (k.choose m : R) *
          ((ascPochhammer R m).eval r * (ascPochhammer R (k - m)).eval s) := by
  rw [ascPochhammer_eval_add, Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- **Multinomial Chu–Vandermonde identity** for the rising factorial.

In Appell's notation this is \((∑_i b_i,\,n)=\sum \mathrm{multinomial}(m)\,∏_i (b_i,m_i)\),
summed over multi-indices with \(|m|=n\). -/
theorem ascPochhammer_eval_sum [CommSemiring R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (b : ι → R) (n : ℕ) :
    (ascPochhammer R n).eval (∑ i ∈ s, b i) =
      ∑ m ∈ piAntidiag s n,
        (Nat.multinomial s m : R) *
          ∏ i ∈ s, (ascPochhammer R (m i)).eval (b i) := by
  induction s using Finset.cons_induction generalizing n with
  | empty => cases n <;> simp
  | cons a s ha ih =>
    rw [sum_cons, ascPochhammer_eval_add, piAntidiag_cons ha, sum_disjiUnion]
    refine sum_congr rfl fun p hp ↦ ?_
    have hp' : p.1 + p.2 = n := mem_antidiagonal.mp hp
    simp only [sum_map, addRightEmbedding_apply, Pi.add_apply]
    rw [ih]
    simp_rw [mul_sum]
    refine sum_congr rfl fun m hm ↦ ?_
    have hma : m a = 0 := not_imp_comm.1 ((mem_piAntidiag.mp hm).2 a) ha
    have hms : ∑ i ∈ s, m i = p.2 := (mem_piAntidiag.mp hm).1
    set f : ι → ℕ := fun t ↦ m t + if t = a then p.1 else 0
    have hfa : f a = p.1 := by
      change m a + (if a = a then p.1 else 0) = p.1
      simp [hma]
    have hfs : ∀ t ∈ s, f t = m t := by
      intro t ht
      change m t + (if t = a then p.1 else 0) = m t
      simp [ne_of_mem_of_not_mem ht ha]
    have hmult : Nat.multinomial (s.cons a ha) f =
        n.choose p.1 * Nat.multinomial s m := by
      rw [Nat.multinomial_cons ha, hfa, sum_congr rfl hfs, hms, hp',
        Nat.multinomial_congr hfs]
    have hprod :
        ∏ i ∈ s.cons a ha, (ascPochhammer R (f i)).eval (b i) =
          (ascPochhammer R p.1).eval (b a) *
            ∏ i ∈ s, (ascPochhammer R (m i)).eval (b i) := by
      rw [prod_cons, hfa]
      congr 1
      exact prod_congr rfl fun i hi ↦ by rw [hfs i hi]
    change _ =
      (Nat.multinomial (s.cons a ha) f : R) *
        ∏ i ∈ s.cons a ha, (ascPochhammer R (f i)).eval (b i)
    rw [hmult, hprod, Nat.cast_mul]
    ring

end
