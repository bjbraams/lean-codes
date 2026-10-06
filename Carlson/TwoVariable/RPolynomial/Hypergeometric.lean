/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.RPolynomial
public import Carlson.TwoVariable.PolynomialDifferential
public import Carlson.RPolynomial.NumeratorBinomial
public import Pochhammer.Identities
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Carlson.RPolynomial.Generating

/-!
# Two-variable R-polynomials as terminating Gauss functions

Carlson's identifications of two-variable R-polynomials with terminating Gauss functions
(Mathlib's `ordinaryHypergeometric`), in division-free numerator form
`Nₙ(β, β'; x, y) = (β + β')ₙ Rₙ(β, β'; x, y)`, together with the exercises of Chapter 6 that
follow from them.

## Main results

* `Carlson.TwoVariable.carlsonRPolynomialNumerator₂_eq_hypergeometric`: Exercise 6.2-5.
* `Carlson.TwoVariable.sum_ascPochhammer_div_factorial_mul_pow`: Exercise 6.2-1.
* `Carlson.TwoVariable.natCast_succ_mul_carlsonRPolynomial₂_one_one`: Exercise 6.2-4.
* `Carlson.TwoVariable.ordinaryHypergeometric_neg_natCast_mul`: Exercise 6.4-1.
* The six `₂F₁` forms of Exercise 6.5-2: `carlsonRPolynomialNumerator₂_eq_hypergeometric`,
  `_eq_hypergeometric'`, `_eq_hypergeometric_div`, `_eq_hypergeometric_div'`,
  `_eq_hypergeometric_sub`, `_eq_hypergeometric_sub'`.
* `Carlson.TwoVariable.ascPochhammer_mul_ordinaryHypergeometric_inv`,
  `ascPochhammer_mul_ordinaryHypergeometric_one_sub`: Exercise 6.5-3.
* `Carlson.TwoVariable.hasSum_ordinaryHypergeometric_neg_natCast`: Exercise 6.6-10.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 6.
-/

open Complex Finset
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- `(γ)ₙ = (γ)ₘ (γ + m)_(n-m)` for `m ≤ n`. -/
theorem ascPochhammer_eval_eq_mul_of_le (γ : ℂ) {m n : ℕ} (h : m ≤ n) :
    (ascPochhammer ℂ n).eval γ =
      (ascPochhammer ℂ m).eval γ * (ascPochhammer ℂ (n - m)).eval (γ + m) := by
  have := congrArg (Polynomial.eval γ) (ascPochhammer_mul ℂ m (n - m))
  rw [Nat.add_sub_cancel' h] at this
  simpa [Polynomial.eval_mul, Polynomial.eval_comp] using this.symm

/-- `(-n)ₘ = (-1)ᵐ m! (n choose m)`. -/
theorem ascPochhammer_eval_neg_natCast (n m : ℕ) :
    (ascPochhammer ℂ m).eval (-(n : ℂ)) = (-1) ^ m * ((m.factorial : ℂ) * (n.choose m : ℂ)) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast; ring

/-- A Gauss function with first parameter `-n` is a polynomial of degree at most `n`. -/
theorem ordinaryHypergeometric_neg_natCast (n : ℕ) (β γ w : ℂ) :
    ordinaryHypergeometric (-(n : ℂ)) β γ w = ∑ m ∈ range (n + 1),
      ((m.factorial : ℂ)⁻¹ * (ascPochhammer ℂ m).eval (-(n : ℂ)) * (ascPochhammer ℂ m).eval β *
        ((ascPochhammer ℂ m).eval γ)⁻¹) * w ^ m := by
  rw [ordinaryHypergeometric_eq_tsum]
  refine tsum_eq_sum fun m hm => ?_
  have hnm : n < m := by simpa using hm
  rw [(ascPochhammer_eval_eq_zero_iff m _).mpr ⟨n, hnm, by simp⟩]
  simp

/-- **Division-free form of a terminating Gauss function**: if `(γ)ₙ ≠ 0`,
`(γ)ₙ ₂F₁(-n, β; γ; w) = ∑ₘ (n choose m) (β)ₘ (γ + m)_(n-m) (-w)ᵐ`. -/
theorem ascPochhammer_mul_ordinaryHypergeometric (n : ℕ) (β γ w : ℂ)
    (hγ : (ascPochhammer ℂ n).eval γ ≠ 0) :
    (ascPochhammer ℂ n).eval γ * ordinaryHypergeometric (-(n : ℂ)) β γ w =
      ∑ m ∈ range (n + 1), (n.choose m : ℂ) * (ascPochhammer ℂ m).eval β *
        (ascPochhammer ℂ (n - m)).eval (γ + m) * (-w) ^ m := by
  rw [ordinaryHypergeometric_neg_natCast, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hsplit := ascPochhammer_eval_eq_mul_of_le γ hmn
  have hγm : (ascPochhammer ℂ m).eval γ ≠ 0 := fun h0 => hγ (by rw [hsplit, h0, zero_mul])
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  rw [hsplit, ascPochhammer_eval_neg_natCast, neg_pow]
  field_simp
  ring

/-- The reflected form: if `(1 - p - n)ₙ ≠ 0`,
`(p)ₙ ₂F₁(-n, β; 1 - p - n; w) = ∑ₘ (n choose m) (β)ₘ (p)_(n-m) wᵐ`. -/
theorem ascPochhammer_mul_ordinaryHypergeometric_reflect (n : ℕ) (β p w : ℂ)
    (hp : (ascPochhammer ℂ n).eval (1 - p - n) ≠ 0) :
    (ascPochhammer ℂ n).eval p * ordinaryHypergeometric (-(n : ℂ)) β (1 - p - n) w =
      ∑ m ∈ range (n + 1), (n.choose m : ℂ) * (ascPochhammer ℂ m).eval β *
        (ascPochhammer ℂ (n - m)).eval p * w ^ m := by
  have h := ascPochhammer_mul_ordinaryHypergeometric n β (1 - p - n) w hp
  rw [ascPochhammer_eval_reflect] at h
  have hsign : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hsign
  rw [← mul_assoc, h, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [show 1 - p - (n : ℂ) + m = 1 - p - ((n - m : ℕ) : ℂ) by push_cast [hmn]; ring,
    ascPochhammer_eval_reflect, neg_pow]
  have : ((-1 : ℂ)) ^ n = (-1) ^ (n - m) * (-1) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmn]
  rw [this]
  ring

/-- The two-node numerator as a sum over the first index. -/
theorem carlsonRPolynomialNumerator₂_eq_sum_range (n : ℕ) (b₀ b₁ x y : ℂ) :
    carlsonRPolynomialNumerator₂ n b₀ b₁ x y = ∑ m ∈ range (n + 1), (n.choose m : ℂ) *
      (ascPochhammer ℂ m).eval b₀ * (ascPochhammer ℂ (n - m)).eval b₁ * x ^ m * y ^ (n - m) :=
  Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (n.choose i : ℂ) *
    (ascPochhammer ℂ i).eval b₀ * (ascPochhammer ℂ j).eval b₁ * x ^ i * y ^ j) n

/-- **The binomial theorem for two-node numerators**, valid for all parameters. -/
theorem carlsonRPolynomialNumerator₂_add_const (n : ℕ) (b₀ b₁ x y a : ℂ) :
    carlsonRPolynomialNumerator₂ n b₀ b₁ (x + a) (y + a) =
      ∑ m ∈ range (n + 1), (n.choose m : ℂ) * a ^ (n - m) *
        (ascPochhammer ℂ (n - m)).eval (b₀ + b₁ + m) *
          carlsonRPolynomialNumerator₂ m b₀ b₁ x y := by
  have h := carlsonRPolynomialNumerator_add_const n a (pair b₀ b₁) (pair x y)
  have hz : (fun i => pair x y i + a) = pair (x + a) (y + a) := by
    funext i; fin_cases i <;> rfl
  rw [hz, carlsonRPolynomialNumerator_pair, sum_pair] at h
  simpa only [carlsonRPolynomialNumerator_pair] using h

/-- **Exercise 6.2-5, division-free form**:
`Nₙ(β, β'; x, y) = ∑ₘ (n choose m) (β)ₘ (β + β' + m)_(n-m) (x - y)ᵐ y^(n-m)`. -/
theorem carlsonRPolynomialNumerator₂_eq_sum_sub (n : ℕ) (β β' x y : ℂ) :
    carlsonRPolynomialNumerator₂ n β β' x y = ∑ m ∈ range (n + 1), (n.choose m : ℂ) *
      (ascPochhammer ℂ m).eval β * (ascPochhammer ℂ (n - m)).eval (β + β' + m) *
        (x - y) ^ m * y ^ (n - m) := by
  have h := carlsonRPolynomialNumerator₂_add_const n β β' (x - y) 0 y
  rw [sub_add_cancel, zero_add] at h
  rw [h]
  refine sum_congr rfl fun m _ => ?_
  rw [carlsonRPolynomialNumerator₂_zero_right]
  ring

/-- **Exercise 6.2-5**: `(c)ₙ Rₙ(β, c - β; x, y) = (c)ₙ yⁿ ₂F₁(-n, β; c; 1 - x/y)`, here in the
form `Nₙ(β, β'; x, y) = (β + β')ₙ yⁿ ₂F₁(-n, β; β + β'; 1 - x/y)` for `y ≠ 0` and
`(β + β')ₙ ≠ 0`. -/
theorem carlsonRPolynomialNumerator₂_eq_hypergeometric (n : ℕ) (β β' x : ℂ) {y : ℂ}
    (hy : y ≠ 0) (hc : (ascPochhammer ℂ n).eval (β + β') ≠ 0) :
    carlsonRPolynomialNumerator₂ n β β' x y = (ascPochhammer ℂ n).eval (β + β') * y ^ n *
      ordinaryHypergeometric (-(n : ℂ)) β (β + β') (1 - x / y) := by
  rw [mul_right_comm, ascPochhammer_mul_ordinaryHypergeometric n β _ _ hc, sum_mul,
    carlsonRPolynomialNumerator₂_eq_sum_sub]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hy' : y ^ n = y ^ m * y ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [hy', show -(1 - x / y) = (x - y) / y by field_simp; ring, div_pow]
  field_simp

/-- **Exercise 6.2-1** (a truncated binomial series):
`∑_{m ≤ n} (α)ₘ xᵐ / m! = Nₙ(α, 1; x, 1)/n! = (α + 1)ₙ Rₙ(α, 1; x, 1)/n!`. -/
theorem sum_ascPochhammer_div_factorial_mul_pow (n : ℕ) (α x : ℂ) :
    ∑ m ∈ range (n + 1), (ascPochhammer ℂ m).eval α / (m.factorial : ℂ) * x ^ m =
      carlsonRPolynomialNumerator₂ n α 1 x 1 / (n.factorial : ℂ) := by
  rw [carlsonRPolynomialNumerator₂_eq_sum_range, sum_div]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [ascPochhammer_eval_one, one_pow, mul_one, Nat.cast_choose ℂ hmn]
  have h1 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((n - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
  have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Exercise 6.2-4**: `(n + 1) Rₙ(1, 1; x, y) = xⁿ + xⁿ⁻¹y + ⋯ + yⁿ`, with
`Rₙ(1, 1; x, y) = Nₙ(1, 1; x, y)/(2)ₙ`. -/
theorem natCast_succ_mul_carlsonRPolynomial₂_one_one (n : ℕ) (x y : ℂ) :
    ((n : ℂ) + 1) * (carlsonRPolynomialNumerator₂ n 1 1 x y / (ascPochhammer ℂ n).eval 2) =
      ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) := by
  have h2 : (ascPochhammer ℂ n).eval (2 : ℂ) = ((n + 1).factorial : ℂ) := by
    have h := ascPochhammer_eval_eq_mul_of_le (1 : ℂ) (m := 1) (n := n + 1) (by omega)
    rw [ascPochhammer_eval_one, ascPochhammer_eval_one, Nat.add_sub_cancel] at h
    rw [h]; norm_num
  rw [h2, carlsonRPolynomialNumerator₂_eq_sum_range, sum_div, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [ascPochhammer_eval_one, ascPochhammer_eval_one, Nat.cast_choose ℂ hmn, Nat.factorial_succ]
  have h1 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((n - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
  have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  push_cast
  field_simp

/-- **Exercise 6.5-2, third form**: `Nₙ(β, β'; x, y) = (β')ₙ yⁿ ₂F₁(-n, β; 1 - β' - n; x/y)`,
if `y ≠ 0` and `(β')ₙ ≠ 0`. -/
theorem carlsonRPolynomialNumerator₂_eq_hypergeometric_div (n : ℕ) (β β' x : ℂ) {y : ℂ}
    (hy : y ≠ 0) (hβ' : (ascPochhammer ℂ n).eval (1 - β' - n) ≠ 0) :
    carlsonRPolynomialNumerator₂ n β β' x y = (ascPochhammer ℂ n).eval β' * y ^ n *
      ordinaryHypergeometric (-(n : ℂ)) β (1 - β' - n) (x / y) := by
  rw [mul_right_comm, ascPochhammer_mul_ordinaryHypergeometric_reflect n β β' _ hβ', sum_mul,
    carlsonRPolynomialNumerator₂_eq_sum_range]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hy' : y ^ n = y ^ m * y ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [hy', div_pow]
  field_simp

/-- **Exercise 6.5-2, fifth form**: `Nₙ(β, β'; x, y) =
(β')ₙ (y - x)ⁿ ₂F₁(-n, 1 - c - n; 1 - β' - n; x/(x - y))`, `c = β + β'`, if `x ≠ y` and
`(β')ₙ ≠ 0`. -/
theorem carlsonRPolynomialNumerator₂_eq_hypergeometric_sub (n : ℕ) (β β' : ℂ) {x y : ℂ}
    (hxy : x ≠ y) (hβ' : (ascPochhammer ℂ n).eval (1 - β' - n) ≠ 0) :
    carlsonRPolynomialNumerator₂ n β β' x y = (ascPochhammer ℂ n).eval β' * (y - x) ^ n *
      ordinaryHypergeometric (-(n : ℂ)) (1 - (β + β') - n) (1 - β' - n) (x / (x - y)) := by
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  rw [mul_right_comm, ascPochhammer_mul_ordinaryHypergeometric_reflect n _ β' _ hβ', sum_mul,
    ← carlsonRPolynomialNumerator₂_swap, carlsonRPolynomialNumerator₂_eq_sum_sub,
    ← sum_range_reflect]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [show n + 1 - 1 - m = n - m by omega, Nat.sub_sub_self hmn, Nat.choose_symm hmn,
    show 1 - (β + β') - (n : ℂ) = 1 - (β + β' + ((n - m : ℕ) : ℂ)) - m by
      push_cast [hmn]; ring, ascPochhammer_eval_reflect, add_comm β' β]
  have hpow : (y - x) ^ n = (y - x) ^ (n - m) * (y - x) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmn]
  rw [hpow, div_pow, show (y - x) ^ m = (-1) ^ m * (x - y) ^ m by rw [← mul_pow]; ring]
  field_simp
  rw [show (((-1 : ℂ)) ^ m) ^ 2 = 1 by rw [← pow_mul, pow_mul']; norm_num]
  ring

/-- **Exercise 6.4-1**: if `(γ)ₙ ≠ 0`,
`₂F₁(-n, β; γ; xy) = ∑ₘ (n choose m) xᵐ (1 - x)^(n-m) ₂F₁(-m, β; γ; y)`. -/
theorem ordinaryHypergeometric_neg_natCast_mul (n : ℕ) (β γ x y : ℂ)
    (hγ : (ascPochhammer ℂ n).eval γ ≠ 0) :
    ordinaryHypergeometric (-(n : ℂ)) β γ (x * y) = ∑ m ∈ range (n + 1),
      (n.choose m : ℂ) * x ^ m * (1 - x) ^ (n - m) * ordinaryHypergeometric (-(m : ℂ)) β γ y := by
  have hγ' : (ascPochhammer ℂ n).eval (β + (γ - β)) ≠ 0 := by rwa [add_sub_cancel]
  have hF (k : ℕ) (w : ℂ) (hk : (ascPochhammer ℂ k).eval γ ≠ 0) :
      carlsonRPolynomialNumerator₂ k β (γ - β) (1 - w) 1 =
        (ascPochhammer ℂ k).eval γ * ordinaryHypergeometric (-(k : ℂ)) β γ w := by
    have := carlsonRPolynomialNumerator₂_eq_hypergeometric k β (γ - β) (1 - w) one_ne_zero
      (by rwa [add_sub_cancel])
    simpa [add_sub_cancel] using this
  apply mul_left_cancel₀ hγ
  rw [← hF n (x * y) hγ]
  have hshift := carlsonRPolynomialNumerator₂_add_const n β (γ - β) (x * (1 - y)) x (1 - x)
  rw [show x * (1 - y) + (1 - x) = 1 - x * y by ring, show x + (1 - x) = 1 by ring] at hshift
  rw [hshift, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hsplit := ascPochhammer_eval_eq_mul_of_le γ hmn
  have hγm : (ascPochhammer ℂ m).eval γ ≠ 0 := fun h0 => hγ (by rw [hsplit, h0, zero_mul])
  have hs := carlsonRPolynomialNumerator₂_smul m β (γ - β) x (1 - y) 1
  rw [mul_one] at hs
  rw [hs, hF m y hγm, add_sub_cancel, hsplit]
  ring

/-- **Exercise 6.5-2, second form**: `Nₙ(β, β'; x, y) = (β + β')ₙ xⁿ ₂F₁(-n, β'; β + β'; 1 - y/x)`
for `x ≠ 0` and `(β + β')ₙ ≠ 0`. -/
theorem carlsonRPolynomialNumerator₂_eq_hypergeometric' (n : ℕ) (β β' y : ℂ) {x : ℂ}
    (hx : x ≠ 0) (hc : (ascPochhammer ℂ n).eval (β + β') ≠ 0) :
    carlsonRPolynomialNumerator₂ n β β' x y = (ascPochhammer ℂ n).eval (β + β') * x ^ n *
      ordinaryHypergeometric (-(n : ℂ)) β' (β + β') (1 - y / x) := by
  rw [← carlsonRPolynomialNumerator₂_swap, add_comm β β']
  exact carlsonRPolynomialNumerator₂_eq_hypergeometric n β' β y hx (by rwa [add_comm])

/-- **Exercise 6.5-2, fourth form**: `Nₙ(β, β'; x, y) = (β)ₙ xⁿ ₂F₁(-n, β'; 1 - β - n; y/x)`
for `x ≠ 0` and `(β)ₙ ≠ 0`. -/
theorem carlsonRPolynomialNumerator₂_eq_hypergeometric_div' (n : ℕ) (β β' y : ℂ) {x : ℂ}
    (hx : x ≠ 0) (hβ : (ascPochhammer ℂ n).eval (1 - β - n) ≠ 0) :
    carlsonRPolynomialNumerator₂ n β β' x y = (ascPochhammer ℂ n).eval β * x ^ n *
      ordinaryHypergeometric (-(n : ℂ)) β' (1 - β - n) (y / x) := by
  rw [← carlsonRPolynomialNumerator₂_swap]
  exact carlsonRPolynomialNumerator₂_eq_hypergeometric_div n β' β y hx hβ

/-- **Exercise 6.5-2, sixth form**: `Nₙ(β, β'; x, y) =
(β)ₙ (x - y)ⁿ ₂F₁(-n, 1 - c - n; 1 - β - n; y/(y - x))` for `x ≠ y` and `(β)ₙ ≠ 0`. -/
theorem carlsonRPolynomialNumerator₂_eq_hypergeometric_sub' (n : ℕ) (β β' : ℂ) {x y : ℂ}
    (hxy : x ≠ y) (hβ : (ascPochhammer ℂ n).eval (1 - β - n) ≠ 0) :
    carlsonRPolynomialNumerator₂ n β β' x y = (ascPochhammer ℂ n).eval β * (x - y) ^ n *
      ordinaryHypergeometric (-(n : ℂ)) (1 - (β + β') - n) (1 - β - n) (y / (y - x)) := by
  rw [← carlsonRPolynomialNumerator₂_swap, add_comm β β']
  exact carlsonRPolynomialNumerator₂_eq_hypergeometric_sub n β' β (Ne.symm hxy) hβ

/-- **Exercise 6.5-3, second relation**: if `(c)ₙ ≠ 0` and `(c - β)ₙ ≠ 0`,
`(c)ₙ ₂F₁(-n, β; c; x) = (c - β)ₙ ₂F₁(-n, β; 1 - c + β - n; 1 - x)`. -/
theorem ascPochhammer_mul_ordinaryHypergeometric_one_sub (n : ℕ) (β c x : ℂ)
    (hc : (ascPochhammer ℂ n).eval c ≠ 0)
    (hcβ : (ascPochhammer ℂ n).eval (1 - (c - β) - n) ≠ 0) :
    (ascPochhammer ℂ n).eval c * ordinaryHypergeometric (-(n : ℂ)) β c x =
      (ascPochhammer ℂ n).eval (c - β) *
        ordinaryHypergeometric (-(n : ℂ)) β (1 - c + β - n) (1 - x) := by
  have h1 := carlsonRPolynomialNumerator₂_eq_hypergeometric n β (c - β) (1 - x) one_ne_zero
    (by rwa [add_sub_cancel])
  have h2 := carlsonRPolynomialNumerator₂_eq_hypergeometric_div n β (c - β) (1 - x)
    one_ne_zero hcβ
  rw [add_sub_cancel, one_pow, mul_one, div_one, sub_sub_cancel] at h1
  rw [one_pow, mul_one, div_one, show 1 - (c - β) - (n : ℂ) = 1 - c + β - n by ring] at h2
  rw [← h1, h2]

/-- **Exercise 6.5-3, first relation**: if `x ≠ 0`, `(c)ₙ ≠ 0` and `(β)ₙ ≠ 0`,
`(c)ₙ ₂F₁(-n, β; c; x) = (β)ₙ (-x)ⁿ ₂F₁(-n, 1 - c - n; 1 - β - n; 1/x)`. -/
theorem ascPochhammer_mul_ordinaryHypergeometric_inv (n : ℕ) (β c : ℂ) {x : ℂ} (hx : x ≠ 0)
    (hc : (ascPochhammer ℂ n).eval c ≠ 0) (hβ : (ascPochhammer ℂ n).eval (1 - β - n) ≠ 0) :
    (ascPochhammer ℂ n).eval c * ordinaryHypergeometric (-(n : ℂ)) β c x =
      (ascPochhammer ℂ n).eval β * (-x) ^ n *
        ordinaryHypergeometric (-(n : ℂ)) (1 - c - n) (1 - β - n) (1 / x) := by
  have h1 := carlsonRPolynomialNumerator₂_eq_hypergeometric n β (c - β) (1 - x) one_ne_zero
    (by rwa [add_sub_cancel])
  have h2 := carlsonRPolynomialNumerator₂_eq_hypergeometric_sub' n β (c - β)
    (x := 1 - x) (y := 1) (by simpa using hx) hβ
  rw [add_sub_cancel, one_pow, mul_one, div_one, sub_sub_cancel] at h1
  rw [add_sub_cancel, show (1 : ℂ) - x - 1 = -x by ring,
    show (1 : ℂ) / (1 - (1 - x)) = 1 / x by ring] at h2
  rw [← h1, h2]

/-- **Exercise 6.6-10** (generating relation of the terminating Gauss functions): if `γ` is not a
nonpositive integer, `‖t‖ < 1` and `‖t (1 - x)‖ < 1`, then
`∑ₙ (γ)ₙ/n! ₂F₁(-n, β; γ; x) tⁿ = (1 - t + t x)^(-β) (1 - t)^(β - γ)`. -/
theorem hasSum_ordinaryHypergeometric_neg_natCast (β γ x : ℂ) {t : ℂ}
    (hγ : ∀ n : ℕ, (ascPochhammer ℂ n).eval γ ≠ 0) (ht : ‖t‖ < 1) (htx : ‖t * (1 - x)‖ < 1) :
    HasSum (fun n : ℕ => (ascPochhammer ℂ n).eval γ / (n.factorial : ℂ) *
        ordinaryHypergeometric (-(n : ℂ)) β γ x * t ^ n)
      (1 / (1 - t * (1 - x)) ^ β * (1 / (1 - t) ^ (γ - β))) := by
  have h := hasSum_carlsonRPolynomialNumerator_div_factorial (pair β (γ - β)) (pair (1 - x) 1) t
    (by intro i; fin_cases i
        · simpa [pair] using htx
        · simpa [pair] using ht)
  have hk : carlsonRGeneratingKernel (pair β (γ - β)) (pair (1 - x) 1) t =
      1 / (1 - t * (1 - x)) ^ β * (1 / (1 - t) ^ (γ - β)) := by
    simp [carlsonRGeneratingKernel, Fin.prod_univ_two, pair, mul_comm]
  rw [hk] at h
  refine h.congr_fun fun n => ?_
  have hN := carlsonRPolynomialNumerator₂_eq_hypergeometric n β (γ - β) (1 - x) one_ne_zero
    (by rw [add_sub_cancel]; exact hγ n)
  rw [carlsonRPolynomialNumerator_pair, hN, add_sub_cancel, one_pow, mul_one, div_one,
    sub_sub_cancel]
  ring

end Carlson.TwoVariable
