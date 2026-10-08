/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Sequences satisfying a binomial theorem

Carlson's class `A_k` ([Carl70]) consists of the sequences `p₀, p₁, …` of functions on `R^k`
that satisfy the binomial theorem `pₙ(z + λ) = ∑ₘ (n choose m) λ^(n-m) pₘ(z)`, where
`z + λ = (z₁ + λ, …, z_k + λ)`. For `k = 1` these are the Appell sequences. This file develops
the general theory of [Carl70], Sections 2 and 4, which underlies Section 6.4 of [Carl77].
No polynomiality is assumed unless stated.

The scalars are as general as each statement allows. The binomial theorem, the closure
properties, the slice theorems (Theorem 2, Corollaries 1 and 2), the one-variable
correspondence (2.7) and umbral evaluation hold for functions `(ι → R) → R` over any commutative
ring `R`; they rest on the binomial theorem for `appellSeq` (`appellSeq_add`). Theorem 1 and the
composition theorem, which use derivatives, hold over `ℝ` or `ℂ` (`RCLike`). The generating
relations, which divide by factorials, hold over any field of characteristic zero.

## Main definitions

* `Appell.IsAppell`: the binomial theorem (Carlson's Definition 1).
* `Appell.appellSeq_add`: the binomial theorem for the sequences of (2.7), over any commutative
  ring.
* `Appell.HasDiagonalDeriv`: `∑ᵢ ∂ᵢ pₙ = n pₙ₋₁`, as a derivative along the diagonal.
* `Appell.ofSlice`, `Appell.appellSeq`: the sequences determined by data on a slice, and by
  constants in one variable.
* `Appell.umbralEval`: the substitution `z₁^r ⋯ z_k^t ↦ q₁ᵣ ⋯ q_{k,t}` of Section 4.
* `Appell.formalSeriesSum`: the formal series `∑ₙ aₙ Xⁿ gₙ(X)`.

## Main results

* `Appell.isAppell_iff_hasDiagonalDeriv`: Theorem 1, the equivalence of (6.4-3) and (6.4-4).
* `Appell.IsAppell.affine`, `Appell.IsAppell.choose_mul_sub`: Corollary 1.
* `Appell.IsAppell.fderiv`: closure under differentiation.
* `Appell.isAppell_of_slice`: Theorem 2.
* `Appell.isAppell_iff_eq_sum_slice`, `Appell.isAppell_ofSlice`,
  `Appell.IsAppell.eq_of_eqOn_slice`: Corollary 2, (2.6) and the correspondence with data on a
  slice.
* `Appell.isAppell_unit_iff`: (2.7), Appell sequences correspond to sequences of constants.
* `Appell.IsAppell.formalSeriesSum_comm`, `Appell.isAppell_of_formalSeriesSum`: Theorem 3 and
  its converse.
* `Appell.formalSeriesSum_appell`, `Appell.eq_appellSeq_of_formalSeriesSum`: Corollary 4, (2.12).
* `Appell.isAppell_unit_iff_exp`: the exponential generating relation (2.13).
* `Appell.IsAppell.comp_reindex_add`: Theorem 4.
* `Appell.isAppell_integral_pow`: Example 20.
* `Appell.isAppell_eval_iff`: the coefficient relation (4.4) for polynomial sequences.
* `Appell.isAppell_umbralEval`: Theorem 5, the composition theorem.

## References

* [Carl70] B. C. Carlson, *Polynomials satisfying a binomial theorem*, J. Math. Anal. Appl. 32
  (1970), 543–558.
* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Section 6.4.
-/

@[expose] public noncomputable section

open Finset

namespace Appell

variable {ι : Type*}

/-! ### The binomial theorem over a commutative ring -/

section Algebra

variable {R : Type*} [CommRing R]

/-- The shift of all coordinates by the same number, `z + λ = (z₁ + λ, …, z_k + λ)`. -/
def shift (z : ι → R) (μ : R) : ι → R := fun i ↦ z i + μ

/-- Coordinates of a diagonal shift. -/
@[simp] theorem shift_apply (z : ι → R) (μ : R) (i : ι) : shift z μ i = z i + μ := rfl

/-- Successive diagonal shifts add. -/
theorem shift_shift (z : ι → R) (μ ν : R) : shift (shift z μ) ν = shift z (μ + ν) := by
  funext i; simp [shift, add_assoc]

/-- The zero shift is the identity. -/
@[simp] theorem shift_zero (z : ι → R) : shift z 0 = z := by funext i; simp [shift]

/-- **Carlson's class `A_k`**: the sequence `p₀, p₁, …` of functions of `z ∈ R^ι` satisfies a
binomial theorem, `pₙ(z + λ) = ∑ₘ (n choose m) λ^(n-m) pₘ(z)` for all `z`, `λ` and `n`. -/
def IsAppell (p : ℕ → (ι → R) → R) : Prop :=
  ∀ n z μ, p n (shift z μ) = ∑ m ∈ range (n + 1), (n.choose m : R) * μ ^ (n - m) * p m z

/-- At `λ = 0` the binomial sum `∑ₘ (n choose m) λ^(n-m) aₘ` reduces to its top term `aₙ`. -/
theorem sum_choose_mul_zero_pow (n : ℕ) (a : ℕ → R) :
    ∑ m ∈ range (n + 1), (n.choose m : R) * (0 : R) ^ (n - m) * a m = a n := by
  rw [sum_range_succ, sum_eq_zero fun m hm ↦ by
    rw [zero_pow (by have := mem_range.mp hm; omega), mul_zero, zero_mul]]
  simp

/-- The sequence `∑ₘ (n choose m) x^(n-m) aₘ` attached to a sequence of constants `a`
(Carlson (1970), (2.7)); `a = (δₛₘ)ₘ` gives the basis sequence `e^(s)` of (2.8). -/
def appellSeq (a : ℕ → R) (n : ℕ) (x : R) : R :=
  ∑ m ∈ range (n + 1), (n.choose m : R) * x ^ (n - m) * a m

/-- `appellSeq a` takes the prescribed values at `0`. -/
@[simp] theorem appellSeq_zero_right (a : ℕ → R) (n : ℕ) : appellSeq a n 0 = a n :=
  sum_choose_mul_zero_pow n a

/-- **Binomial theorem for `appellSeq`**:
`appellSeq a n (l + μ) = ∑ₘ (n choose m) μ^(n-m) appellSeq a m l`. -/
theorem appellSeq_add (a : ℕ → R) (n : ℕ) (l μ : R) :
    appellSeq a n (l + μ) =
      ∑ m ∈ range (n + 1), (n.choose m : R) * μ ^ (n - m) * appellSeq a m l := by
  simp only [appellSeq, mul_sum]
  rw [range_eq_Ico, show (∑ m ∈ Ico 0 (n + 1), ∑ k ∈ range (m + 1),
      (n.choose m : R) * μ ^ (n - m) * ((m.choose k : R) * l ^ (m - k) * a k)) =
      ∑ m ∈ Ico 0 (n + 1), ∑ k ∈ Ico 0 (m + 1),
      (n.choose m : R) * μ ^ (n - m) * ((m.choose k : R) * l ^ (m - k) * a k) by
        simp only [range_eq_Ico], ← sum_Ico_Ico_comm]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_Ico.mp hk).2
  rw [sum_Ico_eq_sum_range, show n + 1 - k = n - k + 1 by omega, add_pow, mul_sum, sum_mul]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ n - k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hc : ((n.choose (k + j) : ℕ) : R) * ((k + j).choose k : ℕ) =
      (n.choose k : R) * ((n - k).choose j : ℕ) := by
    have := Nat.choose_mul (n := n) (k := k + j) (s := k) (by omega)
    rw [show k + j - k = j by omega] at this
    simpa only [Nat.cast_mul] using congrArg (Nat.cast (R := R)) this
  rw [show n - (k + j) = n - k - j by omega, show k + j - k = j by omega]
  linear_combination (-(μ ^ (n - k - j) * l ^ j * a k)) * hc

/-! ### Closure properties -/

namespace IsAppell

variable {p q : ℕ → (ι → R) → R}

/-- The zero sequence satisfies the binomial theorem. -/
theorem zero : IsAppell (fun _ _ ↦ 0 : ℕ → (ι → R) → R) := by
  intro n z μ; simp

/-- `A_k` is closed under addition. -/
theorem add (hp : IsAppell p) (hq : IsAppell q) : IsAppell (fun n z ↦ p n z + q n z) := by
  intro n z μ
  dsimp only
  rw [hp n z μ, hq n z μ, ← sum_add_distrib]
  exact sum_congr rfl fun m _ ↦ by ring

/-- `A_k` is closed under multiplication by a constant. -/
theorem const_mul (hp : IsAppell p) (c : R) : IsAppell (fun n z ↦ c * p n z) := by
  intro n z μ
  dsimp only
  rw [hp n z μ, mul_sum]
  exact sum_congr rfl fun m _ ↦ by ring

/-- **Carlson (1970), Theorem 4** (in a slightly more general form): substituting
`zᵢ = w_{σ i} + cᵢ` for any map of indices `σ` and constants `c` preserves the binomial
theorem. This covers merging variables, `p(z₁, …, z_{k-1}, z_k + α, z_k + β, …)`. -/
theorem comp_reindex_add (hp : IsAppell p) {κ : Type*} (σ : ι → κ) (c : ι → R) :
    IsAppell (fun n (w : κ → R) ↦ p n (fun i ↦ w (σ i) + c i)) := by
  intro n w μ
  dsimp only
  have hw : (fun i ↦ shift w μ (σ i) + c i) = shift (fun i ↦ w (σ i) + c i) μ := by
    funext i; simp only [shift_apply]; ring
  rw [hw, hp]

/-- **Carlson (1970), Corollary 1(ii)**: the shifted sequence `(n choose m) pₙ₋ₘ` (zero for
`n < m`) is again in `A_k`. -/
theorem choose_mul_sub (hp : IsAppell p) (m : ℕ) :
    IsAppell (fun n z ↦ (n.choose m : R) * p (n - m) z) := by
  intro n z μ
  dsimp only
  rcases lt_or_ge n m with hnm | hmn
  · rw [Nat.choose_eq_zero_of_lt hnm, Nat.cast_zero, zero_mul]
    refine (sum_eq_zero fun j hj ↦ ?_).symm
    rw [Nat.choose_eq_zero_of_lt (show j < m by have := mem_range.mp hj; omega), Nat.cast_zero,
      zero_mul, mul_zero]
  · rw [hp (n - m) z μ, mul_sum, ← sum_range_add_sum_Ico _ (show m ≤ n + 1 by omega),
      sum_eq_zero (s := range m) fun j hj ↦ by
        rw [Nat.choose_eq_zero_of_lt (mem_range.mp hj), Nat.cast_zero, zero_mul, mul_zero],
      zero_add, sum_Ico_eq_sum_range, show n + 1 - m = n - m + 1 by omega]
    refine sum_congr rfl fun i hi ↦ ?_
    have hc : ((n.choose (m + i) : ℕ) : R) * ((m + i).choose m : ℕ) =
        (n.choose m : R) * ((n - m).choose i : ℕ) := by
      have := Nat.choose_mul (n := n) (k := m + i) (s := m) (by omega)
      rw [show m + i - m = i by omega] at this
      simpa only [Nat.cast_mul] using congrArg (Nat.cast (R := R)) this
    rw [show n - (m + i) = n - m - i by omega, show m + i - m = i by omega]
    linear_combination (-(μ ^ (n - m - i) * p i z)) * hc

end IsAppell

/-- **Carlson (1970), Corollary 1(i)**: an affine change of variables `w = αz + β`, `α ≠ 0`,
renormalized by `α⁻ⁿ`, preserves `A_k`. -/
theorem IsAppell.affine {K : Type*} [Field K] {p : ℕ → (ι → K) → K} (hp : IsAppell p)
    {α : K} (hα : α ≠ 0) (β : ι → K) :
    IsAppell (fun n z ↦ α⁻¹ ^ n * p n (fun i ↦ α * z i + β i)) := by
  intro n z μ
  dsimp only
  have hw : (fun i ↦ α * shift z μ i + β i) = shift (fun i ↦ α * z i + β i) (α * μ) := by
    funext i; simp only [shift_apply]; ring
  rw [hw, hp n _ (α * μ), mul_sum]
  refine sum_congr rfl fun m hm ↦ ?_
  have hm' : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hpow : α⁻¹ ^ n * α ^ (n - m) = α⁻¹ ^ m := by
    rw [← Nat.add_sub_cancel' hm', pow_add, Nat.add_sub_cancel_left, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hα, one_pow, mul_one]
  rw [mul_pow]
  linear_combination ((n.choose m : K) * μ ^ (n - m) * p m (fun i ↦ α * z i + β i)) * hpow

/-! ### A binomial theorem on one slice suffices -/

/-- **Carlson (1970), Theorem 2**: if the binomial theorem holds for all `z` with one coordinate
fixed, `z i₀ = ζ`, then it holds for all `z`. -/
theorem isAppell_of_slice {p : ℕ → (ι → R) → R} (i₀ : ι) (ζ : R)
    (h : ∀ n z μ, z i₀ = ζ →
      p n (shift z μ) = ∑ m ∈ range (n + 1), (n.choose m : R) * μ ^ (n - m) * p m z) :
    IsAppell p := by
  intro n z μ
  set l := z i₀ - ζ
  set z' := shift z (-l)
  have hz' : z' i₀ = ζ := by simp [z', l]
  have hz : shift z' l = z := by simp [z', shift_shift]
  have hp : ∀ k ν, p k (shift z' ν) = appellSeq (fun m ↦ p m z') k ν := fun k ν ↦ h k z' ν hz'
  rw [← hz, shift_shift, hp, appellSeq_add]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [hp]

/-- **Carlson (1970), Corollary 2 and (2.6)**: `p ∈ A_k` if and only if every `pₙ` is
recovered from its values on the slice `z i₀ = 0` by
`pₙ(z) = ∑ₘ (n choose m) (z i₀)^(n-m) pₘ(z - z i₀)`. -/
theorem isAppell_iff_eq_sum_slice {p : ℕ → (ι → R) → R} (i₀ : ι) :
    IsAppell p ↔ ∀ n z, p n z =
      ∑ m ∈ range (n + 1), (n.choose m : R) * z i₀ ^ (n - m) * p m (shift z (-z i₀)) := by
  constructor
  · intro hp n z
    rw [← hp, shift_shift, neg_add_cancel, shift_zero]
  · intro h
    refine isAppell_of_slice i₀ 0 fun n z μ hz ↦ ?_
    rw [h n (shift z μ)]
    simp [shift_shift, hz]

/-- The sequence in `A_k` with prescribed values `q` on the slice `z i₀ = 0`. -/
def ofSlice (i₀ : ι) (q : ℕ → (ι → R) → R) (n : ℕ) (z : ι → R) : R :=
  ∑ m ∈ range (n + 1), (n.choose m : R) * z i₀ ^ (n - m) * q m (shift z (-z i₀))

/-- On the slice `z i₀ = 0` the sequence `ofSlice i₀ q` takes the prescribed values. -/
theorem ofSlice_of_eq_zero (i₀ : ι) (q : ℕ → (ι → R) → R) (n : ℕ) {z : ι → R}
    (hz : z i₀ = 0) : ofSlice i₀ q n z = q n z := by
  have := sum_choose_mul_zero_pow n (fun m ↦ q m z)
  simpa [ofSlice, hz] using this

/-- Every sequence of functions on the slice `z i₀ = 0` extends to a sequence in `A_k`. -/
theorem isAppell_ofSlice (i₀ : ι) (q : ℕ → (ι → R) → R) : IsAppell (ofSlice i₀ q) := by
  refine isAppell_of_slice i₀ 0 fun n z μ hz ↦ ?_
  have hs : shift z μ i₀ = μ := by simp [hz]
  simp only [ofSlice, hs, shift_shift, add_neg_cancel, shift_zero]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [show q m z = ofSlice i₀ q m z from (ofSlice_of_eq_zero i₀ q m hz).symm]
  rfl

/-- A sequence in `A_k` is determined by its values on the slice `z i₀ = 0`. -/
theorem IsAppell.eq_of_eqOn_slice {p q : ℕ → (ι → R) → R} (hp : IsAppell p) (hq : IsAppell q)
    (i₀ : ι) (h : ∀ n z, z i₀ = 0 → p n z = q n z) : p = q := by
  funext n z
  rw [(isAppell_iff_eq_sum_slice i₀).mp hp, (isAppell_iff_eq_sum_slice i₀).mp hq]
  exact sum_congr rfl fun m _ ↦ by rw [h m _ (by simp)]

/-! ### One variable: Appell sequences -/

/-- **Carlson (1970), (2.7)**: a sequence of functions of one variable satisfies the binomial
theorem if and only if it is the sequence `appellSeq` of its values at `0`. Hence `A₁` is in
bijection with the sequences of elements of `R`. -/
theorem isAppell_unit_iff {p : ℕ → R → R} :
    IsAppell (fun n (z : Unit → R) ↦ p n (z ())) ↔ ∀ n, p n = appellSeq (fun m ↦ p m 0) n := by
  rw [isAppell_iff_eq_sum_slice ()]
  constructor
  · intro h n
    funext x
    have := h n (fun _ ↦ x)
    simpa [shift, appellSeq] using this
  · intro h n z
    have hz : shift z (-z ()) = fun _ ↦ 0 := by funext u; simp [shift]
    rw [hz]
    exact congrFun (h n) (z ())

/-- Every `appellSeq` satisfies the binomial theorem. -/
theorem isAppell_appellSeq (a : ℕ → R) :
    IsAppell (fun n (z : Unit → R) ↦ appellSeq a n (z ())) := by
  rw [isAppell_unit_iff]
  intro n; simp

/-! ### Umbral evaluation -/

section Umbral

open MvPolynomial

variable [Fintype ι] {κ : Type*}

/-- The umbral evaluation of a polynomial in `z₁, …, z_k`: every monomial
`z₁^r ⋯ z_k^t` is replaced by `q₁ᵣ(w) ⋯ q_{k,t}(w)` (Carlson (1970), Section 4). -/
def umbralEval (q : ι → ℕ → (κ → R) → R) (w : κ → R) (P : MvPolynomial ι R) : R :=
  ∑ s ∈ P.support, P.coeff s * ∏ i, q i (s i) w

/-- The umbral evaluation may be summed over any finite set containing the support. -/
theorem umbralEval_eq_sum_of_subset (q : ι → ℕ → (κ → R) → R) (w : κ → R)
    {P : MvPolynomial ι R} {S : Finset (ι →₀ ℕ)} (hS : P.support ⊆ S) :
    umbralEval q w P = ∑ s ∈ S, P.coeff s * ∏ i, q i (s i) w := by
  refine sum_subset hS fun s _ hs ↦ ?_
  rw [notMem_support_iff.mp hs, zero_mul]

/-- Umbral evaluation is additive. -/
theorem umbralEval_add (q : ι → ℕ → (κ → R) → R) (w : κ → R) (P Q : MvPolynomial ι R) :
    umbralEval q w (P + Q) = umbralEval q w P + umbralEval q w Q := by
  classical
  rw [umbralEval_eq_sum_of_subset q w (support_add (p := P) (q := Q)),
    umbralEval_eq_sum_of_subset q w (subset_union_left (s₂ := Q.support)),
    umbralEval_eq_sum_of_subset q w (subset_union_right (s₁ := P.support)), ← sum_add_distrib]
  exact sum_congr rfl fun s _ ↦ by simp [add_mul]

/-- Umbral evaluation of a monomial. -/
theorem umbralEval_monomial (q : ι → ℕ → (κ → R) → R) (w : κ → R) (s : ι →₀ ℕ) (c : R) :
    umbralEval q w (monomial s c) = c * ∏ i, q i (s i) w := by
  classical
  rw [umbralEval_eq_sum_of_subset q w (support_monomial_subset (s := s) (a := c)),
    sum_singleton, coeff_monomial, ite_eq_left_of_eq_true _ _ (eq_true rfl)]

/-- Umbral evaluation commutes with scalar multiplication. -/
theorem umbralEval_smul (q : ι → ℕ → (κ → R) → R) (w : κ → R) (c : R) (P : MvPolynomial ι R) :
    umbralEval q w (c • P) = c * umbralEval q w P := by
  rw [umbralEval_eq_sum_of_subset q w (support_smul (a := c) (f := P)), umbralEval, mul_sum]
  exact sum_congr rfl fun s _ ↦ by rw [coeff_smul, smul_eq_mul, mul_assoc]

/-- Umbral evaluation commutes with finite sums. -/
theorem umbralEval_sum (q : ι → ℕ → (κ → R) → R) (w : κ → R) {α : Type*} (t : Finset α)
    (P : α → MvPolynomial ι R) :
    umbralEval q w (∑ a ∈ t, P a) = ∑ a ∈ t, umbralEval q w (P a) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [umbralEval]
  | insert a t ha ih => rw [sum_insert ha, sum_insert ha, umbralEval_add, ih]

/-- Umbral evaluation with the monomial sequences `qᵢₙ(w) = wᵢⁿ` is ordinary evaluation. -/
theorem umbralEval_pow (z : ι → R) (P : MvPolynomial ι R) :
    umbralEval (fun i n (w : ι → R) ↦ w i ^ n) z P = eval z P := by
  rw [umbralEval, eval_eq']

end Umbral

end Algebra

/-! ### Diagonal derivatives over `ℝ` or `ℂ` -/

section Calculus

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The derivative of `pₙ` along the diagonal direction `(1, …, 1)` (Carlson's `∑ᵢ ∂ᵢ`) is
`n pₙ₋₁` at every point. -/
def HasDiagonalDeriv (p : ℕ → (ι → 𝕜) → 𝕜) : Prop :=
  ∀ n z, HasDerivAt (fun μ : 𝕜 ↦ p n (shift z μ)) (n * p (n - 1) z) 0

/-- The diagonal derivative of the polynomial `μ ↦ ∑ₘ (n choose m) μ^(n-m) aₘ` at `0`. -/
theorem hasDerivAt_binomialSum (n : ℕ) (a : ℕ → 𝕜) :
    HasDerivAt (fun μ : 𝕜 ↦ ∑ m ∈ range (n + 1), (n.choose m : 𝕜) * μ ^ (n - m) * a m)
      (n * a (n - 1)) 0 := by
  set P : Polynomial 𝕜 := ∑ m ∈ range (n + 1),
    Polynomial.C ((n.choose m : 𝕜) * a m) * Polynomial.X ^ (n - m)
  have hP : ∀ μ : 𝕜, P.eval μ = ∑ m ∈ range (n + 1), (n.choose m : 𝕜) * μ ^ (n - m) * a m := by
    intro μ
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    refine sum_congr rfl fun m _ ↦ by ring
  have h := P.hasDerivAt 0
  simp only [hP] at h
  convert h using 1
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, zero_add,
    Nat.cast_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [sum_eq_single (n - 1)]
    · have hc : n.choose (n - 1) = n := by
        rw [Nat.choose_symm_of_eq_add (show n = (n - 1) + 1 by omega), Nat.choose_one_right]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), hc]
      ring
    · intro m hm hne
      rw [ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)]
    · intro h; exact absurd (mem_range.mpr (by omega)) h

/-- The derivative of the binomial sum: `d/dμ ∑ₘ (n+1 choose m) μ^(n+1-m) aₘ
= (n + 1) ∑ₘ (n choose m) μ^(n-m) aₘ`. -/
theorem hasDerivAt_binomialSum_succ (n : ℕ) (a : ℕ → 𝕜) (μ : 𝕜) :
    HasDerivAt (fun μ : 𝕜 ↦ ∑ m ∈ range (n + 2), ((n + 1).choose m : 𝕜) * μ ^ (n + 1 - m) * a m)
      ((n + 1) * ∑ m ∈ range (n + 1), (n.choose m : 𝕜) * μ ^ (n - m) * a m) μ := by
  have h := HasDerivAt.fun_sum (u := range (n + 2)) (A := fun m μ ↦
      ((n + 1).choose m : 𝕜) * μ ^ (n + 1 - m) * a m) (fun m _ ↦
    (((hasDerivAt_pow (n + 1 - m) μ).const_mul (((n + 1).choose m : 𝕜))).mul_const (a m)))
  refine h.congr_deriv ?_
  rw [sum_range_succ, Nat.choose_self, Nat.sub_self, mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun m hm ↦ ?_
  have hm' : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hc := Nat.choose_mul_succ_eq n m
  have hc' : (((n + 1).choose m : ℕ) : 𝕜) * ((n + 1 - m : ℕ) : 𝕜) = (n.choose m : 𝕜) * (n + 1) := by
    exact_mod_cast hc.symm
  rw [show n + 1 - m - 1 = n - m by omega]
  push_cast [Nat.sub_add_comm hm'] at hc' ⊢
  linear_combination (μ ^ (n - m) * a m) * hc'

/-- Two functions on `𝕜` with the same derivative everywhere and the same value at `0` agree.
This is `eq_of_fderiv_eq` in derivative form. -/
private theorem eq_of_hasDerivAt_eq {f g f' : 𝕜 → 𝕜} (hf : ∀ μ, HasDerivAt f (f' μ) μ)
    (hg : ∀ μ, HasDerivAt g (f' μ) μ) (h0 : f 0 = g 0) (μ : 𝕜) : f μ = g μ :=
  congrFun (eq_of_fderiv_eq (fun μ ↦ (hf μ).differentiableAt) (fun μ ↦ (hg μ).differentiableAt)
    (fun μ ↦ (hf μ).hasFDerivAt.fderiv.trans (hg μ).hasFDerivAt.fderiv.symm) 0 h0) μ

/-- **Theorem 1 of Carlson (1970)** (and the equivalence of (6.4-3) and (6.4-4)): a sequence
satisfies a binomial theorem if and only if its diagonal derivative `∑ᵢ ∂ᵢ pₙ` is `n pₙ₋₁`. -/
theorem isAppell_iff_hasDiagonalDeriv {p : ℕ → (ι → 𝕜) → 𝕜} :
    IsAppell p ↔ HasDiagonalDeriv p := by
  constructor
  · intro hp n z
    have := hasDerivAt_binomialSum n (fun m ↦ p m z)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun μ ↦ ?_)
    exact hp n z μ
  · intro hp n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro z
    -- `μ ↦ pₙ(z + μ)` and the binomial sum have the same derivative and agree at `0`.
    have hL : ∀ μ, HasDerivAt (fun μ ↦ p n (shift z μ)) (n * p (n - 1) (shift z μ)) μ := by
      intro μ
      have h := hp n (shift z μ)
      have h' : HasDerivAt (fun ν ↦ p n (shift (shift z μ) (ν - μ)))
          (n * p (n - 1) (shift z μ)) μ :=
        HasDerivAt.comp_sub_const (f := fun ν ↦ p n (shift (shift z μ) ν)) μ μ
          (by rw [sub_self]; exact h)
      refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ν ↦ ?_)
      simp [shift_shift]
    rcases n with _ | k
    · simp only [Nat.cast_zero, zero_mul] at hL
      intro μ
      have := eq_of_hasDerivAt_eq hL (fun μ ↦ hasDerivAt_const μ (p 0 z)) (by simp) μ
      simpa using this
    · have hR : ∀ μ, HasDerivAt
          (fun μ ↦ ∑ m ∈ range (k + 2), ((k + 1).choose m : 𝕜) * μ ^ (k + 1 - m) * p m z)
          (((k + 1 : ℕ) : 𝕜) * p (k + 1 - 1) (shift z μ)) μ := by
        intro μ
        rw [show k + 1 - 1 = k by omega, ih k (by omega) z μ]
        push_cast
        exact hasDerivAt_binomialSum_succ k (fun m ↦ p m z) μ
      intro μ
      refine eq_of_hasDerivAt_eq hL hR ?_ μ
      simp only [shift_zero, sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero,
        Nat.cast_one, one_mul]
      rw [sum_eq_zero fun m hm ↦ by
        rw [zero_pow (by have := mem_range.mp hm; omega), mul_zero, zero_mul]]
      simp

/-- `A_k` is closed under differentiation: if every `pₙ` is differentiable, the directional
derivatives `Dᵥ pₙ` form a sequence in `A_k`. In particular `∂pₙ/∂zᵢ` does. -/
theorem IsAppell.fderiv [Fintype ι] {p : ℕ → (ι → 𝕜) → 𝕜} (hp : IsAppell p)
    (hd : ∀ n, Differentiable 𝕜 (p n)) (v : ι → 𝕜) :
    IsAppell (fun n z ↦ _root_.fderiv 𝕜 (p n) z v) := by
  intro n z μ
  dsimp only
  have hL : HasFDerivAt (fun z ↦ p n (shift z μ)) (_root_.fderiv 𝕜 (p n) (shift z μ)) z := by
    have h := ((hd n (shift z μ)).hasFDerivAt).comp z
      ((hasFDerivAt_id z).add_const (fun _ : ι ↦ μ))
    exact h
  have hR : HasFDerivAt (fun z ↦ ∑ m ∈ range (n + 1), (n.choose m : 𝕜) * μ ^ (n - m) * p m z)
      (∑ m ∈ range (n + 1), ((n.choose m : 𝕜) * μ ^ (n - m)) • _root_.fderiv 𝕜 (p m) z) z :=
    HasFDerivAt.fun_sum fun m _ ↦ ((hd m z).hasFDerivAt).const_mul _
  have hfun : (fun z ↦ p n (shift z μ)) =
      fun z ↦ ∑ m ∈ range (n + 1), (n.choose m : 𝕜) * μ ^ (n - m) * p m z :=
    funext fun z ↦ hp n z μ
  rw [hfun] at hL
  rw [hL.unique hR]
  simp [mul_assoc]

/-! ### The composition theorem -/

section Composition

open MvPolynomial

variable [Fintype ι] {κ : Type*}

/-- The diagonal derivative of an umbral evaluation: if every `qᵢ` has diagonal derivative
`n qᵢₙ₋₁`, then `λ ↦ U_{w+λ}(P)` has derivative `U_w(∑ᵢ ∂P/∂zᵢ)` at `0`. -/
theorem hasDerivAt_umbralEval {q : ι → ℕ → (κ → 𝕜) → 𝕜} (hq : ∀ i, HasDiagonalDeriv (q i))
    (w : κ → 𝕜) (P : MvPolynomial ι 𝕜) :
    HasDerivAt (fun μ ↦ umbralEval q (shift w μ) P) (umbralEval q w (∑ i, pderiv i P)) 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s c =>
    simp only [umbralEval_monomial, pderiv_monomial, umbralEval_sum]
    have h := (HasDerivAt.fun_finsetProd (u := Finset.univ) (x := (0 : 𝕜))
      (f := fun i μ ↦ q i (s i) (shift w μ)) fun i _ ↦ hq i (s i) w).const_mul c
    simp only [shift_zero] at h
    convert h using 1
    rw [mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rcases Nat.eq_zero_or_pos (s i) with hs | hs
    · simp [hs]
    · rw [← mul_prod_erase _ _ (mem_univ i), smul_eq_mul]
      have hrest : ∏ j ∈ univ.erase i, q j ((s - Finsupp.single i 1 : ι →₀ ℕ) j) w =
          ∏ j ∈ univ.erase i, q j (s j) w :=
        prod_congr rfl fun j hj ↦ by
          rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (ne_of_mem_erase hj), Nat.sub_zero]
      rw [hrest, Finsupp.tsub_apply, Finsupp.single_eq_same]
      ring
  | add P Q hP hQ =>
    simp only [umbralEval_add, map_add, sum_add_distrib]
    exact hP.add hQ

/-- The diagonal derivative of a polynomial function is the evaluation of `∑ᵢ ∂P/∂zᵢ`. -/
theorem hasDerivAt_eval_shift (z : ι → 𝕜) (P : MvPolynomial ι 𝕜) :
    HasDerivAt (fun μ ↦ eval (shift z μ) P) (eval z (∑ i, pderiv i P)) 0 := by
  have hq : ∀ i, HasDiagonalDeriv (fun n (w : ι → 𝕜) ↦ w i ^ n) := fun i n w ↦ by
    simpa [shift] using HasDerivAt.comp_const_add (f := fun x : 𝕜 ↦ x ^ n) (w i) 0
      (by rw [add_zero]; exact hasDerivAt_pow n (w i))
  have h := hasDerivAt_umbralEval hq z P
  simp only [umbralEval_pow] at h
  exact h

/-- For a polynomial sequence, Theorem 1 becomes the coefficient identity (4.4):
`∑ᵢ ∂Pₙ/∂zᵢ = n Pₙ₋₁` as polynomials. -/
theorem isAppell_eval_iff (P : ℕ → MvPolynomial ι 𝕜) :
    IsAppell (fun n z ↦ eval z (P n)) ↔ ∀ n, ∑ i, pderiv i (P n) = n • P (n - 1) := by
  rw [isAppell_iff_hasDiagonalDeriv]
  constructor
  · intro h n
    refine MvPolynomial.funext fun z ↦ ?_
    rw [((hasDerivAt_eval_shift z (P n))).unique (h n z), map_nsmul, nsmul_eq_mul]
  · intro h n z
    have := hasDerivAt_eval_shift z (P n)
    rwa [h n, map_nsmul, nsmul_eq_mul] at this

/-- **Carlson (1970), Theorem 5 (composition theorem)**: let `Pₙ` be polynomials whose
evaluations lie in `A_k`, and for each `i` let `qᵢ` be a sequence in `A_m`. Replacing each
monomial `z₁^r ⋯ z_k^t` of `Pₙ` by `q₁ᵣ ⋯ q_{k,t}` gives a sequence in `A_m`. -/
theorem isAppell_umbralEval {P : ℕ → MvPolynomial ι 𝕜} (hP : IsAppell fun n z ↦ eval z (P n))
    {q : ι → ℕ → (κ → 𝕜) → 𝕜} (hq : ∀ i, IsAppell (q i)) :
    IsAppell (fun n w ↦ umbralEval q w (P n)) := by
  have hq' : ∀ i, HasDiagonalDeriv (q i) := fun i ↦ isAppell_iff_hasDiagonalDeriv.mp (hq i)
  rw [isAppell_iff_hasDiagonalDeriv]
  intro n w
  have h := hasDerivAt_umbralEval hq' w (P n)
  rwa [(isAppell_eval_iff P).mp hP n, ← Nat.cast_smul_eq_nsmul 𝕜, umbralEval_smul] at h

end Composition

end Calculus

/-! ### Generating relations -/

section Generating

open PowerSeries Nat

variable {K : Type*} [Field K] [CharZero K]

/-- The formal series `∑ₙ aₙ Xⁿ gₙ(X)` for a sequence of formal power series `gₙ`; its
coefficient of `X^N` is the finite sum `∑_{n ≤ N} aₙ [X^(N-n)] gₙ`
(see `coeff_formalSeriesSum`). -/
def formalSeriesSum (a : ℕ → K) (g : ℕ → K⟦X⟧) : K⟦X⟧ :=
  mk fun N ↦ ∑ n ∈ range (N + 1), a n * coeff (N - n) (g n)

omit [CharZero K] in
/-- The coefficient of `X^N` in `formalSeriesSum a g` agrees with that of the partial sum
`∑_{n ≤ N} aₙ Xⁿ gₙ`, so `formalSeriesSum a g` is the `X`-adic sum of the series. -/
theorem coeff_formalSeriesSum (a : ℕ → K) (g : ℕ → K⟦X⟧) (N : ℕ) :
    coeff N (formalSeriesSum a g) = coeff N (∑ n ∈ range (N + 1), C (a n) * X ^ n * g n) := by
  rw [formalSeriesSum, coeff_mk, map_sum]
  refine sum_congr rfl fun n hn ↦ ?_
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul',
    ite_eq_left_of_eq_true _ _ (eq_true (by have := mem_range.mp hn; omega))]

/-- The basic computation behind Carlson's Theorem 3: with `f⁽ⁿ⁾` the `n`-th formal
derivative, the coefficient of `X^N` in `∑ₙ (bₙ / n!) Xⁿ f⁽ⁿ⁾(λX)` is
`[X^N] f · ∑ₙ (N choose n) λ^(N-n) bₙ`. -/
theorem coeff_formalSeriesSum_rescale (b : ℕ → K) (f : K⟦X⟧) (l : K) (N : ℕ) :
    coeff N (formalSeriesSum (fun n ↦ b n / n !) fun n ↦ rescale l (d⁄dX^[n] f)) =
      coeff N f * ∑ n ∈ range (N + 1), (N.choose n : K) * l ^ (N - n) * b n := by
  rw [formalSeriesSum, coeff_mk, mul_sum]
  refine sum_congr rfl fun n hn ↦ ?_
  have hn' : n ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hn)
  rw [coeff_rescale, coeff_iterate_derivative, Nat.sub_add_cancel hn',
    ascFactorial_eq_factorial_mul_choose, Nat.sub_add_cancel hn', mul_comm]
  have : (n ! : K) ≠ 0 := by exact_mod_cast (factorial_pos n).ne'
  push_cast
  field_simp

/-- **Carlson (1970), Theorem 3**: for `p ∈ A_k` and every formal power series `f`,
`∑ₙ pₙ(z + μ) f⁽ⁿ⁾(λt) tⁿ/n! = ∑ₙ pₙ(z + λ) f⁽ⁿ⁾(μt) tⁿ/n!` as formal series in `t`. -/
theorem IsAppell.formalSeriesSum_comm {p : ℕ → (ι → K) → K} (hp : IsAppell p) (f : K⟦X⟧)
    (z : ι → K) (l μ : K) :
    formalSeriesSum (fun n ↦ p n (shift z μ) / n !) (fun n ↦ rescale l (d⁄dX^[n] f)) =
      formalSeriesSum (fun n ↦ p n (shift z l) / n !) (fun n ↦ rescale μ (d⁄dX^[n] f)) := by
  ext N
  rw [coeff_formalSeriesSum_rescale (fun n ↦ p n (shift z μ)),
    coeff_formalSeriesSum_rescale (fun n ↦ p n (shift z l)), ← hp, ← hp, shift_shift,
    shift_shift, add_comm]

/-- **Carlson (1970), converse of Theorem 3**: if the generating relation holds with `μ = 0`
on a slice `z i₀ = ζ`, for all `λ`, and every coefficient of `f` is nonzero, then `p ∈ A_k`.
Here `f⁽ⁿ⁾(0 · t)` is the constant series `f⁽ⁿ⁾(0)`. -/
theorem isAppell_of_formalSeriesSum {p : ℕ → (ι → K) → K} (i₀ : ι) (ζ : K) {f : K⟦X⟧}
    (hf : ∀ n, coeff n f ≠ 0)
    (h : ∀ z l, z i₀ = ζ →
      formalSeriesSum (fun n ↦ p n z / n !) (fun n ↦ rescale l (d⁄dX^[n] f)) =
        formalSeriesSum (fun n ↦ p n (shift z l) / n !) (fun n ↦ rescale 0 (d⁄dX^[n] f))) :
    IsAppell p := by
  refine isAppell_of_slice i₀ ζ fun n z μ hz ↦ ?_
  have := congrArg (coeff n) (h z μ hz)
  rw [coeff_formalSeriesSum_rescale (fun n ↦ p n z),
    coeff_formalSeriesSum_rescale (fun n ↦ p n (shift z μ)),
    sum_choose_mul_zero_pow n (fun m ↦ p m (shift z μ))] at this
  exact (mul_left_cancel₀ (hf n) this).symm

/-- **Carlson (1970), Corollary 4, (2.12)**: an Appell sequence `p` in one variable satisfies
`∑ₙ pₙ(0) f⁽ⁿ⁾(xt) tⁿ/n! = ∑ₙ pₙ(x) f⁽ⁿ⁾(0) tⁿ/n!` for every formal power series `f`. -/
theorem formalSeriesSum_appell {p : ℕ → K → K} (hp : IsAppell fun n (z : Unit → K) ↦ p n (z ()))
    (f : K⟦X⟧) (x : K) :
    formalSeriesSum (fun n ↦ p n 0 / n !) (fun n ↦ rescale x (d⁄dX^[n] f)) =
      formalSeriesSum (fun n ↦ p n x / n !) (fun n ↦ rescale 0 (d⁄dX^[n] f)) := by
  have := hp.formalSeriesSum_comm f (fun _ ↦ 0) x 0
  simpa [shift] using this

/-- **Carlson (1970), converse of Corollary 4**: if every coefficient of `f` is nonzero, the
sequence `q` generated by (2.12) from constants `a` is the Appell sequence `appellSeq a`. -/
theorem eq_appellSeq_of_formalSeriesSum {a : ℕ → K} {q : ℕ → K → K} {f : K⟦X⟧}
    (hf : ∀ n, coeff n f ≠ 0)
    (h : ∀ x, formalSeriesSum (fun n ↦ a n / n !) (fun n ↦ rescale x (d⁄dX^[n] f)) =
      formalSeriesSum (fun n ↦ q n x / n !) (fun n ↦ rescale 0 (d⁄dX^[n] f))) :
    q = appellSeq a := by
  funext n x
  have := congrArg (coeff n) (h x)
  rw [coeff_formalSeriesSum_rescale a, coeff_formalSeriesSum_rescale (fun m ↦ q m x),
    sum_choose_mul_zero_pow n (fun m ↦ q m x)] at this
  exact (mul_left_cancel₀ (hf n) this).symm

/-- Coefficients of `e^(xt) ∑ₙ aₙ tⁿ / n!`. -/
theorem coeff_rescale_exp_mul (a : ℕ → K) (x : K) (N : ℕ) :
    coeff N (rescale x (exp K) * mk fun n ↦ a n / n !) = appellSeq a N x / N ! := by
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ coeff i (mk fun n ↦ a n / n !) * coeff j (rescale x (exp K))), appellSeq,
    sum_div]
  refine sum_congr rfl fun m hm ↦ ?_
  have hm' : m ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [coeff_mk, coeff_rescale, coeff_exp, Nat.cast_choose K hm']
  have h1 : (m ! : K) ≠ 0 := by exact_mod_cast (factorial_pos m).ne'
  have h2 : ((N - m)! : K) ≠ 0 := by exact_mod_cast (factorial_pos (N - m)).ne'
  have h3 : (N ! : K) ≠ 0 := by exact_mod_cast (factorial_pos N).ne'
  simp only [map_div₀, map_one, map_natCast]
  field_simp

/-- **Carlson (1970), (2.13)** (and (1.4)): a sequence of functions of one variable is an
Appell sequence if and only if `e^(xt) ∑ₙ pₙ(0) tⁿ/n! = ∑ₙ pₙ(x) tⁿ/n!` for every `x`. -/
theorem isAppell_unit_iff_exp {p : ℕ → K → K} :
    IsAppell (fun n (z : Unit → K) ↦ p n (z ())) ↔
      ∀ x, (mk fun n ↦ p n x / n !) = rescale x (exp K) * mk fun n ↦ p n 0 / n ! := by
  rw [isAppell_unit_iff]
  constructor
  · intro h x
    ext N
    rw [coeff_rescale_exp_mul, coeff_mk, ← h N]
  · intro h n
    funext x
    have := congrArg (coeff n) (h x)
    rw [coeff_rescale_exp_mul, coeff_mk] at this
    have h3 : (n ! : K) ≠ 0 := by exact_mod_cast (factorial_pos n).ne'
    exact (div_left_inj' h3).mp this

end Generating

/-! ### Averages over a hyperplane -/

open MeasureTheory in
/-- **Carlson (1970), Example 20**: if `ν` is a measure concentrated on the hyperplane
`∑ᵢ uᵢ = 1`, the averages `pₙ(z) = ∫ (∑ᵢ uᵢ zᵢ)ⁿ dν(u)` satisfy the binomial theorem. -/
theorem isAppell_integral_pow [Fintype ι] {ν : Measure (ι → ℝ)}
    (hν : ∀ᵐ u ∂ν, ∑ i, u i = 1)
    (hint : ∀ (n : ℕ) (z : ι → ℂ), Integrable (fun u : ι → ℝ ↦ (∑ i, (u i : ℂ) * z i) ^ n) ν) :
    IsAppell fun n z ↦ ∫ u, (∑ i, (u i : ℂ) * z i) ^ n ∂ν := by
  intro n z μ
  dsimp only
  have hae : (fun u : ι → ℝ ↦ (∑ i, (u i : ℂ) * shift z μ i) ^ n) =ᵐ[ν]
      fun u ↦ ∑ m ∈ range (n + 1),
        (n.choose m : ℂ) * μ ^ (n - m) * (∑ i, (u i : ℂ) * z i) ^ m := by
    filter_upwards [hν] with u hu
    have hu' : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu
    have : ∑ i, (u i : ℂ) * shift z μ i = (∑ i, (u i : ℂ) * z i) + μ := by
      simp only [shift_apply, mul_add, sum_add_distrib, ← sum_mul, hu', one_mul]
    rw [this, add_pow]
    exact sum_congr rfl fun m _ ↦ by ring
  rw [integral_congr_ae hae, integral_finsetSum _ fun m _ ↦ (hint m z).const_mul _]
  exact sum_congr rfl fun m _ ↦ integral_const_mul _ _

end Appell

end
