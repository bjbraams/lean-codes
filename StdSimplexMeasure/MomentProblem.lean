/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.MomentDetermination
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# The moment problem on the standard simplex

A sequence `a : ℕ^ι → ℝ` is the sequence of monomial moments `a m = ∫ ∏ i, u i ^ m i dμ` of a
finite measure `μ` supported on the standard simplex if and only if `a ≥ 0` and `a` satisfies the
**sum-shift equation** `a n = ∑ i, a (n + e i)` (`exists_measure_iff`). The measure is unique
(`eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex`). For two coordinates this is
Hausdorff's moment problem on `[0, 1]`, with `a (j, k) = ∫ t^j (1 - t)^k dμ`: the sum-shift
equation and nonnegativity of all `a (j, k)` together are complete monotonicity of
`j ↦ a (j, 0)`.

## Proof

Necessity is immediate from `∑ i, u i = 1` on the simplex. For sufficiency, put
`L(xⁿ) = a n` on the monoid algebra of `ℕ^ι`. The sum-shift equation says that multiplication by
`∑ i, x i` does not change `L`, and the multinomial theorem then gives
`∑_{|k| = K} multinomial(k) a (m + k) = a m` (`sum_multinomial_mul`). With the falling-factorial
identity (`sum_multinomial_descFactorial`) this shows that the positive discrete measures
`∑_{|k| = N + 1} multinomial(k) a k δ_{k / (N + 1)}`, of mass `a 0`, have monomial moments
converging to `a m` (`tendsto_approx_monomialC`). By density of the polynomial functions
(Stone–Weierstrass) and the uniform mass bound, the discrete functionals converge on every
continuous function (`exists_tendsto_approx`). The limit is a positive linear functional, and
the Riesz–Markov–Kakutani theorem (`RealRMK.rieszMeasure`) turns it into the measure.

## Main results

* `MeasureTheory.SatisfiesSumShift`: the sum-shift equation.
* `MeasureTheory.exists_measure_of_satisfiesSumShift`: existence.
* `MeasureTheory.satisfiesSumShift_of_measure`: necessity.
* `MeasureTheory.exists_measure_iff`: **the moment problem on the simplex**.

## References

* F. Hausdorff, *Momentprobleme für ein endliches Intervall*, Math. Z. 16 (1923), 220–248.
-/

@[expose] public noncomputable section

open Finset
open scoped CompactlySupported

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **sum-shift equation** `a n = ∑ i, a (n + e i)`, satisfied by the monomial moments of a
measure on the simplex because `∑ i, u i = 1` there. -/
def SatisfiesSumShift (a : (ι → ℕ) → ℝ) : Prop :=
  ∀ n, a n = ∑ i, a (n + Pi.single i 1)

namespace SimplexMoment

open AddMonoidAlgebra

/-- The linear functional on the monoid algebra of `ℕ^ι` sending the basis element of `n` to
`a n`. -/
def lin (a : (ι → ℕ) → ℝ) (p : AddMonoidAlgebra ℝ (ι → ℕ)) : ℝ :=
  p.coeff.sum fun n c => c * a n

omit [Fintype ι] [DecidableEq ι] in
/-- The functional `lin a` is additive. -/
theorem lin_add (a : (ι → ℕ) → ℝ) (p q : AddMonoidAlgebra ℝ (ι → ℕ)) :
    lin a (p + q) = lin a p + lin a q := by
  unfold lin
  rw [coeff_add, Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)]

omit [Fintype ι] [DecidableEq ι] in
/-- The functional `lin a` on a basis element. -/
theorem lin_single (a : (ι → ℕ) → ℝ) (n : ι → ℕ) (c : ℝ) :
    lin a (single n c) = c * a n := by
  unfold lin
  rw [coeff_single, Finsupp.sum_single_index (by simp)]

omit [Fintype ι] [DecidableEq ι] in
/-- The functional `lin a` commutes with finite sums. -/
theorem lin_sum (a : (ι → ℕ) → ℝ) {κ : Type*} (s : Finset κ)
    (p : κ → AddMonoidAlgebra ℝ (ι → ℕ)) : lin a (∑ k ∈ s, p k) = ∑ k ∈ s, lin a (p k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lin]
  | insert k s hk ih => rw [sum_insert hk, sum_insert hk, lin_add, ih]

/-- The element `∑ i, x i`, `x i` the basis element of `e i`. -/
def sumGen : AddMonoidAlgebra ℝ (ι → ℕ) := ∑ i, single (Pi.single i 1) 1

/-- The sum-shift equation: multiplication by `∑ i, x i` does not change `lin a`. -/
theorem lin_mul_sumGen {a : (ι → ℕ) → ℝ} (ha : SatisfiesSumShift a)
    (p : AddMonoidAlgebra ℝ (ι → ℕ)) : lin a (p * sumGen) = lin a p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp [lin]
  | add p q hp hq => rw [add_mul, lin_add, lin_add, hp, hq]
  | single n c =>
    rw [sumGen, mul_sum, lin_sum, lin_single, ha n, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [single_mul_single, mul_one, lin_single]

/-- Multiplication by `(∑ i, x i)^K` does not change `lin a`. -/
theorem lin_mul_sumGen_pow {a : (ι → ℕ) → ℝ} (ha : SatisfiesSumShift a)
    (p : AddMonoidAlgebra ℝ (ι → ℕ)) (K : ℕ) : lin a (p * sumGen ^ K) = lin a p := by
  induction K with
  | zero => simp
  | succ K ih => rw [pow_succ, ← mul_assoc, lin_mul_sumGen ha, ih]

/-- The multinomial theorem for `(∑ i, x i)^K` in the monoid algebra of `ℕ^ι`. -/
theorem sumGen_pow (K : ℕ) :
    (sumGen : AddMonoidAlgebra ℝ (ι → ℕ)) ^ K =
      ∑ k ∈ piAntidiag univ K, single k (Nat.multinomial univ k : ℝ) := by
  rw [sumGen, sum_pow_eq_sum_piAntidiag]
  refine sum_congr rfl fun k _ => ?_
  simp_rw [single_pow, one_pow]
  rw [prod_single, prod_const_one]
  have hk : ∑ i, k i • (Pi.single i 1 : ι → ℕ) = k := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [hk]
  simp [natCast_def, single_mul_single]

/-- Iterating the sum-shift equation: `∑_{|k| = K} multinomial(k) a(m + k) = a m`. -/
theorem sum_multinomial_mul {a : (ι → ℕ) → ℝ} (ha : SatisfiesSumShift a) (m : ι → ℕ) (K : ℕ) :
    ∑ k ∈ piAntidiag univ K, (Nat.multinomial univ k : ℝ) * a (m + k) = a m := by
  have h := lin_mul_sumGen_pow ha (single m 1) K
  rw [sumGen_pow, mul_sum, lin_sum, lin_single, one_mul] at h
  rw [← h]
  refine sum_congr rfl fun k _ => ?_
  rw [single_mul_single, one_mul, lin_single]

omit [DecidableEq ι] in
/-- `multinomial(m + k) ∏ (m i + k i)_(m i) = (N)_M multinomial(k)` with `N = |m + k|`,
`M = |m|`. -/
theorem multinomial_add_mul_prod_descFactorial (m k : ι → ℕ) :
    (Nat.multinomial univ (m + k) : ℝ) * ∏ i, (((m + k) i).descFactorial (m i) : ℝ) =
      ((∑ i, (m + k) i).descFactorial (∑ i, m i) : ℝ) * Nat.multinomial univ k := by
  set N := ∑ i, (m + k) i
  set M := ∑ i, m i
  have hNM : N - M = ∑ i, k i := by
    simp only [N, M, Pi.add_apply, sum_add_distrib]; omega
  have h1 : (∏ i, (((m + k) i).factorial : ℝ)) * Nat.multinomial univ (m + k) = N.factorial := by
    exact_mod_cast Nat.multinomial_spec univ (m + k)
  have h2 : (∏ i, ((k i).factorial : ℝ)) * Nat.multinomial univ k = (N - M).factorial := by
    rw [hNM]; exact_mod_cast Nat.multinomial_spec univ k
  have h3 : (∏ i, ((k i).factorial : ℝ)) * ∏ i, (((m + k) i).descFactorial (m i) : ℝ) =
      ∏ i, (((m + k) i).factorial : ℝ) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    have := Nat.factorial_mul_descFactorial (n := (m + k) i) (k := m i) (by simp)
    simp only [Pi.add_apply, Nat.add_sub_cancel_left] at this ⊢
    exact_mod_cast this
  have hMN : M ≤ N := by
    simp only [N, M, Pi.add_apply, sum_add_distrib]
    exact Nat.le_add_right _ _
  have h4 : ((N - M).factorial : ℝ) * N.descFactorial M = N.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hMN
  have hQ : (∏ i, ((k i).factorial : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  refine mul_left_cancel₀ hQ ?_
  calc (∏ i, ((k i).factorial : ℝ)) * ((Nat.multinomial univ (m + k) : ℝ) *
        ∏ i, (((m + k) i).descFactorial (m i) : ℝ))
      = (Nat.multinomial univ (m + k) : ℝ) * ((∏ i, ((k i).factorial : ℝ)) *
          ∏ i, (((m + k) i).descFactorial (m i) : ℝ)) := by ring
    _ = N.factorial := by rw [h3, mul_comm, h1]
    _ = _ := by rw [← h4, ← h2]; ring

/-- The **falling-factorial identity**: for `|m| ≤ N`,
`∑_{|k| = N} multinomial(k) ∏ (k i)_(m i) a k = (N)_|m| a m`. -/
theorem sum_multinomial_descFactorial {a : (ι → ℕ) → ℝ} (ha : SatisfiesSumShift a)
    (m : ι → ℕ) {N : ℕ} (hN : ∑ i, m i ≤ N) :
    ∑ k ∈ piAntidiag univ N,
        (Nat.multinomial univ k : ℝ) * (∏ i, ((k i).descFactorial (m i) : ℝ)) * a k =
      (N.descFactorial (∑ i, m i) : ℝ) * a m := by
  set f : (ι → ℕ) → ℝ := fun k =>
    (N.descFactorial (∑ i, m i) : ℝ) * ((Nat.multinomial univ k : ℝ) * a (m + k))
  set g : (ι → ℕ) → ℝ := fun k =>
    (Nat.multinomial univ k : ℝ) * (∏ i, ((k i).descFactorial (m i) : ℝ)) * a k
  have hfg : ∀ k ∈ piAntidiag univ (N - ∑ i, m i), f k = g (m + k) := by
    intro k hk
    have hk' : ∑ i, k i = N - ∑ i, m i := (mem_piAntidiag.mp hk).1
    have hrel := multinomial_add_mul_prod_descFactorial m k
    have hsum : ∑ i, (m + k) i = N := by
      simp only [Pi.add_apply, sum_add_distrib, hk']; omega
    rw [hsum] at hrel
    simp only [f, g]
    rw [hrel]
    ring
  rw [← sum_multinomial_mul ha m (N - ∑ i, m i), mul_sum]
  change ∑ k ∈ piAntidiag univ N, g k = ∑ k ∈ piAntidiag univ (N - ∑ i, m i), f k
  symm
  refine sum_bij_ne_zero (fun k _ _ => m + k) ?_ ?_ ?_ (fun k hk _ => hfg k hk)
  · intro k hk _
    have hk' : ∑ i, k i = N - ∑ i, m i := (mem_piAntidiag.mp hk).1
    rw [mem_piAntidiag]
    refine ⟨?_, fun _ _ => mem_univ _⟩
    show ∑ i, (m + k) i = N
    simp only [Pi.add_apply, sum_add_distrib, hk']
    omega
  · intro k₁ _ _ k₂ _ _ h
    exact add_left_cancel h
  · intro k hk hne
    have hle : ∀ i, m i ≤ k i := by
      intro i
      by_contra hlt
      apply hne
      have : (k i).descFactorial (m i) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp only [g]
      rw [prod_eq_zero (mem_univ i) (by exact_mod_cast this), mul_zero, zero_mul]
    have hk' : ∑ i, k i = N := (mem_piAntidiag.mp hk).1
    have hkm : m + (k - m) = k := funext fun i => by
      simp only [Pi.add_apply, Pi.sub_apply]; have := hle i; omega
    have hmem : k - m ∈ piAntidiag univ (N - ∑ i, m i) := by
      rw [mem_piAntidiag]
      refine ⟨?_, fun _ _ => mem_univ _⟩
      have : ∑ i, (k - m) i + ∑ i, m i = ∑ i, k i := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; have := hle i; omega
      show ∑ i, (k - m) i = N - ∑ i, m i
      omega
    refine ⟨k - m, hmem, ?_, hkm⟩
    rw [hfg _ hmem, hkm]
    exact hne

/-! ### Discrete approximations -/

/-- The grid point `k / (N + 1)`. -/
def gridPoint (N : ℕ) (k : ι → ℕ) : ι → ℝ := fun i => (k i : ℝ) / (N + 1)

/-- Grid points of a composition of `N + 1` lie in the simplex. -/
theorem gridPoint_mem {N : ℕ} {k : ι → ℕ} (hk : k ∈ piAntidiag univ (N + 1)) :
    gridPoint N k ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
  refine ⟨fun i => by unfold gridPoint; positivity, ?_⟩
  have hk' : ∑ i, k i = N + 1 := (mem_piAntidiag.mp hk).1
  simp only [gridPoint, ← sum_div]
  rw [div_eq_one_iff_eq (by positivity)]
  exact_mod_cast hk'

open Classical in
/-- The discrete approximating functional
`f ↦ ∑_{|k| = N + 1} multinomial(k) a k f(k / (N + 1))` on functions on the simplex. -/
def approx (a : (ι → ℕ) → ℝ) (N : ℕ)
    (f : Convexity.StdSimplex.coordinateSet ℝ ι → ℝ) : ℝ :=
  ∑ k ∈ piAntidiag univ (N + 1), (Nat.multinomial univ k : ℝ) * a k *
    (if h : gridPoint N k ∈ Convexity.StdSimplex.coordinateSet ℝ ι then f ⟨_, h⟩ else 0)

/-- The discrete approximation is additive. -/
theorem approx_add (a : (ι → ℕ) → ℝ) (N : ℕ) (f g : Convexity.StdSimplex.coordinateSet ℝ ι → ℝ) :
    approx a N (f + g) = approx a N f + approx a N g := by
  unfold approx
  rw [← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [mul_add]

/-- The discrete approximation is homogeneous. -/
theorem approx_smul (a : (ι → ℕ) → ℝ) (N : ℕ) (c : ℝ)
    (f : Convexity.StdSimplex.coordinateSet ℝ ι → ℝ) :
    approx a N (c • f) = c * approx a N f := by
  unfold approx
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  split_ifs <;> simp; ring

/-- The discrete approximation is positive. -/
theorem approx_nonneg {a : (ι → ℕ) → ℝ} (ha : ∀ n, 0 ≤ a n) (N : ℕ)
    {f : Convexity.StdSimplex.coordinateSet ℝ ι → ℝ} (hf : ∀ u, 0 ≤ f u) :
    0 ≤ approx a N f := by
  refine sum_nonneg fun k _ => mul_nonneg (mul_nonneg (by positivity) (ha k)) ?_
  split_ifs
  · exact hf _
  · exact le_rfl

/-- The total mass of the discrete approximation is `a 0`. -/
theorem sum_multinomial_mul_self {a : (ι → ℕ) → ℝ} (ha : SatisfiesSumShift a) (K : ℕ) :
    ∑ k ∈ piAntidiag univ K, (Nat.multinomial univ k : ℝ) * a k = a 0 := by
  simpa using sum_multinomial_mul ha 0 K

/-- The discrete approximation is bounded by `a 0` times a bound for the function. -/
theorem abs_approx_le {a : (ι → ℕ) → ℝ} (ha₀ : ∀ n, 0 ≤ a n) (ha : SatisfiesSumShift a) (N : ℕ)
    {f : Convexity.StdSimplex.coordinateSet ℝ ι → ℝ} {B : ℝ} (hf : ∀ u, |f u| ≤ B) :
    |approx a N f| ≤ a 0 * B := by
  rw [← sum_multinomial_mul_self ha (N + 1), sum_mul]
  unfold approx
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  rw [abs_mul, abs_of_nonneg (mul_nonneg (by positivity) (ha₀ k)),
    dite_eq_left_of_eq_true (eq_true (gridPoint_mem hk))]
  exact mul_le_mul_of_nonneg_left (hf _) (mul_nonneg (by positivity) (ha₀ k))

omit [Fintype ι] [DecidableEq ι] in
/-- The falling factorial as a real product. -/
theorem descFactorial_cast (n m : ℕ) :
    (n.descFactorial m : ℝ) = ∏ j ∈ range m, ((n : ℝ) - j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.descFactorial_succ, prod_range_succ, Nat.cast_mul, ih, mul_comm]
    by_cases hmn : m ≤ n
    · rw [Nat.cast_sub hmn]
    · have h0 : n.descFactorial m = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [← ih]
      simp [h0]

omit [Fintype ι] [DecidableEq ι] in
/-- Products of numbers in `[-1, 1]` differ by at most the sum of the differences. -/
theorem abs_prod_sub_prod_le {κ : Type*} (s : Finset κ) {x y : κ → ℝ}
    (hx : ∀ i ∈ s, |x i| ≤ 1) (hy : ∀ i ∈ s, |y i| ≤ 1) :
    |∏ i ∈ s, x i - ∏ i ∈ s, y i| ≤ ∑ i ∈ s, |x i - y i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
    rw [prod_insert hc, prod_insert hc, sum_insert hc]
    have ih' := ih (fun i hi => hx i (mem_insert_of_mem hi))
      (fun i hi => hy i (mem_insert_of_mem hi))
    have hxc := hx c (mem_insert_self c s)
    have hPy : |∏ i ∈ s, y i| ≤ 1 := by
      rw [abs_prod]
      exact prod_le_one₀ (fun _ _ => abs_nonneg _) fun i hi => hy i (mem_insert_of_mem hi)
    calc |x c * ∏ i ∈ s, x i - y c * ∏ i ∈ s, y i|
        = |x c * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x c - y c) * ∏ i ∈ s, y i| := by ring_nf
      _ ≤ |x c| * |∏ i ∈ s, x i - ∏ i ∈ s, y i| + |x c - y c| * |∏ i ∈ s, y i| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * ∑ i ∈ s, |x i - y i| + |x c - y c| * 1 := by gcongr
      _ = |x c - y c| + ∑ i ∈ s, |x i - y i| := by ring

/-- The monomial `u ↦ ∏ i, u i ^ m i` as a continuous function on the simplex. -/
def monomialC (m : ι → ℕ) : C(Convexity.StdSimplex.coordinateSet ℝ ι, ℝ) :=
  ⟨fun u => ∏ i, (u : ι → ℝ) i ^ m i,
    continuous_finsetProd _ fun i _ => ((continuous_apply i).comp continuous_subtype_val).pow _⟩

/-- The falling-factorial polynomial `∏ i, ∏_{j < m i} (u i - j / (N + 1))`. -/
def fallingC (m : ι → ℕ) (N : ℕ) (u : Convexity.StdSimplex.coordinateSet ℝ ι) : ℝ :=
  ∏ i, ∏ j ∈ range (m i), ((u : ι → ℝ) i - j / (N + 1))

/-- On the falling-factorial polynomial the discrete approximation is exactly
`(N + 1)_M / (N + 1)^M · a m`, by the falling-factorial identity. -/
theorem approx_fallingC {a : (ι → ℕ) → ℝ} (ha : SatisfiesSumShift a) (m : ι → ℕ) {N : ℕ}
    (hN : ∑ i, m i ≤ N + 1) :
    approx a N (fallingC m N) =
      ((N + 1).descFactorial (∑ i, m i) : ℝ) / ((N + 1 : ℝ) ^ ∑ i, m i) * a m := by
  have hpos : (0 : ℝ) < N + 1 := by positivity
  rw [div_mul_eq_mul_div, ← sum_multinomial_descFactorial ha m hN, sum_div]
  unfold approx
  refine sum_congr rfl fun k hk => ?_
  rw [dite_eq_left_of_eq_true (eq_true (gridPoint_mem hk))]
  simp only [fallingC, gridPoint]
  have hterm : ∏ i, ∏ j ∈ range (m i), ((k i : ℝ) / (N + 1) - j / (N + 1)) =
      (∏ i, ((k i).descFactorial (m i) : ℝ)) / (N + 1 : ℝ) ^ ∑ i, m i := by
    rw [← prod_pow_eq_pow_sum, ← prod_div_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [descFactorial_cast, ← card_range (m i), ← prod_const, card_range, ← prod_div_distrib]
    refine prod_congr rfl fun j _ => ?_
    field_simp
  rw [hterm]
  ring

omit [DecidableEq ι] in
/-- On the simplex, the monomial and the falling-factorial polynomial differ by at most
`M² / (N + 1)`, `M = |m|`. -/
theorem abs_monomialC_sub_fallingC_le (m : ι → ℕ) {N : ℕ} (hN : ∑ i, m i ≤ N + 1)
    (u : Convexity.StdSimplex.coordinateSet ℝ ι) :
    |monomialC m u - fallingC m N u| ≤ ((∑ i, m i : ℕ) : ℝ) ^ 2 / (N + 1) := by
  have hpos : (0 : ℝ) < N + 1 := by positivity
  have hu0 : ∀ i, 0 ≤ (u : ι → ℝ) i := fun i => u.2.1 i
  have hu1 : ∀ i, (u : ι → ℝ) i ≤ 1 :=
    fun i => (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet u.2 i).2
  set M : ℕ := ∑ i, m i
  have hmi : ∀ i, m i ≤ M := fun i =>
    single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hmon : monomialC m u = ∏ x ∈ univ.sigma fun i => range (m i), (u : ι → ℝ) x.1 := by
    rw [prod_sigma]
    simp only [prod_const, card_range]
    rfl
  have hfall : fallingC m N u =
      ∏ x ∈ univ.sigma fun i => range (m i), ((u : ι → ℝ) x.1 - x.2 / (N + 1)) := by
    rw [prod_sigma]; rfl
  rw [hmon, hfall]
  have hjN : ∀ x ∈ univ.sigma fun i => range (m i), (x.2 : ℝ) / (N + 1) ≤ M / (N + 1) := by
    intro x hx
    have hx2 : x.2 < m x.1 := mem_range.mp (mem_sigma.mp hx).2
    gcongr
    exact_mod_cast (hx2.le.trans (hmi x.1))
  have hM1 : (M : ℝ) / (N + 1) ≤ 1 := by
    rw [div_le_one hpos]; exact_mod_cast hN
  refine (abs_prod_sub_prod_le _ (fun x _ => by
      rw [abs_of_nonneg (hu0 _)]; exact hu1 _) (fun x hx => ?_)).trans ?_
  · rw [abs_le]
    have := hjN x hx
    constructor <;> nlinarith [hu0 x.1, hu1 x.1, div_nonneg (Nat.cast_nonneg (α := ℝ) x.2) hpos.le]
  · calc ∑ x ∈ univ.sigma (fun i => range (m i)),
          |(u : ι → ℝ) x.1 - ((u : ι → ℝ) x.1 - x.2 / (N + 1))|
        ≤ ∑ x ∈ univ.sigma (fun i => range (m i)), (M : ℝ) / (N + 1) := by
          refine sum_le_sum fun x hx => ?_
          rw [sub_sub_cancel, abs_of_nonneg (by positivity)]
          exact hjN x hx
      _ = (M : ℝ) ^ 2 / (N + 1) := by
          rw [sum_const, card_sigma]
          simp only [card_range]
          rw [nsmul_eq_mul]
          ring

/-- **Convergence of the moments of the discrete approximations.** -/
theorem tendsto_approx_monomialC {a : (ι → ℕ) → ℝ} (ha₀ : ∀ n, 0 ≤ a n)
    (ha : SatisfiesSumShift a) (m : ι → ℕ) :
    Filter.Tendsto (fun N => approx a N (monomialC m)) Filter.atTop (nhds (a m)) := by
  set M : ℕ := ∑ i, m i
  -- The ratio `(N + 1)_M / (N + 1)^M` tends to one.
  have hratio : Filter.Tendsto
      (fun N : ℕ => ((N + 1).descFactorial M : ℝ) / ((N + 1 : ℝ) ^ M)) Filter.atTop (nhds 1) := by
    have hfac : ∀ N : ℕ, ((N + 1).descFactorial M : ℝ) / ((N + 1 : ℝ) ^ M) =
        ∏ j ∈ range M, (1 - (j : ℝ) / (N + 1)) := by
      intro N
      rw [descFactorial_cast, ← card_range M, ← prod_const, card_range, ← prod_div_distrib]
      refine prod_congr rfl fun j _ => ?_
      push_cast
      field_simp
    simp_rw [hfac]
    have hj : ∀ j : ℕ, Filter.Tendsto (fun N : ℕ => (j : ℝ) / (N + 1)) Filter.atTop (nhds 0) := by
      intro j
      have := (tendsto_const_div_atTop_nhds_zero_nat (j : ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    have h := tendsto_finsetProd (range M) fun j (_ : j ∈ range M) =>
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hj j)
    simpa using h
  have hmain : Filter.Tendsto (fun N => approx a N (fallingC m N)) Filter.atTop (nhds (a m)) := by
    have h := hratio.mul_const (a m)
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop M] with N hN
    rw [approx_fallingC ha m (by omega)]
  have herr : Filter.Tendsto (fun N : ℕ => a 0 * ((M : ℝ) ^ 2 / (N + 1))) Filter.atTop
      (nhds 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat ((M : ℝ) ^ 2)).comp
      (Filter.tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this.const_mul (a 0)
  rw [← sub_zero (a m)]
  have hdiff : Filter.Tendsto (fun N => approx a N (monomialC m) - approx a N (fallingC m N))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [Filter.eventually_ge_atTop M] with N hN
    have hsub : approx a N (monomialC m) - approx a N (fallingC m N) =
        approx a N (fun u => monomialC m u - fallingC m N u) := by
      rw [sub_eq_add_neg, show (fun u => monomialC m u - fallingC m N u) =
        (fun u => monomialC m u) + (-1 : ℝ) • fallingC m N by funext u; simp; ring,
        approx_add, approx_smul]
      ring
    rw [hsub, Real.norm_eq_abs]
    exact abs_approx_le ha₀ ha N fun u => abs_monomialC_sub_fallingC_le m (N := N) (by omega) u
  have := hmain.add hdiff
  simpa [sub_eq_add_neg, add_comm] using this

/-! ### The limit functional -/

/-- The coordinate function `u ↦ u i` on the simplex. -/
def coordC (i : ι) : C(Convexity.StdSimplex.coordinateSet ℝ ι, ℝ) :=
  ⟨fun u => (u : ι → ℝ) i, (continuous_apply i).comp continuous_subtype_val⟩

/-- The polynomial functions on the simplex. -/
def polyAlg : Subalgebra ℝ C(Convexity.StdSimplex.coordinateSet ℝ ι, ℝ) :=
  Algebra.adjoin ℝ (Set.range (coordC (ι := ι)))

omit [DecidableEq ι] in
/-- The polynomial functions separate the points of the simplex. -/
theorem polyAlg_separatesPoints : (polyAlg (ι := ι)).SeparatesPoints := by
  intro x y hxy
  have : ∃ i, (x : ι → ℝ) i ≠ (y : ι → ℝ) i := by
    by_contra h
    push Not at h
    exact hxy (Subtype.ext (funext h))
  obtain ⟨i, hi⟩ := this
  exact ⟨coordC i, ⟨coordC i, Algebra.subset_adjoin ⟨i, rfl⟩, rfl⟩, hi⟩

/-- Products of coordinate functions are monomials. -/
theorem exists_monomialC_of_mem_closure {f : C(Convexity.StdSimplex.coordinateSet ℝ ι, ℝ)}
    (hf : f ∈ Submonoid.closure (Set.range (coordC (ι := ι)))) :
    ∃ m : ι → ℕ, f = monomialC m := by
  induction hf using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨i, rfl⟩ := hf
    refine ⟨Pi.single i 1, ?_⟩
    ext u
    simp only [coordC, monomialC, ContinuousMap.coe_mk]
    rw [prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  | one => exact ⟨0, by ext u; simp [monomialC]⟩
  | mul f g _ _ hf hg =>
    obtain ⟨m, rfl⟩ := hf
    obtain ⟨n, rfl⟩ := hg
    refine ⟨m + n, ?_⟩
    ext u
    simp only [monomialC, ContinuousMap.mul_apply, ContinuousMap.coe_mk, Pi.add_apply, pow_add,
      prod_mul_distrib]

/-- The discrete approximation of a difference. -/
theorem approx_sub (a : (ι → ℕ) → ℝ) (N : ℕ) (f g : Convexity.StdSimplex.coordinateSet ℝ ι → ℝ) :
    approx a N f - approx a N g = approx a N (f - g) := by
  rw [show f - g = f + (-1 : ℝ) • g by funext u; simp; ring, approx_add, approx_smul]
  ring

/-- **The discrete approximations converge** on every continuous function on the simplex: on
polynomials by the moment convergence, in general by density (Stone–Weierstrass) and the uniform
bound `|approx f| ≤ a 0 ‖f‖`. -/
theorem exists_tendsto_approx {a : (ι → ℕ) → ℝ} (ha₀ : ∀ n, 0 ≤ a n) (ha : SatisfiesSumShift a)
    (f : C(Convexity.StdSimplex.coordinateSet ℝ ι, ℝ)) :
    ∃ l, Filter.Tendsto (fun N => approx a N f) Filter.atTop (nhds l) := by
  -- The functions along which the approximations converge form a submodule.
  let V : Submodule ℝ C(Convexity.StdSimplex.coordinateSet ℝ ι, ℝ) :=
    { carrier := {f | ∃ l, Filter.Tendsto (fun N => approx a N f) Filter.atTop (nhds l)}
      add_mem' := by
        rintro f g ⟨l, hl⟩ ⟨l', hl'⟩
        refine ⟨l + l', (hl.add hl').congr fun N => ?_⟩
        rw [ContinuousMap.coe_add, approx_add]
      zero_mem' := ⟨0, by
        refine tendsto_const_nhds.congr fun N => ?_
        rw [ContinuousMap.coe_zero, show (0 : Convexity.StdSimplex.coordinateSet ℝ ι → ℝ) =
          (0 : ℝ) • (0 : Convexity.StdSimplex.coordinateSet ℝ ι → ℝ) by simp, approx_smul,
          zero_mul]⟩
      smul_mem' := by
        rintro c f ⟨l, hl⟩
        refine ⟨c * l, (hl.const_mul c).congr fun N => ?_⟩
        rw [ContinuousMap.coe_smul, approx_smul] }
  have hA : ∀ g ∈ polyAlg (ι := ι), g ∈ V := by
    intro g hg
    have hg' : g ∈ Submodule.span ℝ
        (Submonoid.closure (Set.range (coordC (ι := ι))) : Set C(_, ℝ)) := by
      rw [← Algebra.adjoin_eq_span]; exact hg
    refine (Submodule.span_le.mpr (fun h hh => ?_)) hg'
    obtain ⟨m, rfl⟩ := exists_monomialC_of_mem_closure hh
    exact ⟨a m, tendsto_approx_monomialC ha₀ ha m⟩
  -- Density of the polynomial functions.
  have hdense : f ∈ closure (polyAlg (ι := ι) : Set C(_, ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe,
      ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
        polyAlg_separatesPoints]
    trivial
  -- The approximations along `f` form a Cauchy sequence.
  have hbd : ∀ (N : ℕ) (h : C(Convexity.StdSimplex.coordinateSet ℝ ι, ℝ)),
      |approx a N h| ≤ a 0 * ‖h‖ := fun N h =>
    abs_approx_le ha₀ ha N fun u => by
      rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm u
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr fun ε hε => ?_)
  set δ := ε / (4 * (a 0 + 1))
  have ha0 : 0 ≤ a 0 := ha₀ 0
  have hδ : 0 < δ := by positivity
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hdense δ hδ
  obtain ⟨l, hl⟩ := hA g hg
  obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff.mp hl.cauchySeq (ε / 2) (by positivity)
  refine ⟨N₀, fun n hn n' hn' => ?_⟩
  have h1 : |approx a n f - approx a n g| ≤ a 0 * δ := by
    rw [approx_sub, ← ContinuousMap.coe_sub]
    refine (hbd n _).trans (mul_le_mul_of_nonneg_left ?_ ha0)
    rw [← dist_eq_norm]; exact hfg.le
  have h2 : |approx a n' f - approx a n' g| ≤ a 0 * δ := by
    rw [approx_sub, ← ContinuousMap.coe_sub]
    refine (hbd n' _).trans (mul_le_mul_of_nonneg_left ?_ ha0)
    rw [← dist_eq_norm]; exact hfg.le
  have h3 := hN₀ n hn n' hn'
  rw [Real.dist_eq] at h3 ⊢
  have hδε : a 0 * δ ≤ ε / 4 := by
    simp only [δ]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc |approx a n f - approx a n' f|
      ≤ |approx a n f - approx a n g| + |approx a n g - approx a n' g| +
          |approx a n' f - approx a n' g| := by
        have e1 := abs_sub_le (approx a n f) (approx a n g) (approx a n' f)
        have e2 := abs_sub_le (approx a n g) (approx a n' g) (approx a n' f)
        rw [abs_sub_comm (approx a n' g) (approx a n' f)] at e2
        linarith
    _ < ε := by linarith

/-- The limit of the discrete approximations. -/
def limFun (a : (ι → ℕ) → ℝ) (f : Convexity.StdSimplex.coordinateSet ℝ ι → ℝ) : ℝ :=
  Filter.atTop.limUnder fun N => approx a N f

/-- The discrete approximations of a continuous function converge to the limit functional. -/
theorem tendsto_limFun {a : (ι → ℕ) → ℝ} (ha₀ : ∀ n, 0 ≤ a n) (ha : SatisfiesSumShift a)
    (f : C(Convexity.StdSimplex.coordinateSet ℝ ι, ℝ)) :
    Filter.Tendsto (fun N => approx a N f) Filter.atTop (nhds (limFun a f)) :=
  tendsto_nhds_limUnder (exists_tendsto_approx ha₀ ha f)

/-- The limit functional as a positive linear functional on `C_c(Δ, ℝ) = C(Δ, ℝ)`. -/
def rieszFunctional {a : (ι → ℕ) → ℝ} (ha₀ : ∀ n, 0 ≤ a n) (ha : SatisfiesSumShift a) :
    C_c(Convexity.StdSimplex.coordinateSet ℝ ι, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => limFun a f
      map_add' := fun f g => by
        have h := (tendsto_limFun ha₀ ha f.toContinuousMap).add
          (tendsto_limFun ha₀ ha g.toContinuousMap)
        refine tendsto_nhds_unique (tendsto_limFun ha₀ ha (f + g).toContinuousMap)
          (h.congr fun N => ?_)
        rw [← approx_add]; rfl
      map_smul' := fun c f => by
        have h := (tendsto_limFun ha₀ ha f.toContinuousMap).const_mul c
        refine tendsto_nhds_unique (tendsto_limFun ha₀ ha (c • f).toContinuousMap)
          (h.congr fun N => ?_)
        rw [← approx_smul]; rfl }
    fun f hf => ge_of_tendsto' (tendsto_limFun ha₀ ha f.toContinuousMap)
      fun N => approx_nonneg ha₀ N fun u => hf u

end SimplexMoment

open SimplexMoment

/-- **Existence for the moment problem on the simplex.** A nonnegative sequence on `ℕ^ι` with the
sum-shift equation `a n = ∑ i, a (n + e i)` is the sequence of monomial moments of a finite
measure supported on the simplex. -/
theorem exists_measure_of_satisfiesSumShift {a : (ι → ℕ) → ℝ} (ha₀ : ∀ n, 0 ≤ a n)
    (ha : SatisfiesSumShift a) :
    ∃ μ : Measure (ι → ℝ), IsFiniteMeasure μ ∧
      μ.restrict (Convexity.StdSimplex.coordinateSet ℝ ι) = μ ∧
      ∀ m : ι → ℕ, ∫ u, (∏ i, u i ^ m i) ∂μ = a m := by
  set Λ := rieszFunctional ha₀ ha
  set μS := RealRMK.rieszMeasure Λ
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  refine ⟨μS.map Subtype.val, inferInstance, ?_, fun m => ?_⟩
  · rw [Measure.restrict_map measurable_subtype_coe hS]
    congr 1
    convert Measure.restrict_univ (μ := μS)
    ext u
    simp
  · rw [integral_map measurable_subtype_coe.aemeasurable
      (by fun_prop : Continuous fun u : ι → ℝ => ∏ i, u i ^ m i).aestronglyMeasurable]
    have h := RealRMK.integral_rieszMeasure Λ
      (CompactlySupportedContinuousMap.continuousMapEquiv (monomialC m))
    have hΛ : Λ (CompactlySupportedContinuousMap.continuousMapEquiv (monomialC m)) = a m :=
      tendsto_nhds_unique (tendsto_limFun ha₀ ha _) (tendsto_approx_monomialC ha₀ ha m)
    rw [hΛ] at h
    rw [← h]
    rfl

/-- **Necessity.** The monomial moments of a finite measure supported on the simplex are
nonnegative and satisfy the sum-shift equation. -/
theorem satisfiesSumShift_of_measure {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ ι) = μ) :
    (∀ m : ι → ℕ, 0 ≤ ∫ u, (∏ i, u i ^ m i) ∂μ) ∧
      SatisfiesSumShift fun m => ∫ u, (∏ i, u i ^ m i) ∂μ := by
  have hS := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  have hae := ae_mem_of_restrict_eq_self hS hμ
  refine ⟨fun m => integral_nonneg_of_ae ?_, fun m => ?_⟩
  · filter_upwards [hae] with u hu
    exact prod_nonneg fun i _ => pow_nonneg (hu.1 i) _
  · have hint : ∀ n : ι → ℕ, Integrable (fun u : ι → ℝ => ∏ i, u i ^ n i) μ := fun n =>
      integrable_of_continuous_of_restrict_stdSimplex hμ (by fun_prop)
    simp only
    rw [← integral_finsetSum _ fun i _ => hint _]
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    have hshift : ∀ i, ∏ j, u j ^ (m + Pi.single i 1 : ι → ℕ) j = u i * ∏ j, u j ^ m j := by
      intro i
      simp only [Pi.add_apply, pow_add, prod_mul_distrib]
      rw [mul_comm]
      congr 1
      rw [prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
      simp
    simp only [hshift, ← sum_mul, hu.2, one_mul]

/-- **The moment problem on the simplex.** A sequence on `ℕ^ι` is the sequence of monomial moments
of a finite measure supported on the simplex if and only if it is nonnegative and satisfies the
sum-shift equation. The measure is unique
(`eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex`). -/
theorem exists_measure_iff (a : (ι → ℕ) → ℝ) :
    (∃ μ : Measure (ι → ℝ), IsFiniteMeasure μ ∧
      μ.restrict (Convexity.StdSimplex.coordinateSet ℝ ι) = μ ∧
      ∀ m : ι → ℕ, ∫ u, (∏ i, u i ^ m i) ∂μ = a m) ↔
    (∀ n, 0 ≤ a n) ∧ SatisfiesSumShift a := by
  constructor
  · rintro ⟨μ, hμf, hμ, hm⟩
    have h := satisfiesSumShift_of_measure hμ
    have ha : a = fun m => ∫ u, (∏ i, u i ^ m i) ∂μ := funext fun m => (hm m).symm
    rw [ha]
    exact h
  · rintro ⟨ha₀, ha⟩
    exact exists_measure_of_satisfiesSumShift ha₀ ha


end MeasureTheory
