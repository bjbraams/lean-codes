/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.AlgebraicExpansion
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Monic Jacobi polynomials with arbitrary endpoints

The shifted monic Jacobi polynomial is transported from endpoints `1, 0` to
`r, s` by scaling its roots and then translating. This construction involves
no division by `r-s`. At coincident endpoints it gives `(X-s)^n`, the polynomial
in Taylor's formula. Parameter-dependent normalization still requires the
nonvanishing leading Pochhammer factor.

## Main results

* `monic_jacobiOn`: monicity for every pair of endpoints.
* `jacobiOn_self`: reduction to Taylor monomials at coincident endpoints.
* `eval_jacobiOn_affine`: affine-coordinate evaluation.
* `iterate_derivative_comp_affine`: polynomial differentiation under an affine
  substitution, used to transport derivative-average coefficients.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, Definition 7.1-1 and Theorem 7.2-2.
-/

@[expose] public noncomputable section
namespace Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- The monic normalization of the shifted Jacobi polynomial. -/
def monicShiftedJacobi (α β : K) (n : ℕ) : K[X] :=
  C ((n.factorial : K) / ((-1 : K) ^ n *
    (ascPochhammer K n).eval (α + β + n + 1))) * shiftedJacobi α β n

/-- The shifted monic normalization retains the expected degree when its
normalizing Pochhammer factor is nonzero. -/
theorem natDegree_monicShiftedJacobi (α β : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    (monicShiftedJacobi α β n).natDegree = n := by
  rw [monicShiftedJacobi, natDegree_C_mul (div_ne_zero
    (by exact_mod_cast n.factorial_ne_zero) (mul_ne_zero (pow_ne_zero _ (by norm_num)) h))]
  exact natDegree_eq_of_degree_eq_some (degree_shiftedJacobi α β n h)

/-- Monicity of the shifted normalization at nonsingular parameters. -/
theorem monic_monicShiftedJacobi (α β : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    (monicShiftedJacobi α β n).Monic := by
  rw [Monic, leadingCoeff, natDegree_monicShiftedJacobi α β n h,
    monicShiftedJacobi, coeff_C_mul, coeff_shiftedJacobi_self]
  norm_num only [map_div₀, map_pow, map_neg, map_one, map_natCast]
  have hf : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- Carlson's monic Jacobi polynomial with endpoints `r, s`, constructed without
division by their difference. The first beta parameter corresponds to `r`. -/
def jacobiOn (α β r s : K) (n : ℕ) : K[X] :=
  ((monicShiftedJacobi α β n).scaleRoots (r - s)).comp (X - C s)

/-- The endpoint polynomial is monic, even at coincident endpoints. -/
theorem monic_jacobiOn (α β r s : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    (jacobiOn α β r s n).Monic :=
  ((monic_scaleRoots_iff (r - s)).mpr (monic_monicShiftedJacobi α β n h)).comp_X_sub_C s

/-- The endpoint polynomial retains degree `n`, including at coincident endpoints. -/
theorem natDegree_jacobiOn (α β r s : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    (jacobiOn α β r s n).natDegree = n := by
  simp only [jacobiOn, natDegree_comp, natDegree_X_sub_C, mul_one,
    natDegree_scaleRoots, natDegree_monicShiftedJacobi α β n h]

/-- Degree of the monic endpoint polynomial. -/
theorem degree_jacobiOn (α β r s : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    (jacobiOn α β r s n).degree = n := by
  rw [degree_eq_natDegree (monic_jacobiOn α β r s n h).ne_zero,
    natDegree_jacobiOn α β r s n h]

/-- The monic Jacobi sequence at arbitrary endpoints. -/
def jacobiOnSequence (α β r s : K)
    (h : ∀ n, (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) : Sequence K where
  elems' := jacobiOn α β r s
  degree_eq' n := degree_jacobiOn α β r s n (h n)

/-- The monic Jacobi basis at arbitrary endpoints, including the Taylor basis
when the endpoints coincide. -/
def jacobiOnBasis (α β r s : K)
    (h : ∀ n, (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) : Module.Basis ℕ K K[X] :=
  (jacobiOnSequence α β r s h).basis (fun n => isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr ((jacobiOnSequence α β r s h).ne_zero n)))

/-- The vectors of the endpoint Jacobi basis are the monic endpoint polynomials. -/
@[simp] theorem jacobiOnBasis_apply (α β r s : K)
    (h : ∀ n, (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) (n : ℕ) :
    jacobiOnBasis α β r s h n = jacobiOn α β r s n :=
  Sequence.basis_eq_self _ _ n

/-- Coincident endpoints recover the monomials in Taylor's formula. -/
theorem jacobiOn_self (α β s : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    jacobiOn α β s s n = (X - C s) ^ n := by
  simp only [jacobiOn, sub_self, scaleRoots_zero,
    (monic_monicShiftedJacobi α β n h).leadingCoeff,
    natDegree_monicShiftedJacobi α β n h, one_smul, pow_comp, X_comp]

/-- Evaluation in the affine coordinate joining the endpoints. -/
theorem eval_jacobiOn_affine (α β r s x : K) (n : ℕ)
    (h : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0) :
    (jacobiOn α β r s n).eval ((r - s) * x + s) =
      (r - s) ^ n * ((n.factorial : K) /
        ((-1 : K) ^ n * (ascPochhammer K n).eval (α + β + n + 1))) *
          (shiftedJacobi α β n).eval x := by
  simp only [jacobiOn, eval_comp, eval_sub, eval_X, eval_C, add_sub_cancel_right]
  rw [scaleRoots_eval_mul, natDegree_monicShiftedJacobi α β n h]
  simp only [monicShiftedJacobi, eval_mul, eval_C, mul_assoc]

omit [CharZero K] in
/-- Iterated differentiation commutes with an affine substitution, up to the
corresponding power of its slope. -/
theorem iterate_derivative_comp_affine (p : K[X]) (a s : K) (m : ℕ) :
    derivative^[m] (p.comp (C a * X + C s)) =
      C (a ^ m) * (derivative^[m] p).comp (C a * X + C s) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp,
      derivative_add, derivative_mul, derivative_X, mul_one, add_zero, pow_succ,
      C_mul, Function.iterate_succ_apply']
    ring

/-- Taylor's finite formula expressed through iterated ordinary polynomial derivatives. -/
theorem sum_eval_iterate_derivative_div_factorial (p : K[X]) (s x : K) :
    ∑ m ∈ Finset.range (p.natDegree + 1),
      (derivative^[m] p).eval s / (m.factorial : K) * (x - s) ^ m = p.eval x := by
  have ht := (taylor s p).eval_eq_sum_range (x - s)
  rw [taylor_eval_sub, natDegree_taylor] at ht
  rw [ht]
  apply Finset.sum_congr rfl
  intro m _
  rw [taylor_coeff]
  congr 1
  apply (div_eq_iff (show (m.factorial : K) ≠ 0 by exact_mod_cast m.factorial_ne_zero)).mpr
  have hi := congrFun (factorial_smul_hasseDeriv (R := K) (k := m)) p
  change m.factorial • hasseDeriv m p = derivative^[m] p at hi
  have hv := congrArg (eval s) hi
  simpa only [LinearMap.smul_apply, nsmul_eq_mul, eval_mul, eval_natCast, mul_comm] using hv.symm

end Polynomial
