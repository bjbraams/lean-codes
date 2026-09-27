/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.Generating
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Concentration limits of R-polynomials

Carlson's Theorem 6.2-5: for weights `w` with `∑ wᵢ = 1`, the R-polynomials with parameters
`c w` satisfy `Rₙ(c w, z) → ∑ wᵢ zᵢⁿ` as `c → 0` and `Rₙ(c w, z) → (∑ wᵢ zᵢ)ⁿ` as `c → ∞`.
Here `Rₙ(c w, z)` is the Pochhammer numerator divided by `(c)ₙ`, and `c → ∞` means that `c`
leaves every bounded subset of `ℂ`.

The proof follows Carlson: in the multinomial expansion each Pochhammer weight
`∏ (c wᵢ)_{mᵢ} / (c)ₙ` has an explicit limit. As `c → ∞` it tends to `∏ wᵢ^{mᵢ}`, and the
multinomial theorem sums the limits. As `c → 0` it tends to zero unless the multi-index is
concentrated on one node, because every occupied node contributes a factor `c` against a
single factor `c` in `(c)ₙ`.

## Main results

* `Carlson.tendsto_carlsonRPolynomial_concentration_zero`: formula (6.2-17).
* `Carlson.tendsto_carlsonRPolynomial_concentration_cobounded`: formula (6.2-18).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.2.
-/

open Complex Filter Finset Polynomial Bornology
open scoped Topology
@[expose] public noncomputable section

namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- `(c w)ₘ / cᵐ → wᵐ` as `c → ∞`. -/
theorem tendsto_ascPochhammer_mul_div_pow_cobounded (w : ℂ) (m : ℕ) :
    Tendsto (fun c : ℂ => (ascPochhammer ℂ m).eval (c * w) / c ^ m) (cobounded ℂ)
      (𝓝 (w ^ m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hinv := tendsto_inv₀_cobounded (α := ℂ)
    have h1 : Tendsto (fun c : ℂ => w + m * c⁻¹) (cobounded ℂ) (𝓝 w) := by
      simpa using tendsto_const_nhds.add (hinv.const_mul (m : ℂ))
    have hne : ∀ᶠ c : ℂ in cobounded ℂ, c ≠ 0 := by
      simpa using (tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop 0
    refine ((ih.mul h1).congr' ?_).trans (by rw [pow_succ])
    filter_upwards [hne] with c hc
    rw [ascPochhammer_succ_eval, pow_succ]
    field_simp

/-- `(c w)ₘ / c → w (m-1)!` as `c → 0`, for `m ≥ 1`. -/
theorem tendsto_ascPochhammer_mul_div_nhds_zero (w : ℂ) (m : ℕ) :
    Tendsto (fun c : ℂ => (ascPochhammer ℂ (m + 1)).eval (c * w) / c) (𝓝[≠] 0)
      (𝓝 (w * m.factorial)) := by
  have hc : Continuous fun c : ℂ => w * (ascPochhammer ℂ m).eval (c * w + 1) :=
    continuous_const.mul ((Polynomial.continuous _).comp (by fun_prop))
  have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  simp only [zero_mul, zero_add, ascPochhammer_eval_one] at h0
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc0 : c ≠ 0 := hc
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_X, eval_one]
  field_simp

/-- **Theorem 6.2-5**, the limit `c → ∞` (6.2-18): with `∑ wᵢ = 1`,
`Rₙ(c w, z) → (∑ wᵢ zᵢ)ⁿ`, where `Rₙ(c w, z) = Nₙ(c w, z) / (c)ₙ`. -/
theorem tendsto_carlsonRPolynomial_concentration_cobounded (n : ℕ) (w z : ι → ℂ) :
    Tendsto (fun c : ℂ => carlsonRPolynomialNumerator n (fun i => c * w i) z /
      (ascPochhammer ℂ n).eval c) (cobounded ℂ) (𝓝 ((∑ i, w i * z i) ^ n)) := by
  classical
  have hne : ∀ᶠ c : ℂ in cobounded ℂ, c ≠ 0 := by
    simpa using (tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop 0
  have hden := tendsto_ascPochhammer_mul_div_pow_cobounded 1 n
  simp only [mul_one, one_pow] at hden
  have hnum : Tendsto (fun c : ℂ => carlsonRPolynomialNumerator n (fun i => c * w i) z / c ^ n)
      (cobounded ℂ) (𝓝 ((∑ i, w i * z i) ^ n)) := by
    rw [sum_pow_eq_sum_piAntidiag]
    have hterm : ∀ m ∈ piAntidiag (univ : Finset ι) n, Tendsto (fun c : ℂ =>
        (Nat.multinomial univ m : ℂ) * (∏ i, z i ^ m i) *
          ∏ i, ((ascPochhammer ℂ (m i)).eval (c * w i) / c ^ m i)) (cobounded ℂ)
        (𝓝 ((Nat.multinomial univ m : ℂ) * ∏ i, (w i * z i) ^ m i)) := by
      intro m _
      have := tendsto_finsetProd (univ : Finset ι) fun i _ =>
        tendsto_ascPochhammer_mul_div_pow_cobounded (w i) (m i)
      convert (tendsto_const_nhds (x := (Nat.multinomial univ m : ℂ) * ∏ i, z i ^ m i)).mul
        this using 2
      rw [mul_assoc, ← prod_mul_distrib]
      congr 1; refine prod_congr rfl fun i _ => by ring
    refine (tendsto_finsetSum _ hterm).congr' ?_
    filter_upwards [hne] with c hc
    rw [carlsonRPolynomialNumerator_eq_multinomial_sum, sum_div]
    refine sum_congr rfl fun m hm => ?_
    have hs : ∑ i, m i = n := (mem_piAntidiag.mp hm).1
    rw [prod_div_distrib, prod_pow_eq_pow_sum, hs]
    ring
  have hq := hnum.div hden one_ne_zero
  rw [div_one] at hq
  refine hq.congr' ?_
  filter_upwards [hne] with c hc
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ (pow_ne_zero _ hc)]


/-- The limit of the Pochhammer weight of one multi-index as `c → 0`: it concentrates on the
multi-indices `n eⱼ`, with limit `wⱼ`. -/
private theorem tendsto_weight_nhds_zero [DecidableEq ι] (k : ℕ) (w : ι → ℂ) (m : ι → ℕ)
    (hm : ∑ i, m i = k + 1) :
    Tendsto (fun c : ℂ => (∏ i, (ascPochhammer ℂ (m i)).eval (c * w i)) /
        (ascPochhammer ℂ (k + 1)).eval c) (𝓝[≠] 0)
      (𝓝 (∑ j, if m = Pi.single j (k + 1) then w j else 0)) := by
  have hden := tendsto_ascPochhammer_mul_div_nhds_zero 1 k
  simp only [mul_one, one_mul] at hden
  have hk : ((k.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  by_cases hsingle : ∃ j, m = Pi.single j (k + 1)
  · obtain ⟨j, rfl⟩ := hsingle
    have hL : (∑ j', if Pi.single j (k + 1) = (Pi.single j' (k + 1) : ι → ℕ) then w j' else 0)
        = w j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hj'
        rw [ite_eq_right_iff.mpr (fun h' => absurd h' ?_)]
        intro h
        have := congrFun h j
        simp [hj'.symm] at this
      · simp
    rw [hL]
    have hprod : ∀ c : ℂ, (∏ i, (ascPochhammer ℂ ((Pi.single j (k + 1) : ι → ℕ) i)).eval (c * w i))
        = (ascPochhammer ℂ (k + 1)).eval (c * w j) := by
      intro c
      rw [Finset.prod_eq_single j]
      · simp
      · intro i _ hi; simp [hi]
      · simp
    have hnum := tendsto_ascPochhammer_mul_div_nhds_zero (w j) k
    have := hnum.div hden hk
    rw [mul_div_cancel_right₀ _ hk] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hc0 : c ≠ 0 := hc
    simp only [Pi.div_apply, hprod]
    rw [div_div_div_cancel_right₀ hc0]
  · push Not at hsingle
    have hL : (∑ j, if m = Pi.single j (k + 1) then w j else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [ite_eq_right_iff.mpr (fun h => absurd h (hsingle j))]
    rw [hL]
    -- two distinct occupied indices
    obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
      by_contra h; push Not at h; simp [h] at hm
    obtain ⟨i, hij, hi⟩ : ∃ i, i ≠ j ∧ m i ≠ 0 := by
      by_contra h; push Not at h
      apply hsingle j
      have hmj : m j = k + 1 := by
        rw [← hm, Finset.sum_eq_single j (fun i _ hi => h i hi) (by simp)]
      funext l
      by_cases hl : l = j
      · subst hl; simp [hmj]
      · simp [hl, h l hl]
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hi
    obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hj
    set R := (Finset.univ.erase i).erase j
    have hsplit : ∀ c : ℂ, (∏ l, (ascPochhammer ℂ (m l)).eval (c * w l)) =
        (ascPochhammer ℂ (m i)).eval (c * w i) * ((ascPochhammer ℂ (m j)).eval (c * w j) *
          ∏ l ∈ R, (ascPochhammer ℂ (m l)).eval (c * w l)) := by
      intro c
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    have hA := tendsto_ascPochhammer_mul_div_nhds_zero (w i) a
    have hB := tendsto_ascPochhammer_mul_div_nhds_zero (w j) b
    have hC : Tendsto (fun c : ℂ => c * ∏ l ∈ R, (ascPochhammer ℂ (m l)).eval (c * w l))
        (𝓝[≠] 0) (𝓝 (0 * ∏ l ∈ R, (ascPochhammer ℂ (m l)).eval (0 * w l))) := by
      refine (Continuous.tendsto ?_ 0).mono_left nhdsWithin_le_nhds
      exact continuous_id.mul (continuous_finsetProd _ fun l _ =>
        (Polynomial.continuous _).comp (by fun_prop))
    have := ((hA.mul hB).mul hC).div hden hk
    rw [zero_mul, mul_zero, zero_div] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hc0 : c ≠ 0 := hc
    simp only [Pi.div_apply]
    rw [hsplit, ha, hb]
    field_simp

/-- **Theorem 6.2-5**, the limit `c → 0` (6.2-17): with `∑ wᵢ = 1`,
`Rₙ(c w, z) → ∑ wᵢ zᵢⁿ`, where `Rₙ(c w, z) = Nₙ(c w, z) / (c)ₙ`. -/
theorem tendsto_carlsonRPolynomial_concentration_zero (n : ℕ) (w z : ι → ℂ)
    (hw : ∑ i, w i = 1) :
    Tendsto (fun c : ℂ => carlsonRPolynomialNumerator n (fun i => c * w i) z /
      (ascPochhammer ℂ n).eval c) (𝓝[≠] 0) (𝓝 (∑ i, w i * z i ^ n)) := by
  classical
  rcases n with _ | k
  · simp only [carlsonRPolynomialNumerator_zero, ascPochhammer_zero, eval_one, div_one,
      pow_zero, mul_one, hw]
    exact tendsto_const_nhds
  have hterm : ∀ m ∈ piAntidiag (univ : Finset ι) (k + 1), Tendsto (fun c : ℂ =>
      (Nat.multinomial univ m : ℂ) * (∏ i, z i ^ m i) *
        ((∏ i, (ascPochhammer ℂ (m i)).eval (c * w i)) / (ascPochhammer ℂ (k + 1)).eval c))
      (𝓝[≠] 0) (𝓝 ((Nat.multinomial univ m : ℂ) * (∏ i, z i ^ m i) *
        ∑ j, if m = Pi.single j (k + 1) then w j else 0)) := fun m hm =>
    tendsto_const_nhds.mul (tendsto_weight_nhds_zero k w m (mem_piAntidiag.mp hm).1)
  have hsum := tendsto_finsetSum _ hterm
  have hval : (∑ m ∈ piAntidiag (univ : Finset ι) (k + 1), (Nat.multinomial univ m : ℂ) *
      (∏ i, z i ^ m i) * ∑ j, if m = Pi.single j (k + 1) then w j else 0) =
      ∑ i, w i * z i ^ (k + 1) := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq' (piAntidiag univ (k + 1)) (Pi.single j (k + 1))]
    rw [ite_eq_left_iff.mpr (fun h => absurd (by simp [mem_piAntidiag]) h)]
    rw [Nat.multinomial_single, Nat.cast_one, one_mul,
      Finset.prod_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
    simp [mul_comm]
  rw [hval] at hsum
  refine hsum.congr' (Eventually.of_forall fun c => ?_)
  show _ = carlsonRPolynomialNumerator (k + 1) (fun i => c * w i) z / _
  rw [carlsonRPolynomialNumerator_eq_multinomial_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

end Carlson
