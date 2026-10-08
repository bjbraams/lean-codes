/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.R.Associated
public import Carlson.R.ZeroParameter
public import Carlson.R.SmallVariableContinuation
public import Carlson.R.SlitRelations
public import Carlson.Aggregation
public import Carlson.TwoVariable.ParameterSymmetry

/-!
# Elementary two-variable `R` functions (Carlson's Exercises 5.9-10 and 5.9-13)

* A zero parameter: `R_t(1, 0; x, y) = x^t` and `R_t(0, 1; x, y) = y^t` on the slit plane.
* Exercise 5.9-10, regularized:
  `R_t(u, v; x, y) = c(c + t + 1) R_t(u + 1, v + 1; x, y) - t(uy + vx) R_{t-1}(u + 1, v + 1; x, y)`,
  with `c = u + v`.
* Exercise 5.9-13: `t(x - y) R_{t-1}(1, 1; x, y) = x^t - y^t` and
  `(x - y) R_{-1}(1, 1; x, y) = log x - log y`. These are the base cases of Theorem 8.5-1.

## Main results

* `Carlson.TwoVariable.regCarlsonR_pair_one_zero`, `Carlson.TwoVariable.regCarlsonR_pair_zero_one`.
* `Carlson.TwoVariable.regCarlsonR_pair_raise_both`: Exercise 5.9-10.
* `Carlson.TwoVariable.regCarlsonR_pair_one_one`,
  `Carlson.TwoVariable.regCarlsonR_pair_one_one_log`:
  Exercise 5.9-13.
* `Carlson.TwoVariable.regCarlsonR_pair_neg_one_one_one`,
  `Carlson.TwoVariable.regCarlsonR_pair_neg_one_one_one_diag`: the logarithmic elementary function
  of Section 8.5 and its diagonal value, on the whole slit plane.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.9.
-/

open Complex Set Filter Dirichlet
open scoped Topology
@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- A zero parameter on the right half-plane: `R_t(1, 0; z) = z₀^t`. -/
private theorem regCarlsonR_pair_one_zero_right (t : ℂ) {z : Fin 2 → ℂ}
    (hz : z ∈ carlsonRVariableDomain) : regCarlsonR t (pair 1 0) z = z 0 ^ t := by
  set q : Option (Fin 1) → Fin 2 := fun o => Option.elim o 1 fun _ => 0
  have hq : Function.Surjective q := by
    intro k; fin_cases k
    · exact ⟨some 0, rfl⟩
    · exact ⟨none, rfl⟩
  set b' : Option (Fin 1) → ℂ := fun o => Option.elim o 0 fun _ => 1
  have hagg : stdSimplexAggregate q b' = pair 1 0 := by
    classical
    funext k
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    fin_cases k
    · have : (Finset.univ.filter fun o : Option (Fin 1) => q o = 0) = {some 0} := by decide
      show (Finset.univ.filter fun o => q o = 0).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
    · have : (Finset.univ.filter fun o : Option (Fin 1) => q o = 1) = {none} := by decide
      show (Finset.univ.filter fun o => q o = 1).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
  have hs : z ∈ carlsonRSlitDomain := carlsonRVariableDomain_subset_slitDomain hz
  have h := regCarlsonR_aggregate_of_slit hq t hs b'
  rw [hagg] at h
  rw [← h, regCarlsonR_option_zero t (b := b') (z := z ∘ q) rfl
    (carlsonRVariableDomain_subset_slitDomain fun o => hz (q o))]
  have hb : b' ∘ some = fun _ => 1 := rfl
  have hzq : (z ∘ q) ∘ some = fun _ => z 0 := rfl
  rw [hb, hzq, regCarlsonR_const_node t _ (carlsonRightHalfPlane_subset_slitPlane (hz 0))]
  simp

/-- **A zero parameter**: `R_t(1, 0; z) = z₀^t` on the slit plane. -/
theorem regCarlsonR_pair_one_zero (t : ℂ) {z : Fin 2 → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR t (pair 1 0) z = z 0 ^ t := by
  have hG : AnalyticOnNhd ℂ (fun w : Fin 2 → ℂ => w 0 ^ t) carlsonRSlitDomain := fun w hw =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt w).cpow
      analyticAt_const (hw 0)
  exact eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane (analyticOnNhd_regCarlsonR t _) hG
    (fun w hw => regCarlsonR_pair_one_zero_right t hw) hz

/-- **A zero parameter**: `R_t(0, 1; x, y) = y^t` on the slit plane. -/
theorem regCarlsonR_pair_zero_one (t : ℂ) {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    regCarlsonR t (pair 0 1) (pair x y) = y ^ t := by
  rw [← regCarlsonR_pair_swap t 0 1 hx hy]
  have hs : pair y x ∈ carlsonRSlitDomain := by intro i; fin_cases i <;> assumption
  simpa [pair] using regCarlsonR_pair_one_zero t hs

/-- **Carlson's Exercise 5.9-10**, regularized: with `c = u + v`,
`R_t(u, v; x, y) = c(c + t + 1) R_t(u + 1, v + 1; x, y)`
`- t(uy + vx) R_{t-1}(u + 1, v + 1; x, y)`. -/
theorem regCarlsonR_pair_raise_both (t u v : ℂ) {x y : ℂ} (hz : pair x y ∈ carlsonRSlitDomain) :
    regCarlsonR t (pair u v) (pair x y) =
      (u + v) * (u + v + t + 1) * regCarlsonR t (pair (u + 1) (v + 1)) (pair x y) -
        t * (u * y + v * x) * regCarlsonR (t - 1) (pair (u + 1) (v + 1)) (pair x y) := by
  have hsum := regCarlsonR_eq_sum_addDirichletUnit t (pair u v) hz
  have h0 : addDirichletUnit (pair u v) 0 = pair (u + 1) v := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  have h1 : addDirichletUnit (pair u v) 1 = pair u (v + 1) := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  have r0 := regCarlsonR_eq_addDirichletUnit t (pair (u + 1) v) hz 1
  have r1 := regCarlsonR_eq_addDirichletUnit t (pair u (v + 1)) hz 0
  have e0 : addDirichletUnit (pair (u + 1) v) 1 = pair (u + 1) (v + 1) := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  have e1 : addDirichletUnit (pair u (v + 1)) 0 = pair (u + 1) (v + 1) := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  rw [e0] at r0
  rw [e1] at r1
  simp only [Fin.sum_univ_two, pair_zero, pair_one, h0, h1] at hsum r0 r1
  rw [hsum, r0, r1]
  ring

/-- **Carlson's Exercise 5.9-13, first part**: `t (x - y) R_{t-1}(1, 1; x, y) = x^t - y^t` on the
slit plane. -/
theorem regCarlsonR_pair_one_one (t : ℂ) {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    t * (x - y) * regCarlsonR (t - 1) (pair 1 1) (pair x y) = x ^ t - y ^ t := by
  have hz : pair x y ∈ carlsonRSlitDomain := by intro i; fin_cases i <;> assumption
  have h := regCarlsonR_tangent t (pair 0 0) hz 0 1
  have e1 : addDirichletUnit (addDirichletUnit (pair (0 : ℂ) 0) 1) 0 = pair 1 1 := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  have e2 : addDirichletUnit (pair (0 : ℂ) 0) 0 = pair 1 0 := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  have e3 : addDirichletUnit (pair (0 : ℂ) 0) 1 = pair 0 1 := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  rw [e1, e2, e3, regCarlsonR_pair_one_zero t hz, regCarlsonR_pair_zero_one t hx hy] at h
  simp only [pair_zero, pair_one] at h
  linear_combination h

/-- **Carlson's Exercise 5.9-13, second part**: `(x - y) R_{-1}(1, 1; x, y) = log x - log y` on the
slit plane. -/
theorem regCarlsonR_pair_one_one_log {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    (x - y) * regCarlsonR (-1) (pair 1 1) (pair x y) = log x - log y := by
  have hz : pair x y ∈ carlsonRSlitDomain := by intro i; fin_cases i <;> assumption
  set F : ℂ → ℂ := fun t => (x - y) * regCarlsonR (t - 1) (pair 1 1) (pair x y)
  have hF : ContinuousAt F 0 := by
    have h := analyticAt_regCarlsonR_comp (t := fun s : ℂ => s - 1)
      (b := fun _ => pair (1 : ℂ) 1) (z := fun _ => pair x y) (p := (0 : ℂ))
      (analyticAt_id.sub analyticAt_const) analyticAt_const analyticAt_const hz
    exact (continuousAt_const.mul h.continuousAt)
  have hslope : ∀ w : ℂ, w ≠ 0 → Tendsto (fun t : ℂ => t⁻¹ * (w ^ t - 1)) (𝓝[≠] 0)
      (𝓝 (log w)) := by
    intro w hw
    have hd : HasDerivAt (fun t : ℂ => w ^ t) (w ^ (0 : ℂ) * log w * 1) 0 :=
      (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl hw)
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    simpa using hd
  have hlim : Tendsto F (𝓝[≠] 0) (𝓝 (log x - log y)) := by
    have := (hslope x (slitPlane_ne_zero hx)).sub (hslope y (slitPlane_ne_zero hy))
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    have h := regCarlsonR_pair_one_one t hx hy
    simp only [F]
    field_simp
    linear_combination -h
  have := tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds) hlim
  simpa [F] using this

/-- Carlson's logarithmic elementary function of Section 8.5, for distinct slit-plane nodes. -/
theorem regCarlsonR_pair_neg_one_one_one {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hxy : x ≠ y) :
    regCarlsonR (-1) (pair 1 1) (pair x y) = (log y - log x) / (y - x) := by
  rw [eq_div_iff (sub_ne_zero.mpr hxy.symm)]
  linear_combination -regCarlsonR_pair_one_one_log hx hy

/-- The diagonal value of Carlson's logarithmic elementary function:
`R₋₁(1, 1; x, x) = x⁻¹` for slit-plane `x`. -/
theorem regCarlsonR_pair_neg_one_one_one_diag {x : ℂ} (hx : x ∈ slitPlane) :
    regCarlsonR (-1) (pair 1 1) (pair x x) = x⁻¹ := by
  have hxx : pair x x = fun _ : Fin 2 => x := by funext i; fin_cases i <;> rfl
  have h2 : Gamma (1 + 1 : ℂ) = 1 := by simpa using Complex.Gamma_nat_eq_factorial 1
  rw [hxx, regCarlsonR_const_node _ _ hx, sum_pair, cpow_neg_one, h2, inv_one, mul_one]

end Carlson.TwoVariable
