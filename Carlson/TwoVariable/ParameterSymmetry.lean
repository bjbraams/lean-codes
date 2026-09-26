/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.HalfPlane
public import Carlson.TwoVariable.RPolynomial
public import Carlson.R.Explicit

/-!
# Interchanging an exponent and a Dirichlet parameter

The two numerator parameters in the Gauss series are symmetric. We establish
this symmetry first near the all-one node vector, then continue in the parameters
and in the slit-plane node. This is the R-identity underlying Carlson (1987), (2.12).

## Main results

* `Carlson.TwoVariable.carlsonRPolynomialNumerator₂_zero_left`: Only one monomial survives when
  the first polynomial node vanishes.
* `Carlson.TwoVariable.regCarlsonR_normalize_first`: Normalize the first node, with branch
  control for arbitrary right-half-plane nodes. The normalized second node need only belong to
  the slit plane.
* `Carlson.TwoVariable.regCarlsonR_parameterInterchange`: Exponent-parameter interchange at two
  right-half-plane nodes, with no parameter restrictions and a slit-plane ratio on the
  transformed side.
* `Carlson.TwoVariable.regCarlsonR_pair_swap`: Simultaneously swapping the two parameters and
  nodes on the slit domain.
* `Carlson.TwoVariable.regCarlsonR_parameterInterchange_last`: The second form of the
  exponent-parameter interchange, normalized at the last node.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- Only one monomial survives when the first polynomial node vanishes. -/
theorem carlsonRPolynomialNumerator₂_zero_left (n : ℕ) (u v y : ℂ) :
    carlsonRPolynomialNumerator₂ n u v 0 y = (ascPochhammer ℂ n).eval v * y ^ n := by
  unfold carlsonRPolynomialNumerator₂
  rw [Finset.sum_eq_single (0, n)]
  · simp
  · intro ij hij hne
    have hi : ij.1 ≠ 0 := by
      intro h
      apply hne
      have hs := Finset.mem_antidiagonal.mp hij
      ext <;> simp_all
    simp [zero_pow hi]
  · simp

/-- For convergent parameter vectors, the native two-node R-integral near unit nodes is invariant
under interchange of the two numerator parameters of its Gauss series. -/
private theorem parameterSymmetry_native_near_one (a u v y : ℂ)
    (hb : pair u v ∈ mvBetaConvergent)
    (hB : pair (u + v - a) a ∈ mvBetaConvergent) (hy : ‖y‖ < 1) :
    regCarlsonRIntegral (-a) (pair u v) (pair 1 (1 - y)) =
      regCarlsonRIntegral (-v) (pair (u + v - a) a) (pair 1 (1 - y)) := by
  have hnode : ∀ i, ‖pair 0 y i‖ < 1 := by
    intro i; fin_cases i
    · simp [pair]
    · exact hy
  have h₁ := hasSum_regCarlsonRIntegral_near_one a (pair u v) (pair 0 y) hb hnode
  have h₂ := hasSum_regCarlsonRIntegral_near_one v (pair (u + v - a) a) (pair 0 y) hB hnode
  have heq : (fun n : ℕ => (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) *
      regCarlsonRPolynomial n (pair u v) (pair 0 y)) =
      (fun n => (ascPochhammer ℂ n).eval v / (n.factorial : ℂ) *
      regCarlsonRPolynomial n (pair (u + v - a) a) (pair 0 y)) := by
    funext n
    change _ * regRPolynomial n u v 0 y = _ * regRPolynomial n (u + v - a) a 0 y
    rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma,
      regRPolynomial_eq_numerator₂_mul_one_div_Gamma,
      carlsonRPolynomialNumerator₂_zero_left, carlsonRPolynomialNumerator₂_zero_left]
    rw [sub_add_cancel]
    ring
  rw [heq] at h₁
  have hn : (fun i => 1 - pair 0 y i) = pair 1 (1 - y) := by
    ext i; fin_cases i <;> simp [pair]
  simpa only [hn] using h₁.unique h₂

/-- The numerator-parameter symmetry near unit nodes extends to all parameters of the regularized
R-function. -/
private theorem parameterSymmetry_near_one (a u v y : ℂ) (hy : ‖y‖ < 1) :
    regCarlsonR (-a) (pair u v) (pair 1 (1 - y)) =
      regCarlsonR (-v) (pair (u + v - a) a) (pair 1 (1 - y)) := by
  have hz : pair 1 (1 - y) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · change 0 < (1 : ℂ).re
      norm_num
    · change 0 < (1 - y).re
      have := re_le_norm y
      simp only [sub_re, one_re]
      linarith
  have hs := carlsonRVariableDomain_subset_slitDomain hz
  let B : (Fin 3 → ℂ) → Fin 2 → ℂ := fun p => pair (p 1 + p 2 - p 0) (p 0)
  have hB (p : Fin 3 → ℂ) : AnalyticAt ℂ B p := by
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact ((analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p))
        1).add (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p))
            2)).sub (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 0)
    · exact (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 0)
  have hb (p : Fin 3 → ℂ) : AnalyticAt ℂ (fun q => pair (q 1) (q 2)) p := by
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 1)
    · exact (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ) (z := p)) 2)
  have hleft : AnalyticOnNhd ℂ (fun p : Fin 3 → ℂ =>
      regCarlsonR (-(p 0)) (pair (p 1) (p 2)) (pair 1 (1 - y))) univ :=
    fun p _ => analyticAt_regCarlsonR_comp (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ)
        (z := p)) 0).neg
      (hb p) analyticAt_const hs
  have hright : AnalyticOnNhd ℂ (fun p : Fin 3 → ℂ =>
      regCarlsonR (-(p 2)) (B p) (pair 1 (1 - y))) univ :=
    fun p _ => analyticAt_regCarlsonR_comp (analyticAt_pi_iff.mp (analyticAt_id (𝕜 := ℂ)
        (z := p)) 2).neg
      (hB p) analyticAt_const hs
  have heq := hleft.eq_of_eventuallyEq hright (z₀ := fun _ => 1) (by
    have hl := (hb (fun _ => 1)).continuousAt.tendsto.eventually
      (isOpen_mvBetaConvergent.mem_nhds (by intro i; fin_cases i <;> norm_num [pair]))
    have hr := (hB (fun _ => 1)).continuousAt.tendsto.eventually
      (isOpen_mvBetaConvergent.mem_nhds (by intro i; fin_cases i <;> norm_num [B, pair]))
    filter_upwards [hl, hr] with p hp hP
    rw [regCarlsonR_eq_regCarlsonRIntegral _ hp hz, regCarlsonR_eq_regCarlsonRIntegral _ hP hz]
    exact parameterSymmetry_native_near_one (p 0) (p 1) (p 2) y hp hP hy)
  exact congrFun heq ![a, u, v]

/-- Gauss numerator-parameter symmetry on the entire slit plane, with all
complex parameters allowed by reciprocal-Gamma regularization. -/
theorem regCarlsonR_parameterSymmetry (a u v : ℂ) {w : ℂ} (hw : w ∈ slitPlane) :
    regCarlsonR (-a) (pair u v) (pair 1 w) =
      regCarlsonR (-v) (pair (u + v - a) a) (pair 1 w) := by
  have hn {w : ℂ} (hw : w ∈ slitPlane) : pair 1 w ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · simp [pair]
    · exact hw
  have hnode (w : ℂ) : AnalyticAt ℂ (fun w => pair 1 w) w := by
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact analyticAt_const
    · exact analyticAt_id
  have ha (t : ℂ) (b : Fin 2 → ℂ) :
      AnalyticOnNhd ℂ (fun w => regCarlsonR t b (pair 1 w)) slitPlane :=
    fun w hw => analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const (hnode w) (hn hw)
  apply (ha (-a) (pair u v)).eqOn_of_preconnected_of_eventuallyEq
    (ha (-v) (pair (u + v - a) a))
    (starConvex_one_slitPlane.isPathConnected (by simp)).isConnected.isPreconnected
    (show (1 : ℂ) ∈ slitPlane by simp) ?_ hw
  have hnear : ∀ᶠ w : ℂ in 𝓝 1, ‖1 - w‖ < 1 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  filter_upwards [hnear] with w hw
  simpa using parameterSymmetry_near_one a u v (1 - w) hw

/-- Normalize the first node, with branch control for arbitrary right-half-plane nodes.
The normalized second node need only belong to the slit plane. -/
theorem regCarlsonR_normalize_first (t : ℂ) (b : Fin 2 → ℂ) {x y : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonR t b (pair x y) = x ^ t * regCarlsonR t b (pair 1 (y / x)) := by
  let q : (Fin 2 → ℂ) → Fin 2 → ℂ := fun z => pair 1 (z 1 / z 0)
  have hq {z : Fin 2 → ℂ} (hz : z ∈ carlsonRVariableDomain) : AnalyticAt ℂ q z := by
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact analyticAt_const
    · exact ((analyticAt_pi_iff.mp analyticAt_id) 1).div
        ((analyticAt_pi_iff.mp analyticAt_id) 0) (ne_zero_of_re_pos (hz 0))
  have hqs {z : Fin 2 → ℂ} (hz : z ∈ carlsonRVariableDomain) : q z ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · simp [q, pair]
    · exact div_mem_slitPlane_of_re_pos (hz 1) (hz 0)
  have hnative {z : Fin 2 → ℂ} (hz : z ∈ carlsonRVariableDomain)
      (hQ : q z ∈ carlsonRVariableDomain) :
      regCarlsonR t b z = z 0 ^ t * regCarlsonR t b (q z) := by
    apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
      (fun _ _ => analyticAt_regCarlsonR_comp analyticAt_const analyticAt_id
        analyticAt_const (carlsonRVariableDomain_subset_slitDomain hz))
      (fun _ _ => analyticAt_const.mul (analyticAt_regCarlsonR_comp analyticAt_const
        analyticAt_id analyticAt_const (hqs hz))) ?_) b
    intro B hB
    change regCarlsonR t B z = z 0 ^ t * regCarlsonR t B (q z)
    rw [regCarlsonR_eq_regCarlsonRIntegral _ hB hz, regCarlsonR_eq_regCarlsonRIntegral _ hB hQ]
    have h := regCarlsonRIntegral_smul_of_re_pos (b := B) t (hz 0) hQ
    have heq : (fun i => z 0 * q z i) = z := by
      ext i; fin_cases i
      · simp [q]
      · dsimp [q]
        field_simp [ne_zero_of_re_pos (hz 0)]
    rwa [heq] at h
  have hleft : AnalyticOnNhd ℂ (regCarlsonR t b) carlsonRVariableDomain :=
    (analyticOnNhd_regCarlsonR t b).mono carlsonRVariableDomain_subset_slitDomain
  have hright : AnalyticOnNhd ℂ (fun z => z 0 ^ t * regCarlsonR t b (q z))
      carlsonRVariableDomain := by
    intro z hz
    have hcoord : AnalyticAt ℂ (fun w : Fin 2 → ℂ => w 0) z :=
      (analyticAt_pi_iff.mp analyticAt_id) 0
    exact (hcoord.cpow analyticAt_const
      (carlsonRightHalfPlane_subset_slitPlane (hz 0))).mul
        (analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const (hq hz) (hqs hz))
  have hc : Convex ℝ (carlsonRVariableDomain : Set (Fin 2 → ℂ)) := by
    intro z hz w hw a c ha hc hac i
    exact convex_carlsonRightHalfPlane (hz i) (hw i) ha hc hac
  have hone : (fun _ : Fin 2 => (1 : ℂ)) ∈ carlsonRVariableDomain :=
    fun _ => by norm_num [carlsonRightHalfPlane]
  have hevent : (regCarlsonR t b) =ᶠ[𝓝 (fun _ : Fin 2 => 1)]
      (fun z => z 0 ^ t * regCarlsonR t b (q z)) := by
    have hQ := (hq hone).continuousAt.tendsto.eventually
      (isOpen_carlsonRVariableDomain.mem_nhds (by
        intro i; fin_cases i <;> norm_num [q, carlsonRightHalfPlane]))
    filter_upwards [isOpen_carlsonRVariableDomain.mem_nhds hone, hQ] with z hz hQ
    exact hnative hz hQ
  apply hleft.eqOn_of_preconnected_of_eventuallyEq hright hc.isPreconnected hone hevent
  intro i; fin_cases i
  · exact hx
  · exact hy

/-- Exponent-parameter interchange at two right-half-plane nodes, with no parameter
restrictions and a slit-plane ratio on the transformed side. -/
theorem regCarlsonR_parameterInterchange (t u v : ℂ) {x y : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonR t (pair u v) (pair x y) =
      x ^ t * regCarlsonR (-v) (pair (u + v + t) (-t)) (pair 1 (y / x)) := by
  rw [regCarlsonR_normalize_first t _ hx hy]
  have h := regCarlsonR_parameterSymmetry (-t) u v (div_mem_slitPlane_of_re_pos hy hx)
  simpa using congrArg (fun w => x ^ t * w) h

/-- Simultaneously swapping the two parameters and nodes on the slit domain. -/
theorem regCarlsonR_pair_swap (t u v : ℂ) {x y : ℂ}
    (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    regCarlsonR t (pair v u) (pair y x) = regCarlsonR t (pair u v) (pair x y) := by
  have hperm (b : Fin 2 → ℂ) : AnalyticAt ℂ (fun B => B ∘ swap) b :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp analyticAt_id) (swap i)
  have hright {z : Fin 2 → ℂ} (hz : z ∈ carlsonRVariableDomain) (b : Fin 2 → ℂ) :
      regCarlsonR t (b ∘ swap) (z ∘ swap) = regCarlsonR t b z := by
    apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
      (fun B _ => analyticAt_regCarlsonR_comp analyticAt_const (hperm B) analyticAt_const
        (carlsonRVariableDomain_subset_slitDomain (fun i => hz (swap i))))
      (fun _ _ => analyticAt_regCarlsonR_comp analyticAt_const analyticAt_id analyticAt_const
        (carlsonRVariableDomain_subset_slitDomain hz)) ?_) b
    intro B hB
    change regCarlsonR t (B ∘ swap) (z ∘ swap) = regCarlsonR t B z
    dsimp only [Function.comp_def]
    rw [regCarlsonR_eq_regCarlsonRIntegral _ (fun i => hB (swap i)) (fun i => hz (swap i)),
      regCarlsonR_eq_regCarlsonRIntegral _ hB hz]
    exact regCarlsonDirichletAverage_perm B z (fun w => w ^ t) swap
  have hleft : AnalyticOnNhd ℂ (fun z : Fin 2 → ℂ =>
      regCarlsonR t ((pair u v) ∘ swap) (z ∘ swap)) carlsonRSlitDomain :=
    fun z hz => analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const (hperm z)
      (fun i => hz (swap i))
  have hz : pair x y ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hx
    · exact hy
  have h := eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft
    (analyticOnNhd_regCarlsonR t (pair u v)) (fun z hz => hright hz (pair u v)) hz
  simpa only [pair_comp_swap] using h

/-- The second form of the exponent-parameter interchange, normalized at the last node. -/
theorem regCarlsonR_parameterInterchange_last (t u v : ℂ) {x y : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonR t (pair u v) (pair x y) =
      y ^ t * regCarlsonR (-u) (pair (-t) (u + v + t)) (pair (x / y) 1) := by
  rw [← regCarlsonR_pair_swap t u v
    (carlsonRightHalfPlane_subset_slitPlane hx) (carlsonRightHalfPlane_subset_slitPlane hy),
    regCarlsonR_parameterInterchange t v u hy hx]
  rw [← regCarlsonR_pair_swap (-u) (v + u + t) (-t)
    (show (1 : ℂ) ∈ slitPlane by simp) (div_mem_slitPlane_of_re_pos hx hy), add_comm v u]

end Carlson.TwoVariable
