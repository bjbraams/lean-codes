/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Explicit
public import Carlson.R.Relations
public import Carlson.R.SlitPlane
public import ComplexAnalysis.RealUniqueness

/-!
# Homogeneity of the R-function on the slit node domain

Carlson's homogeneity relation (5.9-3), `R_t(b; μ z) = μ^t R_t(b; z)`, is proved for the
regularized R-function at all complex exponents and parameters and all slit-plane nodes, under
the branch condition that `μ` lies in the slit plane and `arg μ + arg zᵢ ∈ (-π, π)` for every
node. For positive real `μ` no condition is needed.

The positive real case follows from the native integral by permanence, first in the nodes and
then in the parameters. For complex `μ`, the admissible scalings form an open sector, the image
of a product of intervals in polar coordinates; the identity theorem on this sector extends the
positive real case.

## Main results

* `Carlson.regCarlsonR_smul_of_pos`: homogeneity under positive real scaling.
* `Carlson.regCarlsonR_mul_of_arg_add`: homogeneity under complex scaling with the principal
  branch condition.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.9.
-/

open Dirichlet
open Complex Set Filter
open scoped Topology
@[expose] public noncomputable section

namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- Positive real homogeneity of the regularized R-function on the full slit node domain:
`R_t(b; a z) = a^t R_t(b; z)` for `a > 0`, all complex `t, b`. -/
theorem regCarlsonR_smul_of_pos (t : ℂ) (b : ι → ℂ) {a : ℝ} (ha : 0 < a) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR t b (fun i => (a : ℂ) * z i) = (a : ℂ) ^ t * regCarlsonR t b z := by
  have hslit : ∀ {w : ι → ℂ}, w ∈ carlsonRSlitDomain →
      (fun i => (a : ℂ) * w i) ∈ carlsonRSlitDomain := fun {w} hw i => by
    have h := hw i
    rw [mem_slitPlane_iff_arg] at h ⊢
    refine ⟨?_, mul_ne_zero (by exact_mod_cast ha.ne') h.2⟩
    rw [arg_real_mul _ ha]; exact h.1
  have hsmul : AnalyticOnNhd ℂ (fun w : ι → ℂ => fun i => (a : ℂ) * w i) univ := fun w _ =>
    analyticAt_pi_iff.mpr fun i => analyticAt_const.mul ((analyticAt_pi_iff.mp analyticAt_id) i)
  -- first for convergent parameters, by permanence in the nodes
  have hconv : ∀ B ∈ (mvBetaConvergent : Set (ι → ℂ)),
      regCarlsonR t B (fun i => (a : ℂ) * z i) = (a : ℂ) ^ t * regCarlsonR t B z := by
    intro B hB
    refine eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
      (F := fun w => regCarlsonR t B (fun i => (a : ℂ) * w i))
      (G := fun w => (a : ℂ) ^ t * regCarlsonR t B w) ?_ ?_ ?_ hz
    · intro w hw
      exact analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const (hsmul w trivial)
        (hslit hw)
    · intro w hw
      exact analyticAt_const.mul (analyticOnNhd_regCarlsonR t B w hw)
    · intro w hw
      have hw' : (fun i => (a : ℂ) * w i) ∈ carlsonRVariableDomain := fun i => by
        have := hw i
        simp only [carlsonRightHalfPlane, mem_ofPred_eq, re_ofReal_mul] at this ⊢
        positivity
      change regCarlsonR t B (fun i => (a : ℂ) * w i) = (a : ℂ) ^ t * regCarlsonR t B w
      rw [regCarlsonR_eq_regCarlsonRIntegral t hB hw', regCarlsonR_eq_regCarlsonRIntegral t hB hw,
        regCarlsonRIntegral_smul_of_re_pos t (by simpa using ha) hw]
  -- then for all parameters, by permanence in the parameters
  have h := analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (G := fun B => regCarlsonR t B (fun i => (a : ℂ) * z i))
    (H := fun B => (a : ℂ) ^ t * regCarlsonR t B z)
    (fun B _ => analyticAt_regCarlsonR_comp analyticAt_const analyticAt_id analyticAt_const
      (hslit hz))
    (fun B _ => analyticAt_const.mul (analyticAt_regCarlsonR_comp analyticAt_const analyticAt_id
      analyticAt_const hz)) hconv
  exact congrFun h b

/-- The set of scalings compatible with the principal arguments of the nodes. -/
def argSector (z : ι → ℂ) : Set ℂ :=
  {μ | μ ∈ slitPlane ∧ ∀ i, arg μ + arg (z i) ∈ Ioo (-Real.pi) Real.pi}

/-- A compatible scaling keeps every node on the principal branch. -/
private theorem mul_mem_slitPlane_of_arg_add {μ w : ℂ} (hμ : μ ∈ slitPlane)
    (hw : w ∈ slitPlane) (h : arg μ + arg w ∈ Ioo (-Real.pi) Real.pi) : μ * w ∈ slitPlane := by
  rw [mem_slitPlane_iff_arg] at hμ hw ⊢
  rw [arg_mul hμ.2 hw.2 ⟨h.1, h.2.le⟩]
  exact ⟨h.2.ne, mul_ne_zero hμ.2 hw.2⟩

/-- The argument sector is open. -/
private theorem isOpen_argSector (z : ι → ℂ) : IsOpen (argSector z) := by
  have hc : ContinuousOn arg slitPlane := fun x hx => (continuousAt_arg hx).continuousWithinAt
  have : argSector z = slitPlane ∩ arg ⁻¹' {θ | ∀ i, θ + arg (z i) ∈ Ioo (-Real.pi) Real.pi} := by
    ext μ; simp [argSector]
  rw [this]
  refine hc.isOpen_inter_preimage isOpen_slitPlane ?_
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Ioo.preimage (continuous_id.add continuous_const)

omit [Fintype ι] in
/-- The argument sector is preconnected: it is the image of a product of intervals under
polar coordinates. -/
private theorem isPreconnected_argSector (z : ι → ℂ) :
    IsPreconnected (argSector z) := by
  set T : Set ℝ := Ioo (-Real.pi) Real.pi ∩
    {θ | ∀ i, θ + arg (z i) ∈ Ioo (-Real.pi) Real.pi}
  have hT : IsPreconnected T := by
    refine (Set.OrdConnected.isPreconnected ?_)
    refine Set.OrdConnected.inter Set.ordConnected_Ioo ?_
    rw [ofPred_forall]
    refine Set.ordConnected_iInter fun i => ⟨fun x hx y hy θ hθ => ?_⟩
    exact ⟨by linarith [hx.1, hθ.1], by linarith [hy.2, hθ.2]⟩
  have himage : argSector z =
      (fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I)) '' (Ioi 0 ×ˢ T) := by
    ext μ
    constructor
    · rintro ⟨hμ, hargs⟩
      have hμ' := mem_slitPlane_iff_arg.mp hμ
      refine ⟨(‖μ‖, arg μ), ⟨norm_pos_iff.mpr hμ'.2, ⟨neg_pi_lt_arg μ,
        lt_of_le_of_ne (arg_le_pi μ) hμ'.1⟩, hargs⟩, ?_⟩
      exact norm_mul_exp_arg_mul_I μ
    · rintro ⟨⟨r, θ⟩, ⟨hr, hθ, hθs⟩, rfl⟩
      have hr' : (0 : ℝ) < r := hr
      have harg : arg ((r : ℂ) * exp (θ * I)) = θ := by
        rw [arg_real_mul _ hr', exp_mul_I, arg_cos_add_sin_mul_I ⟨hθ.1, hθ.2.le⟩]
      refine ⟨?_, fun i => by rw [harg]; exact hθs i⟩
      rw [mem_slitPlane_iff_arg, harg]
      exact ⟨hθ.2.ne, mul_ne_zero (by exact_mod_cast hr'.ne') (exp_ne_zero _)⟩
  rw [himage]
  exact (isPreconnected_Ioi.prod hT).image _ (by fun_prop)

/-- **Complex homogeneity** of the regularized R-function on the slit node domain:
`R_t(b; μ z) = μ^t R_t(b; z)` whenever `μ` and all `z i` lie on the principal branch and
`arg μ + arg (z i) ∈ (-π, π)` for every `i`. This is Carlson's homogeneity (5.9-3) with its
branch condition made explicit. -/
theorem regCarlsonR_mul_of_arg_add (t : ℂ) (b : ι → ℂ) {μ : ℂ} {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) (hμ : μ ∈ slitPlane)
    (harg : ∀ i, arg μ + arg (z i) ∈ Ioo (-Real.pi) Real.pi) :
    regCarlsonR t b (fun i => μ * z i) = μ ^ t * regCarlsonR t b z := by
  have hsub : ∀ ν ∈ argSector z, (fun i => ν * z i) ∈ carlsonRSlitDomain :=
    fun ν hν i => mul_mem_slitPlane_of_arg_add hν.1 (hz i) (hν.2 i)
  have hF : AnalyticOnNhd ℂ (fun ν => regCarlsonR t b (fun i => ν * z i)) (argSector z) :=
    fun ν hν => analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pi_iff.mpr fun i => analyticAt_id.mul analyticAt_const) (hsub ν hν)
  have hG : AnalyticOnNhd ℂ (fun ν => ν ^ t * regCarlsonR t b z) (argSector z) :=
    fun ν hν => (analyticAt_id.cpow analyticAt_const hν.1).mul analyticAt_const
  have hone : ((1 : ℝ) : ℂ) ∈ argSector z := by
    refine ⟨by simp, fun i => ?_⟩
    have := mem_slitPlane_iff_arg.mp (hz i)
    simp only [ofReal_one, arg_one, zero_add]
    exact ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) this.1⟩
  refine hF.eqOn_of_eventuallyEq_ofReal hG (isPreconnected_argSector z) hone ?_ ⟨hμ, harg⟩
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
  exact regCarlsonR_smul_of_pos t b hx hz

end Carlson
