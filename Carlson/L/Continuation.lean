/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.L.Basic
public import Carlson.R.Explicit

/-!
# Carlson's L-function

The regularized L-function `L_t(b, z) / Γ(∑ b)` is the exponent derivative of the regularized
R-function `regCarlsonR`. Since `regCarlsonR` is defined for all complex exponents and
parameters and is analytic on the product slit plane in the nodes, so is `regCarlsonL`, and it
inherits joint holomorphy in all arguments (Carlson (1987), (2.1)). On the convergence domain
of the native integral, for right-half-plane nodes, `regCarlsonL` is the power-logarithm
Dirichlet average `regCarlsonLIntegral`, and it is the unique entire continuation of that
integral in the parameters.

## Main definitions

* `Carlson.regCarlsonL t b z`: the regularized L-function `deriv (fun s => regCarlsonR s b z) t`.
* `Carlson.carlsonL t b z`: Carlson's function `L_t(b, z) = Γ(∑ b) regCarlsonL t b z`.

## Main results

* `Carlson.hasDerivAt_regCarlsonR_L`: the derivative characterization on the slit domain.
* `Carlson.analyticOnNhd_regCarlsonL_joint`, `Carlson.analyticAt_regCarlsonL_comp`: joint
  holomorphy in exponent, parameters and slit-plane nodes.
* `Carlson.regCarlsonL_eq_regCarlsonLIntegral`: agreement with the native integral.
* `Carlson.isRegCarlsonLContinuation_regCarlsonL`: the L-function is the unique entire
  continuation of the native integral in the parameters.

## References

* B. C. Carlson, *A table of elliptic integrals of the third kind*, Math. Comp. 51 (1987);
  cited as Carlson (1987).
-/

open Dirichlet
open Complex Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The regularized L-function, defined by differentiating the regularized R-function in its
exponent. Values at nodes outside the product slit plane are unspecified. -/
def regCarlsonL (t : ℂ) (b z : ι → ℂ) : ℂ :=
  deriv (fun s => regCarlsonR s b z) t

/-- Carlson's L-function `L_t(b, z)`. At poles of `Γ(∑ i, b i)` this is only Lean's totalized
expression; the entire object is `regCarlsonL`. -/
def carlsonL (t : ℂ) (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonL t b z

/-- On the slit domain the regularized L-function is the exponent derivative of the
regularized R-function. -/
theorem hasDerivAt_regCarlsonR_L (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    HasDerivAt (fun s => regCarlsonR s b z) (regCarlsonL t b z) t :=
  (analyticAt_regCarlsonR_comp analyticAt_id analyticAt_const analyticAt_const
      hz).differentiableAt.hasDerivAt

/-- Differentiating the ordinary R-function gives the ordinary L-function. -/
theorem hasDerivAt_carlsonR_L (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    HasDerivAt (fun s => carlsonR s b z) (carlsonL t b z) t :=
  (hasDerivAt_regCarlsonR_L t b hz).const_mul (Gamma (∑ i, b i))

/-- Carlson (1987), (2.1): full joint holomorphy, with no parameter exceptions after
Gamma regularization. The coordinates are exponent, parameters, then nodes. -/
theorem analyticOnNhd_regCarlsonL_joint :
    AnalyticOnNhd ℂ (fun p : Option (ι ⊕ ι) → ℂ =>
      regCarlsonL (p none) (fun i => p (some (.inl i))) (fun i => p (some (.inr i))))
      {p | (fun i => p (some (.inr i))) ∈ carlsonRSlitDomain} := by
  classical
  have h := analyticOnNhd_regCarlsonR_joint (ι := ι) |>.partialDeriv
    (isOpen_carlsonRSlitDomain.preimage (by fun_prop)) none
  have heq : SeveralComplexVariables.partialDeriv none
      (fun p : Option (ι ⊕ ι) → ℂ => regCarlsonR (p none)
        (fun i => p (some (.inl i))) (fun i => p (some (.inr i)))) =
      (fun p => regCarlsonL (p none)
        (fun i => p (some (.inl i))) (fun i => p (some (.inr i)))) := by
    funext p
    simp only [SeveralComplexVariables.partialDeriv, regCarlsonL,
      Function.update_self, Function.update_of_ne (Option.some_ne_none _)]
  rwa [heq] at h

/-- Analytic substitutions in all arguments preserve analyticity on the slit domain. -/
theorem analyticAt_regCarlsonL_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : E → ℂ} {b z : E → ι → ℂ} {p : E}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) :
    AnalyticAt ℂ (fun q => regCarlsonL (t q) (b q) (z q)) p := by
  let f : E → Option (ι ⊕ ι) → ℂ := fun q k => k.elim (t q) (Sum.elim (b q) (z q))
  suffices hf : AnalyticAt ℂ f p from
    (analyticOnNhd_regCarlsonL_joint (f p) hslit).comp_of_eq hf rfl
  apply analyticAt_pi_iff.mpr
  intro k
  cases k with
  | none => exact ht
  | some k =>
    cases k with
    | inl i => exact (analyticAt_pi_iff.mp hb) i
    | inr i => exact (analyticAt_pi_iff.mp hz) i

/-- At fixed exponent and parameters the regularized L-function is analytic on the product
slit plane. -/
theorem analyticOnNhd_regCarlsonL (t : ℂ) (b : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonL t b) carlsonRSlitDomain := fun _ hz =>
  analyticAt_regCarlsonL_comp analyticAt_const analyticAt_const analyticAt_id hz

/-- At fixed slit-plane nodes the regularized L-function is entire jointly in the exponent
and the parameters. -/
theorem analyticOnNhd_regCarlsonL_exponent_parameters {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun p : Option ι → ℂ =>
      regCarlsonL (p none) (fun i => p (some i)) z) univ := by
  intro p _
  apply analyticAt_regCarlsonL_comp
  · exact (ContinuousLinearMap.proj none : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p
  · exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p
  · exact analyticAt_const
  · exact hz

/-- At fixed slit-plane nodes the regularized L-function is entire in the parameters. -/
theorem analyticOnNhd_regCarlsonL_parameters (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun b => regCarlsonL t b z) univ := fun _ _ =>
  analyticAt_regCarlsonL_comp analyticAt_const analyticAt_id analyticAt_const hz

/-- The ordinary L-function is jointly analytic away from the Gamma poles of the total
parameter. -/
theorem analyticAt_carlsonL_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : E → ℂ} {b z : E → ι → ℂ} {p : E}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) (hc : ∀ n : ℕ, (∑ i, b p i) ≠ -n) :
    AnalyticAt ℂ (fun q => carlsonL (t q) (b q) (z q)) p := by
  have hsum : AnalyticAt ℂ (fun q => ∑ i, b q i) p :=
    Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i
  have hrecip := (differentiable_one_div_Gamma.analyticAt (∑ i, b p i)).comp_of_eq hsum rfl
  have hgamma : AnalyticAt ℂ (fun q => Gamma (∑ i, b q i)) p := by
    have h := hrecip.inv (inv_ne_zero (Gamma_ne_zero hc))
    change AnalyticAt ℂ (fun q => ((Gamma (∑ i, b q i))⁻¹)⁻¹) p at h
    simpa only [inv_inv] using h
  exact hgamma.mul (analyticAt_regCarlsonL_comp ht hb hz hslit)

/-- On the convergence region, for right-half-plane nodes, the regularized L-function is
the power-logarithm Dirichlet average. -/
theorem regCarlsonL_eq_regCarlsonLIntegral (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonL t b z = regCarlsonLIntegral t b z := by
  unfold regCarlsonL
  simp_rw [regCarlsonR_eq_regCarlsonRIntegral _ hb hz]
  exact (hasDerivAt_regCarlsonRIntegral_L t hb hz).deriv

/-- On the convergence region the ordinary L-function is the native L-integral. -/
theorem carlsonL_eq_carlsonLIntegral (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    carlsonL t b z = carlsonLIntegral t b z := by
  simp only [carlsonL, carlsonLIntegral, regCarlsonL_eq_regCarlsonLIntegral t hb hz]

/-- The L-function satisfies the general Dirichlet-continuation specification for the
power-logarithm kernel. -/
theorem isRegCarlsonLContinuation_regCarlsonL (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    IsRegCarlsonContinuation (carlsonLKernel t) z (regCarlsonL t · z) :=
  ⟨analyticOnNhd_regCarlsonL_parameters t (carlsonRVariableDomain_subset_slitDomain hz),
    fun _ hb => regCarlsonL_eq_regCarlsonLIntegral t hb hz⟩

/-- Any entire continuation of the native L-integral in the parameters is the L-function. -/
theorem _root_.Dirichlet.IsRegCarlsonContinuation.eq_regCarlsonL {t : ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation (carlsonLKernel t) z G)
    (hz : z ∈ carlsonRVariableDomain) : G = (regCarlsonL t · z) :=
  hG.eq (isRegCarlsonLContinuation_regCarlsonL t hz)

/-- A function analytic on the slit domain that agrees with the L-function on right-half-plane
nodes agrees with it on the whole slit domain. -/
theorem eqOn_regCarlsonL_of_eqOn_variableDomain {t : ℂ} {b : ι → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F carlsonRSlitDomain)
    (heq : ∀ z ∈ carlsonRVariableDomain, F z = regCarlsonL t b z) :
    EqOn F (regCarlsonL t b) carlsonRSlitDomain :=
  eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hF (analyticOnNhd_regCarlsonL t b) heq

/-- With an empty index type the regularized L-function vanishes. -/
@[simp] theorem regCarlsonL_eq_zero_of_isEmpty [IsEmpty ι] (t : ℂ) (b z : ι → ℂ) :
    regCarlsonL t b z = 0 := by
  unfold regCarlsonL
  simp_rw [regCarlsonR_eq_zero_of_isEmpty _ b _]
  exact deriv_const t 0

end Carlson
