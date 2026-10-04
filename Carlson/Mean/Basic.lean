/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.L.Properties
public import Carlson.R.SmallVariableContinuation
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Complex hypergeometric means

The hypergeometric mean, the two-order ratio mean, and the power-transformed mean
are defined using the principal logarithm of the continued R-function. The zero
order and coincident-order cases use L, the exponent derivative of R.

These are total functions, but their analytic interpretation requires admissible
nodes, avoidance of Gamma poles, and appropriate logarithm branches. In particular,
complex roots do not inherit unrestricted homogeneity from R. The real positive
theory is developed separately.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), 759–766.
* J. L. Brenner and B. C. Carlson, *Homogeneous mean values: weights and asymptotics*,
  J. Math. Anal. Appl. 123 (1987), 265–280, equations (3.12), (3.18), (3.19).
-/

open Complex Dirichlet Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The logarithm used to define the complex hypergeometric mean, including order zero. -/
def carlsonMeanLog (t : ℂ) (b z : ι → ℂ) : ℂ :=
  if t = 0 then carlsonL 0 b z else log (carlsonR t b z) / t

/-- Carlson's hypergeometric mean, using the principal logarithm for nonzero order. -/
def carlsonMean (t : ℂ) (b z : ι → ℂ) : ℂ := exp (carlsonMeanLog t b z)

/-- The logarithm of the two-order ratio mean, with its derivative value on the diagonal. -/
def carlsonRatioMeanLog (s t : ℂ) (b z : ι → ℂ) : ℂ :=
  if s = t then carlsonL t b z / carlsonR t b z
  else (log (carlsonR t b z) - log (carlsonR s b z)) / (t - s)

/-- Brenner–Carlson's two-order ratio mean (3.18), on principal logarithm branches. -/
def carlsonRatioMean (s t : ℂ) (b z : ι → ℂ) : ℂ :=
  exp (carlsonRatioMeanLog s t b z)

/-- The logarithm defining the power-transformed mean. Its zero power is the weighted
geometric mean, with complex weights `b i / ∑ j, b j`. -/
def carlsonPowerMeanLog (s t : ℂ) (b z : ι → ℂ) : ℂ :=
  if s = 0 then ∑ i, (b i / ∑ j, b j) * log (z i)
  else carlsonMeanLog t b (fun i => z i ^ s) / s

/-- Brenner–Carlson's power-transformed mean (3.19). The logarithm is divided before
exponentiating, avoiding a second, potentially inconsistent, principal logarithm. -/
def carlsonPowerMean (s t : ℂ) (b z : ι → ℂ) : ℂ :=
  exp (carlsonPowerMeanLog s t b z)

/-- The zero-order mean is the exponential of the logarithmic Dirichlet average. -/
@[simp] theorem carlsonMean_zero (b z : ι → ℂ) :
    carlsonMean 0 b z = exp (carlsonL 0 b z) := by simp [carlsonMean, carlsonMeanLog]

/-- The nonzero-order defining formula for the hypergeometric mean. -/
theorem carlsonMean_of_ne_zero {t : ℂ} (ht : t ≠ 0) (b z : ι → ℂ) :
    carlsonMean t b z = exp (log (carlsonR t b z) / t) := by
  simp [carlsonMean, carlsonMeanLog, ht]

/-- A complex hypergeometric mean never vanishes. -/
theorem carlsonMean_ne_zero (t : ℂ) (b z : ι → ℂ) : carlsonMean t b z ≠ 0 :=
  exp_ne_zero _

/-- The diagonal value of the ratio mean uses the logarithmic exponent derivative. -/
@[simp] theorem carlsonRatioMean_self (t : ℂ) (b z : ι → ℂ) :
    carlsonRatioMean t t b z = exp (carlsonL t b z / carlsonR t b z) := by
  simp [carlsonRatioMean, carlsonRatioMeanLog]

/-- Interchanging the two orders leaves the ratio mean unchanged. -/
theorem carlsonRatioMean_symm (s t : ℂ) (b z : ι → ℂ) :
    carlsonRatioMean s t b z = carlsonRatioMean t s b z := by
  by_cases h : s = t
  · subst t; rfl
  · simp only [carlsonRatioMean, carlsonRatioMeanLog, h, Ne.symm h, ↓reduceIte]
    congr 1
    apply (div_eq_div_iff (sub_ne_zero.mpr (Ne.symm h)) (sub_ne_zero.mpr h)).mpr
    ring

/-- At power one the transformed family is the original hypergeometric mean. -/
@[simp] theorem carlsonPowerMean_one (t : ℂ) (b z : ι → ℂ) :
    carlsonPowerMean 1 t b z = carlsonMean t b z := by
  simp [carlsonPowerMean, carlsonPowerMeanLog, carlsonMean]

/-- At power zero the transformed family is independent of its order. -/
@[simp] theorem carlsonPowerMean_zero (t : ℂ) (b z : ι → ℂ) :
    carlsonPowerMean 0 t b z = exp (∑ i, (b i / ∑ j, b j) * log (z i)) := by
  simp [carlsonPowerMean, carlsonPowerMeanLog]

/-- R at the all-one vector is one away from poles of the ordinary normalization. -/
theorem carlsonR_one_nodes (t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) : carlsonR t b (fun _ => 1) = 1 := by
  rw [carlsonR, regCarlsonR_const_node t b (by norm_num)]
  simp [Gamma_ne_zero hb]

/-- Exponent zero gives one on the full product slit domain, for all nonexceptional parameters. -/
theorem carlsonR_zero_exponent {b z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain)
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) : carlsonR 0 b z = 1 := by
  have h : regCarlsonR 0 b z = (Gamma (∑ i, b i))⁻¹ := by
    apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
      (analyticOnNhd_regCarlsonR 0 b) analyticOnNhd_const _ hz
    intro w hw
    simpa using regCarlsonR_natCast 0 b hw
  rw [carlsonR, h]
  simp [Gamma_ne_zero hb]

/-- All orders of the hypergeometric mean are normalized at the all-one vector. -/
@[simp] theorem carlsonMean_one_nodes (t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) : carlsonMean t b (fun _ => 1) = 1 := by
  simp [carlsonMean, carlsonMeanLog, carlsonR_one_nodes t hb, carlsonL]

/-- All orders of the ratio mean are normalized at the all-one vector. -/
@[simp] theorem carlsonRatioMean_one_nodes (s t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) : carlsonRatioMean s t b (fun _ => 1) = 1 := by
  simp [carlsonRatioMean, carlsonRatioMeanLog, carlsonR_one_nodes _ hb, carlsonL]

/-- Setting one order to zero recovers the hypergeometric mean. -/
theorem carlsonRatioMean_zero_left (t : ℂ) {b z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) :
    carlsonRatioMean 0 t b z = carlsonMean t b z := by
  by_cases ht : t = 0
  · subst t; simp [carlsonR_zero_exponent hz hb]
  · simp [carlsonRatioMean, carlsonRatioMeanLog, carlsonMean, carlsonMeanLog, ht,
      Ne.symm ht, carlsonR_zero_exponent hz hb]

/-- The first-order mean is R itself wherever R is nonzero. -/
theorem carlsonMean_one_order (b z : ι → ℂ) (h : carlsonR 1 b z ≠ 0) :
    carlsonMean 1 b z = carlsonR 1 b z := by
  simp [carlsonMean, carlsonMeanLog, exp_log h]

/-- For fixed order, the mean is analytic along analytic parameter and node maps, on the
principal logarithm branch. At order zero no logarithm condition is needed. -/
theorem analyticAt_carlsonMean_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℂ) {b z : E → ι → ℂ} {p : E}
    (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) (hc : ∀ n : ℕ, (∑ i, b p i) ≠ -n)
    (hlog : t ≠ 0 → carlsonR t (b p) (z p) ∈ slitPlane) :
    AnalyticAt ℂ (fun q => carlsonMean t (b q) (z q)) p := by
  by_cases ht : t = 0
  · subst t
    simpa only [carlsonMean_zero, Function.comp_def] using
      (analyticAt_carlsonL_comp analyticAt_const hb hz hslit hc).cexp
  · simp only [carlsonMean, carlsonMeanLog, ht, ↓reduceIte]
    exact (((analyticAt_carlsonR_comp analyticAt_const hb hz hslit hc).clog
      (hlog ht)).div_const (c := t)).cexp

/-- The ratio mean is analytic in parameters and nodes on its stated logarithm branches. -/
theorem analyticAt_carlsonRatioMean_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s t : ℂ) {b z : E → ι → ℂ} {p : E}
    (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) (hc : ∀ n : ℕ, (∑ i, b p i) ≠ -n)
    (hs : carlsonR s (b p) (z p) ∈ slitPlane)
    (ht : carlsonR t (b p) (z p) ∈ slitPlane) :
    AnalyticAt ℂ (fun q => carlsonRatioMean s t (b q) (z q)) p := by
  have hR a := analyticAt_carlsonR_comp (t := fun _ => a) analyticAt_const hb hz hslit hc
  by_cases h : s = t
  · subst s
    simp only [carlsonRatioMean_self]
    exact ((analyticAt_carlsonL_comp analyticAt_const hb hz hslit hc).div
      (hR t) (slitPlane_ne_zero ht)).cexp
  · simp only [carlsonRatioMean, carlsonRatioMeanLog, h, ↓reduceIte]
    exact ((((hR t).clog ht).sub ((hR s).clog hs)).div_const (c := t - s)).cexp

/-- As a function of its second order, the logarithmic ratio mean is the extended divided
difference of `log R`. This also identifies the value at coincident orders. -/
theorem carlsonRatioMeanLog_eq_dslope (s t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) (hs : carlsonR s b z ∈ slitPlane) :
    carlsonRatioMeanLog s t b z = dslope (fun a => log (carlsonR a b z)) s t := by
  by_cases h : s = t
  · subst t
    simp only [carlsonRatioMeanLog, ↓reduceIte, dslope_same]
    exact ((hasDerivAt_carlsonR_L s b hz).clog hs).deriv.symm
  · simp [carlsonRatioMeanLog, h, dslope_of_ne _ (Ne.symm h), slope_def_field]

/-- The coincident-order definition removes the singularity analytically in either order. -/
theorem analyticAt_carlsonRatioMean_order_self (s : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) (hs : carlsonR s b z ∈ slitPlane) :
    AnalyticAt ℂ (fun t => carlsonRatioMean s t b z) s := by
  have hR : AnalyticAt ℂ (fun t => carlsonR t b z) s :=
    analyticAt_const.mul
      (analyticAt_regCarlsonR_comp analyticAt_id analyticAt_const analyticAt_const hz)
  have ha := hR.clog hs
  obtain ⟨p, hp⟩ := ha
  have hd := hp.has_fpower_series_dslope_fslope.analyticAt.cexp
  simpa only [carlsonRatioMean, carlsonRatioMeanLog_eq_dslope s _ b hz hs,
    Function.comp_def] using hd

/-- The zero-order definition removes the singularity analytically in the order. -/
theorem analyticAt_carlsonMean_order_zero {b z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) :
    AnalyticAt ℂ (fun t => carlsonMean t b z) 0 := by
  have h := analyticAt_carlsonRatioMean_order_self 0 b
    hz
    (by rw [carlsonR_zero_exponent hz hb]; exact one_mem_slitPlane)
  simpa only [carlsonRatioMean_zero_left _ hz hb] using h

/-- The logarithm defining M is analytic in parameters and nodes on its principal branch. -/
theorem analyticAt_carlsonMeanLog_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℂ) {b z : E → ι → ℂ} {p : E}
    (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) (hc : ∀ n : ℕ, (∑ i, b p i) ≠ -n)
    (hlog : t ≠ 0 → carlsonR t (b p) (z p) ∈ slitPlane) :
    AnalyticAt ℂ (fun q => carlsonMeanLog t (b q) (z q)) p := by
  by_cases ht : t = 0
  · subst t
    simpa only [carlsonMeanLog, ↓reduceIte] using
      analyticAt_carlsonL_comp analyticAt_const hb hz hslit hc
  · simp only [carlsonMeanLog, ht, ↓reduceIte]
    exact ((analyticAt_carlsonR_comp analyticAt_const hb hz hslit hc).clog
      (hlog ht)).div_const

/-- The power-transformed mean is analytic in parameters and nodes when both the original
nodes and the powered nodes lie on their stated principal branches. -/
theorem analyticAt_carlsonPowerMean_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s t : ℂ) {b z : E → ι → ℂ} {p : E}
    (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) (hc : ∀ n : ℕ, (∑ i, b p i) ≠ -n)
    (hpow : s ≠ 0 → (fun i => z p i ^ s) ∈ carlsonRSlitDomain)
    (hlog : s ≠ 0 → t ≠ 0 → carlsonR t (b p) (fun i => z p i ^ s) ∈ slitPlane) :
    AnalyticAt ℂ (fun q => carlsonPowerMean s t (b q) (z q)) p := by
  by_cases hs : s = 0
  · subst s
    simp only [carlsonPowerMean_zero]
    apply AnalyticAt.cexp'
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (((analyticAt_pi_iff.mp hb) i).div
      (Finset.analyticAt_fun_sum _ fun j _ => (analyticAt_pi_iff.mp hb) j)
      (by simpa using hc 0)).mul (((analyticAt_pi_iff.mp hz) i).clog (hslit i))
  · have hp : AnalyticAt ℂ (fun q i => z q i ^ s) p :=
      analyticAt_pi_iff.mpr fun i => ((analyticAt_pi_iff.mp hz) i).cpow
        analyticAt_const (hslit i)
    simp only [carlsonPowerMean, carlsonPowerMeanLog, hs, ↓reduceIte]
    exact ((analyticAt_carlsonMeanLog_comp t hb hp (hpow hs) hc
      (hlog hs)).div_const (c := s)).cexp'

/-- The power-transformed mean is normalized at the all-one node vector. -/
@[simp] theorem carlsonPowerMean_one_nodes (s t : ℂ) {b : ι → ℂ}
    (hb : ∀ n : ℕ, (∑ i, b i) ≠ -n) : carlsonPowerMean s t b (fun _ => 1) = 1 := by
  simp [carlsonPowerMean, carlsonPowerMeanLog, carlsonMeanLog, carlsonL,
    carlsonR_one_nodes t hb]

/-- Analytic dependence on the complex order away from zero on the principal branch. -/
theorem analyticAt_carlsonMean_order_of_ne_zero {t : ℂ} (ht : t ≠ 0) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (hlog : carlsonR t b z ∈ slitPlane) :
    AnalyticAt ℂ (fun a => carlsonMean a b z) t := by
  have hR : AnalyticAt ℂ (fun a => carlsonR a b z) t :=
    analyticAt_const.mul
      (analyticAt_regCarlsonR_comp analyticAt_id analyticAt_const analyticAt_const hz)
  have ha := ((hR.clog hlog).div analyticAt_id ht).cexp'
  apply ha.congr
  filter_upwards [isOpen_ne.mem_nhds ht] with a ha
  exact (carlsonMean_of_ne_zero ha b z).symm

end Carlson
