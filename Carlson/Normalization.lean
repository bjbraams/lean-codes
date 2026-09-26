/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Normalization.Basic
public import Carlson.R.Explicit
public import Carlson.L.Continuation
public import Carlson.S.Continuation
public import Carlson.T

/-!
# Gamma normalization for Carlson's R, L, S and T functions

All four regularized functions are entire in the Dirichlet parameters on their stated
node domains. The ordinary functions are jointly holomorphic away from nonpositive integral
total parameters and meromorphic under one-complex-variable analytic substitutions.

At total parameter `-m`, varying a chosen coordinate while holding all others fixed gives
residue `(-1)^m / m!` times the regularized value. The singularity on this transverse line
is removable exactly when that value vanishes; its finite limit is the same Gamma residue
times the derivative of the regularized slice. This pointwise condition must not be confused
with divisibility along an entire exceptional hypersurface in several variables.

## Main results

* `Carlson.analyticAt_carlsonS_comp`, `Carlson.analyticAt_carlsonT_comp`, and
  `Carlson.analyticAt_carlsonTSlit_comp`: ordinary joint holomorphy, complementing R and L.
* `Carlson.meromorphicAt_carlsonR_comp` and its L, S, T analogues: meromorphic analytic slices.
* `Carlson.tendsto_carlsonR_parameterLine` and its analogues: exceptional-parameter residues.
* `Carlson.exists_analyticAt_carlsonR_parameterLine_iff` and its analogues: removability.
* `Carlson.tendsto_carlsonR_parameterLine_of_eq_zero` and its analogues: finite removable values.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 6.
* B. C. Carlson, *Dirichlet averages of x^t log x*, SIAM J. Math. Anal. 18 (1987), 550–565.
-/

open Complex Dirichlet Set Filter
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- A transverse parameter line, varying coordinate `i` so that the total parameter is `c`.
All other coordinates retain their values in `b`. -/
def carlsonParameterLine (b : ι → ℂ) (i : ι) (c : ℂ) : ι → ℂ :=
  Function.update b i (b i + c - ∑ j, b j)

/-- The distinguished parameter line has total parameter equal to its argument. -/
@[simp] theorem sum_carlsonParameterLine (b : ι → ℂ) (i : ι) (c : ℂ) :
    ∑ j, carlsonParameterLine b i c j = c := by
  classical
  unfold carlsonParameterLine
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hs : ∑ j ∈ Finset.univ \ {i}, b j + b i = ∑ j, b j := by
    simpa only [Finset.sdiff_singleton_eq_erase] using
      Finset.sum_erase_add Finset.univ b (Finset.mem_univ i)
  rw [← hs]
  ring

/-- At the original total parameter the transverse line passes through the original vector. -/
@[simp] theorem carlsonParameterLine_sum (b : ι → ℂ) (i : ι) :
    carlsonParameterLine b i (∑ j, b j) = b := by
  classical
  simp [carlsonParameterLine]

/-- The total-parameter line is entire. -/
theorem analyticAt_carlsonParameterLine (b : ι → ℂ) (i : ι) (c : ℂ) :
    AnalyticAt ℂ (carlsonParameterLine b i) c := by
  classical
  apply analyticAt_pi_iff.mpr
  intro j
  by_cases h : j = i
  · subst j
    simp only [carlsonParameterLine, Function.update_self]
    exact (analyticAt_const.add analyticAt_id).sub analyticAt_const
  · simp only [carlsonParameterLine, Function.update_of_ne h]
    exact analyticAt_const

/-- The regularized germ restricted to a transverse total-parameter line remains analytic. -/
theorem analyticAt_parameterLine_comp {F : (ι → ℂ) → ℂ} {b : ι → ℂ}
    (hF : AnalyticAt ℂ F b) (i : ι) {m : ℕ} (hm : ∑ j, b j = -m) :
    AnalyticAt ℂ (fun c => F (carlsonParameterLine b i c)) (-m) :=
  hF.comp_of_eq (analyticAt_carlsonParameterLine b i (-m)) (by rw [← hm, carlsonParameterLine_sum])

/-- The residue of a Gamma normalization along a transverse total-parameter line. -/
theorem tendsto_Gamma_mul_parameterLine {F : (ι → ℂ) → ℂ} {b : ι → ℂ}
    (hF : AnalyticAt ℂ F b) (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    Tendsto (fun c => (c + m) * (Gamma c * F (carlsonParameterLine b i c)))
      (𝓝[≠] (-m : ℂ)) (𝓝 (((-1 : ℂ) ^ m / m.factorial) * F b)) := by
  have he : carlsonParameterLine b i (-m) = b := by rw [← hm, carlsonParameterLine_sum]
  simpa only [he] using tendsto_mul_Gamma_mul m (analyticAt_parameterLine_comp hF i hm).continuousAt

/-- Removability of a transverse parameter slice is equivalent to vanishing of the
regularized value at the base vector. -/
theorem exists_analyticAt_Gamma_mul_parameterLine_iff {F : (ι → ℂ) → ℂ} {b : ι → ℂ}
    (hF : AnalyticAt ℂ F b) (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    (∃ H : ℂ → ℂ, AnalyticAt ℂ H (-m) ∧
      (fun c => Gamma c * F (carlsonParameterLine b i c)) =ᶠ[𝓝[≠] (-m : ℂ)] H) ↔ F b = 0 := by
  have he : carlsonParameterLine b i (-m) = b := by rw [← hm, carlsonParameterLine_sum]
  simpa only [he] using exists_analyticAt_Gamma_mul_iff m (analyticAt_parameterLine_comp hF i hm)

/-- The finite value on a removable transverse slice is determined by the derivative of
the regularized slice, not by the totalized ordinary product. -/
theorem tendsto_Gamma_mul_parameterLine_of_eq_zero {F : (ι → ℂ) → ℂ} {b : ι → ℂ}
    (hF : AnalyticAt ℂ F b) (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) (hzero : F b = 0) :
    Tendsto (fun c => Gamma c * F (carlsonParameterLine b i c)) (𝓝[≠] (-m : ℂ))
      (𝓝 (((-1 : ℂ) ^ m / m.factorial) *
        deriv (fun c => F (carlsonParameterLine b i c)) (-m))) := by
  apply tendsto_Gamma_mul_of_eq_zero m
    (analyticAt_parameterLine_comp hF i hm).differentiableAt
  rwa [show carlsonParameterLine b i (-m) = b by rw [← hm, carlsonParameterLine_sum]]

/-- Every analytic one-complex-variable specialization of the ordinary R-function is
meromorphic, including at exceptional total parameters. -/
theorem meromorphicAt_carlsonR_comp {t : ℂ → ℂ} {b z : ℂ → ι → ℂ} {p : ℂ}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hdom : z p ∈ carlsonRSlitDomain) :
    MeromorphicAt (fun q => carlsonR (t q) (b q) (z q)) p :=
  meromorphicAt_Gamma_mul_comp
    (Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i)
    (analyticAt_regCarlsonR_comp ht hb hz hdom)

/-- The ordinary R-function has residue `(-1)^m / m!` times its regularized value
on a transverse line through total parameter `-m`. -/
theorem tendsto_carlsonR_parameterLine (t : ℂ) {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonRSlitDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    Tendsto (fun c => (c + m) * carlsonR t (carlsonParameterLine b i c) z)
      (𝓝[≠] (-m : ℂ)) (𝓝 (((-1 : ℂ) ^ m / m.factorial) * regCarlsonR t b z)) := by
  simpa only [carlsonR, sum_carlsonParameterLine] using
    tendsto_Gamma_mul_parameterLine (F := fun a => regCarlsonR t a z)
      (analyticAt_regCarlsonR_comp analyticAt_const analyticAt_id analyticAt_const hz) i m hm

/-- The exceptional total parameter is removable on a transverse R-slice exactly
when the regularized value vanishes at the base vector. -/
theorem exists_analyticAt_carlsonR_parameterLine_iff (t : ℂ) {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonRSlitDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    (∃ H : ℂ → ℂ, AnalyticAt ℂ H (-m) ∧
      (fun c => carlsonR t (carlsonParameterLine b i c) z) =ᶠ[𝓝[≠] (-m : ℂ)] H) ↔
      regCarlsonR t b z = 0 := by
  simpa only [carlsonR, sum_carlsonParameterLine] using
    exists_analyticAt_Gamma_mul_parameterLine_iff (F := fun a => regCarlsonR t a z)
      (analyticAt_regCarlsonR_comp analyticAt_const analyticAt_id analyticAt_const hz) i m hm

/-- The finite removable value of the ordinary R-function on a transverse parameter line. -/
theorem tendsto_carlsonR_parameterLine_of_eq_zero (t : ℂ) {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonRSlitDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) (hzero : regCarlsonR t b z = 0) :
    Tendsto (fun c => carlsonR t (carlsonParameterLine b i c) z) (𝓝[≠] (-m : ℂ))
      (𝓝 (((-1 : ℂ) ^ m / m.factorial) *
        deriv (fun c => regCarlsonR t (carlsonParameterLine b i c) z) (-m))) := by
  simpa only [carlsonR, sum_carlsonParameterLine] using
    tendsto_Gamma_mul_parameterLine_of_eq_zero (F := fun a => regCarlsonR t a z)
      (analyticAt_regCarlsonR_comp analyticAt_const analyticAt_id analyticAt_const hz) i m hm hzero

/-- Every analytic one-complex-variable specialization of the ordinary L-function is
meromorphic, including at exceptional total parameters. -/
theorem meromorphicAt_carlsonL_comp {t : ℂ → ℂ} {b z : ℂ → ι → ℂ} {p : ℂ}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hdom : z p ∈ carlsonRSlitDomain) :
    MeromorphicAt (fun q => carlsonL (t q) (b q) (z q)) p :=
  meromorphicAt_Gamma_mul_comp
    (Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i)
    (analyticAt_regCarlsonL_comp ht hb hz hdom)

/-- The ordinary L-function has residue `(-1)^m / m!` times its regularized value
on a transverse line through total parameter `-m`. -/
theorem tendsto_carlsonL_parameterLine (t : ℂ) {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonRSlitDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    Tendsto (fun c => (c + m) * carlsonL t (carlsonParameterLine b i c) z)
      (𝓝[≠] (-m : ℂ)) (𝓝 (((-1 : ℂ) ^ m / m.factorial) * regCarlsonL t b z)) := by
  simpa only [carlsonL, sum_carlsonParameterLine] using
    tendsto_Gamma_mul_parameterLine (F := fun a => regCarlsonL t a z)
      (analyticAt_regCarlsonL_comp analyticAt_const analyticAt_id analyticAt_const hz) i m hm

/-- The exceptional total parameter is removable on a transverse L-slice exactly
when the regularized value vanishes at the base vector. -/
theorem exists_analyticAt_carlsonL_parameterLine_iff (t : ℂ) {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonRSlitDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    (∃ H : ℂ → ℂ, AnalyticAt ℂ H (-m) ∧
      (fun c => carlsonL t (carlsonParameterLine b i c) z) =ᶠ[𝓝[≠] (-m : ℂ)] H) ↔
      regCarlsonL t b z = 0 := by
  simpa only [carlsonL, sum_carlsonParameterLine] using
    exists_analyticAt_Gamma_mul_parameterLine_iff (F := fun a => regCarlsonL t a z)
      (analyticAt_regCarlsonL_comp analyticAt_const analyticAt_id analyticAt_const hz) i m hm

/-- The finite removable value of the ordinary L-function on a transverse parameter line. -/
theorem tendsto_carlsonL_parameterLine_of_eq_zero (t : ℂ) {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonRSlitDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) (hzero : regCarlsonL t b z = 0) :
    Tendsto (fun c => carlsonL t (carlsonParameterLine b i c) z) (𝓝[≠] (-m : ℂ))
      (𝓝 (((-1 : ℂ) ^ m / m.factorial) *
        deriv (fun c => regCarlsonL t (carlsonParameterLine b i c) z) (-m))) := by
  simpa only [carlsonL, sum_carlsonParameterLine] using
    tendsto_Gamma_mul_parameterLine_of_eq_zero (F := fun a => regCarlsonL t a z)
      (analyticAt_regCarlsonL_comp analyticAt_const analyticAt_id analyticAt_const hz) i m hm hzero

/-- The ordinary S-function is jointly analytic away from Gamma poles of the total parameter. -/
theorem analyticAt_carlsonS_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b z : E → ι → ℂ} {p : E} (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hreg : ∀ m : ℕ, (∑ i, b p i) ≠ -m) :
    AnalyticAt ℂ (fun q => carlsonS (b q) (z q)) p :=
  analyticAt_Gamma_mul_comp
    (Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i)
    (analyticAt_regCarlsonS_comp hb hz) hreg

/-- Every analytic one-complex-variable specialization of the ordinary S-function is
meromorphic, including at exceptional total parameters. -/
theorem meromorphicAt_carlsonS_comp {b z : ℂ → ι → ℂ} {p : ℂ}
    (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p) :
    MeromorphicAt (fun q => carlsonS (b q) (z q)) p :=
  meromorphicAt_Gamma_mul_comp
    (Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i)
    (analyticAt_regCarlsonS_comp hb hz)

/-- The ordinary S-function has residue `(-1)^m / m!` times its regularized value
on a transverse line through total parameter `-m`. -/
theorem tendsto_carlsonS_parameterLine {b : ι → ℂ} (z : ι → ℂ)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    Tendsto (fun c => (c + m) * carlsonS (carlsonParameterLine b i c) z)
      (𝓝[≠] (-m : ℂ)) (𝓝 (((-1 : ℂ) ^ m / m.factorial) * regCarlsonS b z)) := by
  simpa only [carlsonS, sum_carlsonParameterLine] using
    tendsto_Gamma_mul_parameterLine (F := fun a => regCarlsonS a z)
      (analyticAt_regCarlsonS_comp analyticAt_id analyticAt_const) i m hm

/-- The exceptional total parameter is removable on a transverse S-slice exactly
when the regularized value vanishes at the base vector. -/
theorem exists_analyticAt_carlsonS_parameterLine_iff {b : ι → ℂ} (z : ι → ℂ)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    (∃ H : ℂ → ℂ, AnalyticAt ℂ H (-m) ∧
      (fun c => carlsonS (carlsonParameterLine b i c) z) =ᶠ[𝓝[≠] (-m : ℂ)] H) ↔
      regCarlsonS b z = 0 := by
  simpa only [carlsonS, sum_carlsonParameterLine] using
    exists_analyticAt_Gamma_mul_parameterLine_iff (F := fun a => regCarlsonS a z)
      (analyticAt_regCarlsonS_comp analyticAt_id analyticAt_const) i m hm

/-- The finite removable value of the ordinary S-function on a transverse parameter line. -/
theorem tendsto_carlsonS_parameterLine_of_eq_zero {b : ι → ℂ} (z : ι → ℂ)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) (hzero : regCarlsonS b z = 0) :
    Tendsto (fun c => carlsonS (carlsonParameterLine b i c) z) (𝓝[≠] (-m : ℂ))
      (𝓝 (((-1 : ℂ) ^ m / m.factorial) *
        deriv (fun c => regCarlsonS (carlsonParameterLine b i c) z) (-m))) := by
  simpa only [carlsonS, sum_carlsonParameterLine] using
    tendsto_Gamma_mul_parameterLine_of_eq_zero (F := fun a => regCarlsonS a z)
      (analyticAt_regCarlsonS_comp analyticAt_id analyticAt_const) i m hm hzero

/-- The ordinary T-function is jointly analytic away from Gamma poles of the total parameter. -/
theorem analyticAt_carlsonT_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b z : E → ι → ℂ} {p : E} (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hdom : z p ∈ carlsonTVariableDomain)
    (hreg : ∀ m : ℕ, (∑ i, b p i) ≠ -m) :
    AnalyticAt ℂ (fun q => carlsonT (b q) (z q)) p :=
  analyticAt_Gamma_mul_comp
    (Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i)
    (analyticAt_regCarlsonT_comp hb hz hdom) hreg

/-- Every analytic one-complex-variable specialization of the ordinary T-function is
meromorphic, including at exceptional total parameters. -/
theorem meromorphicAt_carlsonT_comp {b z : ℂ → ι → ℂ} {p : ℂ}
    (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p) (hdom : z p ∈ carlsonTVariableDomain) :
    MeromorphicAt (fun q => carlsonT (b q) (z q)) p :=
  meromorphicAt_Gamma_mul_comp
    (Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i)
    (analyticAt_regCarlsonT_comp hb hz hdom)

/-- The ordinary T-function has residue `(-1)^m / m!` times its regularized value
on a transverse line through total parameter `-m`. -/
theorem tendsto_carlsonT_parameterLine {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonTVariableDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    Tendsto (fun c => (c + m) * carlsonT (carlsonParameterLine b i c) z)
      (𝓝[≠] (-m : ℂ)) (𝓝 (((-1 : ℂ) ^ m / m.factorial) * regCarlsonT b z)) := by
  simpa only [carlsonT, sum_carlsonParameterLine] using
    tendsto_Gamma_mul_parameterLine (F := fun a => regCarlsonT a z)
      (analyticAt_regCarlsonT_comp analyticAt_id analyticAt_const hz) i m hm

/-- The exceptional total parameter is removable on a transverse T-slice exactly
when the regularized value vanishes at the base vector. -/
theorem exists_analyticAt_carlsonT_parameterLine_iff {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonTVariableDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    (∃ H : ℂ → ℂ, AnalyticAt ℂ H (-m) ∧
      (fun c => carlsonT (carlsonParameterLine b i c) z) =ᶠ[𝓝[≠] (-m : ℂ)] H) ↔
      regCarlsonT b z = 0 := by
  simpa only [carlsonT, sum_carlsonParameterLine] using
    exists_analyticAt_Gamma_mul_parameterLine_iff (F := fun a => regCarlsonT a z)
      (analyticAt_regCarlsonT_comp analyticAt_id analyticAt_const hz) i m hm

/-- The finite removable value of the ordinary T-function on a transverse parameter line. -/
theorem tendsto_carlsonT_parameterLine_of_eq_zero {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonTVariableDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) (hzero : regCarlsonT b z = 0) :
    Tendsto (fun c => carlsonT (carlsonParameterLine b i c) z) (𝓝[≠] (-m : ℂ))
      (𝓝 (((-1 : ℂ) ^ m / m.factorial) *
        deriv (fun c => regCarlsonT (carlsonParameterLine b i c) z) (-m))) := by
  simpa only [carlsonT, sum_carlsonParameterLine] using
    tendsto_Gamma_mul_parameterLine_of_eq_zero (F := fun a => regCarlsonT a z)
      (analyticAt_regCarlsonT_comp analyticAt_id analyticAt_const hz) i m hm hzero

/-- The ordinary principal T-branch is jointly analytic away from Gamma poles of the
total parameter. -/
theorem analyticAt_carlsonTSlit_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b z : E → ι → ℂ} {p : E} (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hdom : z p ∈ carlsonRSlitDomain)
    (hreg : ∀ m : ℕ, (∑ i, b p i) ≠ -m) :
    AnalyticAt ℂ (fun q => carlsonTSlit (b q) (z q)) p :=
  analyticAt_Gamma_mul_comp
    (Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i)
    (analyticAt_regCarlsonTSlit_comp hb hz hdom) hreg

/-- Every analytic one-complex-variable specialization of the ordinary principal T-branch is
meromorphic, including at exceptional total parameters. -/
theorem meromorphicAt_carlsonTSlit_comp {b z : ℂ → ι → ℂ} {p : ℂ}
    (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hdom : z p ∈ carlsonRSlitDomain) :
    MeromorphicAt (fun q => carlsonTSlit (b q) (z q)) p :=
  meromorphicAt_Gamma_mul_comp
    (Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i)
    (analyticAt_regCarlsonTSlit_comp hb hz hdom)

/-- The ordinary principal T-branch has residue `(-1)^m / m!` times its regularized value
on a transverse line through total parameter `-m`. -/
theorem tendsto_carlsonTSlit_parameterLine {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonRSlitDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    Tendsto (fun c => (c + m) * carlsonTSlit (carlsonParameterLine b i c) z)
      (𝓝[≠] (-m : ℂ)) (𝓝 (((-1 : ℂ) ^ m / m.factorial) * regCarlsonTSlit b z)) := by
  simpa only [carlsonTSlit, sum_carlsonParameterLine] using
    tendsto_Gamma_mul_parameterLine (F := fun a => regCarlsonTSlit a z)
      (analyticAt_regCarlsonTSlit_comp analyticAt_id analyticAt_const hz) i m hm

/-- The exceptional total parameter is removable on a transverse principal T-slice exactly
when the regularized value vanishes at the base vector. -/
theorem exists_analyticAt_carlsonTSlit_parameterLine_iff {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonRSlitDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) :
    (∃ H : ℂ → ℂ, AnalyticAt ℂ H (-m) ∧
      (fun c => carlsonTSlit (carlsonParameterLine b i c) z) =ᶠ[𝓝[≠] (-m : ℂ)] H) ↔
      regCarlsonTSlit b z = 0 := by
  simpa only [carlsonTSlit, sum_carlsonParameterLine] using
    exists_analyticAt_Gamma_mul_parameterLine_iff (F := fun a => regCarlsonTSlit a z)
      (analyticAt_regCarlsonTSlit_comp analyticAt_id analyticAt_const hz) i m hm

/-- The finite removable value of the ordinary principal T-branch on a transverse parameter line. -/
theorem tendsto_carlsonTSlit_parameterLine_of_eq_zero {b : ι → ℂ} (z : ι → ℂ)
    (hz : z ∈ carlsonRSlitDomain)
    (i : ι) (m : ℕ) (hm : ∑ j, b j = -m) (hzero : regCarlsonTSlit b z = 0) :
    Tendsto (fun c => carlsonTSlit (carlsonParameterLine b i c) z) (𝓝[≠] (-m : ℂ))
      (𝓝 (((-1 : ℂ) ^ m / m.factorial) *
        deriv (fun c => regCarlsonTSlit (carlsonParameterLine b i c) z) (-m))) := by
  simpa only [carlsonTSlit, sum_carlsonParameterLine] using
    tendsto_Gamma_mul_parameterLine_of_eq_zero (F := fun a => regCarlsonTSlit a z)
      (analyticAt_regCarlsonTSlit_comp analyticAt_id analyticAt_const hz) i m hm hzero

end Carlson
