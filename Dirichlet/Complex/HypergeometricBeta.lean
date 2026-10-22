/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Transform.Euler
public import Pochhammer.BinomialSeries
public import ToMathlib.Analysis.SpecialFunctions.HypergeometricBeta

/-!
# The double-beta hypergeometric integral

Carlson (1977), Exercise 4.4-3. Two applications of the general beta parameter-raising
identity evaluate the double integral as a regularized `₃F₂`. The binomial kernel is
identified using the Tau Ceti contributors' complex binomial series through the
existing Pochhammer adapter. All endpoint parameters have positive real parts;
the argument lies in the open unit disk.
-/

open Complex Set MeasureTheory

public noncomputable section

namespace Dirichlet

/-- A balanced hypergeometric series converges throughout the open unit disk. -/
private theorem mem_hypergeometric_ball {A C : Multiset ℂ}
    (hcard : A.card = C.card + 1) {z : ℂ} (hz : ‖z‖ < 1) :
    z ∈ Metric.eball 0 (regularizedHGFunSeries A C).radius := by
  rw [Metric.mem_eball, edist_zero_right]
  apply lt_of_lt_of_le ?_ (radius_regularizedHGFunSeries_ge_one hcard)
  rw [← ofReal_norm, ENNReal.ofReal_lt_one]
  exact hz

/-- The `₁F₀` series is the principal binomial kernel inside its convergence disk. -/
private theorem hypergeometric_binomial (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedHGFun {a} 0 z = 1 / (1 - z) ^ a := by
  have h := hasSum_regularizedHGFun_of_mem_eball
    (a := ({a} : Multiset ℂ)) (b := 0) (mem_hypergeometric_ball (by simp) hz)
  apply h.unique
  convert hasSum_ascPochhammer_mul_pow_div_factorial a z hz using 1
  funext n
  simp [regularizedHGFunCoeff]

/-- **Carlson Exercise 4.4-3.** The doubly Gamma-regularized double-beta integral
of a binomial kernel is a regularized `₃F₂`. Multiplication by the two total-parameter
Gamma factors gives the ordinary normalized Dirichlet-average formula. -/
theorem regEulerIntegral_regEulerIntegral_binomial {a b₁ b₂ d₁ d₂ z : ℂ}
    (hb₁ : 0 < b₁.re) (hb₂ : 0 < b₂.re) (hd₁ : 0 < d₁.re) (hd₂ : 0 < d₂.re)
    (hz : ‖z‖ < 1) :
    regEulerIntegral d₁ d₂ (fun v =>
      regEulerIntegral b₁ b₂ (fun u => 1 / (1 - (u : ℂ) * ((v : ℂ) * z)) ^ a)) =
      regularizedHGFun (d₁ ::ₘ b₁ ::ₘ ({a} : Multiset ℂ))
        ((d₁ + d₂) ::ₘ ({b₁ + b₂} : Multiset ℂ)) z := by
  have hnorm {v : ℝ} (hv : v ∈ Ioo 0 1) {w : ℂ} (hw : ‖w‖ < 1) : ‖(v : ℂ) * w‖ < 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hv.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hv.2.le).trans_lt hw
  have hi (v : ℝ) (hv : v ∈ Ioo 0 1) :
      regEulerIntegral b₁ b₂ (fun u => 1 / (1 - (u : ℂ) * ((v : ℂ) * z)) ^ a) =
        regularizedHGFun (b₁ ::ₘ ({a} : Multiset ℂ)) {b₁ + b₂} ((v : ℂ) * z) := by
    rw [regEulerIntegral]
    have he := integral_betaKernel_mul_regularizedHGFun hb₁ hb₂
      (mem_hypergeometric_ball (A := ({a} : Multiset ℂ)) (C := 0) (by simp) (hnorm hv hz))
    convert he using 2
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    dsimp only
    rw [hypergeometric_binomial a (hnorm hu (hnorm hv hz))]
  rw [regEulerIntegral]
  have he := integral_betaKernel_mul_regularizedHGFun hd₁ hd₂
    (mem_hypergeometric_ball (A := b₁ ::ₘ ({a} : Multiset ℂ))
      (C := ({b₁ + b₂} : Multiset ℂ)) (by simp) hz)
  convert he using 2
  apply setIntegral_congr_fun measurableSet_Ioo
  intro v hv
  dsimp only
  rw [hi v hv]

end Dirichlet
