/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SmallVariableContinuation
public import Carlson.TwoVariable.QuadraticSlit
public import Carlson.TwoVariable.ParameterSymmetry
public import ComplexAnalysis.RealUniqueness
public import Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The hybrid quadratic transformation, the AGM and Borchardt's algorithm

Eliminating the equal-parameter R-function between the two quadratic transformations gives
Carlson's hybrid Transformation 6.10-4,
`R_t(β, 1/2 - t; x², y²) = R_{2t}(2β, 1/2 - t - β; (x+y)/2, y)`. It is first obtained at real
nodes, where square roots of the transformed nodes can be chosen explicitly, and at parameters
where Legendre's duplication ratio does not vanish; the identity theorem then removes both
restrictions.

The second transformation at `-t = β = 1/2` is the invariance of `R_K` under the
arithmetic-geometric mean step, which with Mathlib's AGM gives Gauss's formula
`R_K(x², y²) = 1/M(x, y)` for positive reals. The hybrid transformation at `-t = β = 1/2`,
together with the parameter interchange of the two-variable R-function, gives the invariance of
`R_C` under Borchardt's step, and hence Borchardt's algorithm. For positive real nodes `R_C` is
an elementary integral, evaluated by the substitution `u = v²` and an explicit antiderivative;
this gives the inverse-circular and logarithmic forms (6.9-15), (6.9-16).

## Main results

* `Carlson.TwoVariable.regR_hybridQuadratic`: Transformation 6.10-4 for all complex `t, β`
  and nodes with positive real parts.
* `Carlson.TwoVariable.carlsonRK_sq_eq`: invariance of `R_K` (Example 6.10-2, equation (5)).
* `Carlson.TwoVariable.carlsonRK_sq_eq_inv_agm`: Gauss's formula (Example 6.10-2, equation (8)).
* `Carlson.TwoVariable.carlsonRC_sq_eq`: invariance of `R_C` (Example 6.10-5, equation (23)).
* `Carlson.TwoVariable.exists_borchardt_limit`: Borchardt's algorithm (Example 6.10-5,
  equation (26)).
* `Carlson.TwoVariable.carlsonRC_of_lt`, `Carlson.TwoVariable.carlsonRC_of_gt`: the elementary
  values (6.9-15), (6.9-16) of `R_C`, with `arcsin_eq_mul_carlsonRC` and
  `log_eq_mul_carlsonRC`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.10.
-/

open Dirichlet
open Complex Set Filter
open scoped Topology
@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- A pair of analytic functions is analytic as a map to `Fin 2 → ℂ`. -/
private theorem analyticAt_pair {f g : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hg : AnalyticAt ℂ g p) : AnalyticAt ℂ (fun q => pair (f q) (g q)) p := by
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact hf
  · exact hg

/-- Right-half-plane points lie in the slit plane. -/
private theorem mem_slitPlane_of_re_pos' {z : ℂ} (hz : 0 < z.re) : z ∈ slitPlane := Or.inl hz

/-- The hybrid identity in square-root coordinates, before removal of the Gamma factor. -/
private theorem hybrid_sqrt_of_ne (t β r s : ℂ) (hr : 0 < r.re) (hs : 0 < s.re)
    (hr2 : 0 < (r ^ 2).re) (hs2 : 0 < (s ^ 2).re) (hq : quadraticGammaRatio β ≠ 0) :
    regCarlsonR t (pair (β + t) (1 / 2 - t))
        (pair (arithmeticMeanSq (r ^ 2) (s ^ 2)) (geometricMeanSq (r ^ 2) (s ^ 2))) =
      regCarlsonR (2 * t) (pair (2 * β + 2 * t) (1 / 2 - β - 2 * t))
        (pair (arithmeticMeanSq r s) (geometricMeanSq r s)) := by
  have h1 := regRSlit_firstQuadratic t β (r ^ 2) (s ^ 2) hr2 hs2
  have h2 := regRSlit_secondQuadratic (2 * t) β r s hr hs
  rw [show 2 * β + 2 * t = 2 * β + (2 * t) by ring,
    show 1 / 2 - β - 2 * t = 1 / 2 - β - (2 * t) by ring]
  exact mul_left_cancel₀ hq (h1.symm.trans h2)

/-- The hybrid identity in square-root coordinates, for every parameter. -/
private theorem hybrid_sqrt (t β r s : ℂ) (hr : 0 < r.re) (hs : 0 < s.re)
    (hr2 : 0 < (r ^ 2).re) (hs2 : 0 < (s ^ 2).re) :
    regCarlsonR t (pair (β + t) (1 / 2 - t))
        (pair (arithmeticMeanSq (r ^ 2) (s ^ 2)) (geometricMeanSq (r ^ 2) (s ^ 2))) =
      regCarlsonR (2 * t) (pair (2 * β + 2 * t) (1 / 2 - β - 2 * t))
        (pair (arithmeticMeanSq r s) (geometricMeanSq r s)) := by
  have hm2 := meanSquares_mem_slitDomain hr2 hs2
  have hm := meanSquares_mem_slitDomain hr hs
  have hF : AnalyticOnNhd ℂ (fun β : ℂ => regCarlsonR t (pair (β + t) (1 / 2 - t))
      (pair (arithmeticMeanSq (r ^ 2) (s ^ 2)) (geometricMeanSq (r ^ 2) (s ^ 2)))) univ :=
    fun β _ => analyticAt_regCarlsonR_comp analyticAt_const
      (analyticAt_pair (analyticAt_id.add analyticAt_const) analyticAt_const) analyticAt_const hm2
  have hG : AnalyticOnNhd ℂ (fun β : ℂ => regCarlsonR (2 * t)
      (pair (2 * β + 2 * t) (1 / 2 - β - 2 * t))
      (pair (arithmeticMeanSq r s) (geometricMeanSq r s))) univ :=
    fun β _ => analyticAt_regCarlsonR_comp analyticAt_const
      (analyticAt_pair ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
        ((analyticAt_const.sub analyticAt_id).sub analyticAt_const)) analyticAt_const hm
  have h := hF.eq_of_eqOn_posReal hG fun x hx => by
    refine hybrid_sqrt_of_ne t x r s hr hs hr2 hs2 ?_
    unfold quadraticGammaRatio
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (inv_ne_zero (Gamma_ne_zero_of_re_pos (by simpa)))
    · exact cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
    · exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  exact congrFun h β

/-- The hybrid identity at real nodes `x > y > 0`. -/
private theorem hybrid_real (t β : ℂ) {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
    regCarlsonR t (pair β (1 / 2 - t)) (pair ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)) =
      regCarlsonR (2 * t) (pair (2 * β) (1 / 2 - t - β)) (pair (((x : ℂ) + y) / 2) y) := by
  set a := Real.sqrt ((x + y) / 2)
  set b := Real.sqrt ((x - y) / 2)
  have ha2 : a ^ 2 = (x + y) / 2 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (x - y) / 2 := Real.sq_sqrt (by linarith)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hab : b < a := by
    apply Real.sqrt_lt_sqrt (by linarith); linarith
  have hr : (0 : ℝ) < a + b := by linarith
  have hs : (0 : ℝ) < a - b := by linarith
  have h := hybrid_sqrt t (β - t) ((a + b : ℝ) : ℂ) ((a - b : ℝ) : ℂ)
    (by simpa using hr) (by simpa using hs)
    (by rw [← ofReal_pow, ofReal_re]; positivity) (by rw [← ofReal_pow, ofReal_re]; positivity)
  have e1 : arithmeticMeanSq (((a + b : ℝ) : ℂ) ^ 2) (((a - b : ℝ) : ℂ) ^ 2) = (x : ℂ) ^ 2 := by
    unfold arithmeticMeanSq
    have : (((a + b) ^ 2 + (a - b) ^ 2) / 2 : ℝ) = x := by nlinarith
    rw [← this]; push_cast; ring
  have e2 : geometricMeanSq (((a + b : ℝ) : ℂ) ^ 2) (((a - b : ℝ) : ℂ) ^ 2) = (y : ℂ) ^ 2 := by
    unfold geometricMeanSq
    have : ((a + b) * (a - b) : ℝ) = y := by nlinarith
    rw [← this]; push_cast; ring
  have e3 : arithmeticMeanSq ((a + b : ℝ) : ℂ) ((a - b : ℝ) : ℂ) = ((x : ℂ) + y) / 2 := by
    unfold arithmeticMeanSq
    have : (((a + b + (a - b)) / 2) ^ 2 : ℝ) = (x + y) / 2 := by nlinarith
    rw [show ((x : ℂ) + y) / 2 = (((x + y) / 2 : ℝ) : ℂ) by push_cast; ring, ← this]
    push_cast; ring
  have e4 : geometricMeanSq ((a + b : ℝ) : ℂ) ((a - b : ℝ) : ℂ) = (y : ℂ) := by
    unfold geometricMeanSq
    have : ((a + b) * (a - b) : ℝ) = y := by nlinarith
    rw [← this]; push_cast; ring
  rw [e1, e2, e3, e4, sub_add_cancel, show 2 * (β - t) + 2 * t = 2 * β by ring,
    show 1 / 2 - (β - t) - 2 * t = 1 / 2 - t - β by ring] at h
  exact h

/-- Two functions of two nodes, holomorphic in each node separately on the right half-plane,
agree there once they agree at real nodes `x > y > 0`. -/
theorem eqOn_rightHalfPlane₂_of_real {F G : ℂ → ℂ → ℂ}
    (hF₁ : ∀ y : ℂ, 0 < y.re → AnalyticOnNhd ℂ (fun x => F x y) {z | 0 < z.re})
    (hG₁ : ∀ y : ℂ, 0 < y.re → AnalyticOnNhd ℂ (fun x => G x y) {z | 0 < z.re})
    (hF₂ : ∀ x : ℂ, 0 < x.re → AnalyticOnNhd ℂ (fun y => F x y) {z | 0 < z.re})
    (hG₂ : ∀ x : ℂ, 0 < x.re → AnalyticOnNhd ℂ (fun y => G x y) {z | 0 < z.re})
    (h : ∀ x y : ℝ, 0 < y → y < x → F x y = G x y) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    F x y = G x y := by
  have hU : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have step1 : ∀ y₀ : ℝ, 0 < y₀ → ∀ X : ℂ, 0 < X.re → F X y₀ = G X y₀ := by
    intro y₀ hy₀ X hX
    have hy₀' : 0 < (y₀ : ℂ).re := by simpa using hy₀
    refine (hF₁ _ hy₀').eqOn_of_eventuallyEq_ofReal (hG₁ _ hy₀') hU
      (show ((y₀ + 1 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re} by simp; linarith) ?_ hX
    filter_upwards [eventually_gt_nhds (show y₀ < y₀ + 1 by linarith)] with x hx
    exact h x y₀ hy₀ hx
  refine (hF₂ x hx).eqOn_of_eventuallyEq_ofReal (hG₂ x hx) hU
    (show ((1 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re} by simp) ?_ hy
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with y₀ hy₀
  exact step1 y₀ hy₀ x hx

/-- Squares of right-half-plane nodes lie in the slit domain. -/
private theorem sq_pair_mem_slitDomain {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    pair (x ^ 2) (y ^ 2) ∈ carlsonRSlitDomain := by
  intro i; fin_cases i
  · exact sq_mem_slitPlane_of_re_pos hx
  · exact sq_mem_slitPlane_of_re_pos hy

/-- The mean and second node of a right-half-plane pair lie in the slit domain. -/
private theorem mean_pair_mem_slitDomain {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    pair ((x + y) / 2) y ∈ carlsonRSlitDomain := by
  intro i; fin_cases i
  · refine mem_slitPlane_of_re_pos' ?_
    change 0 < ((x + y) / 2).re
    simp only [div_ofNat_re, add_re]; linarith
  · exact mem_slitPlane_of_re_pos' hy

/-- **Transformation 6.10-4** (hybrid quadratic transformation), in regularized form for all
complex `t, β` and nodes with positive real parts:
`R_t(β, 1/2 - t; x², y²) = R_{2t}(2β, 1/2 - t - β; (x+y)/2, y)`. Both sides carry the same
total parameter `β + 1/2 - t`, so the identity also holds in ordinary normalization. -/
theorem regR_hybridQuadratic (t β x y : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonR t (pair β (1 / 2 - t)) (pair (x ^ 2) (y ^ 2)) =
      regCarlsonR (2 * t) (pair (2 * β) (1 / 2 - t - β)) (pair ((x + y) / 2) y) := by
  refine eqOn_rightHalfPlane₂_of_real (F := fun X Y =>
      regCarlsonR t (pair β (1 / 2 - t)) (pair (X ^ 2) (Y ^ 2)))
    (G := fun X Y => regCarlsonR (2 * t) (pair (2 * β) (1 / 2 - t - β)) (pair ((X + Y) / 2) Y))
    ?_ ?_ ?_ ?_ (fun x y hy hxy => hybrid_real t β hy hxy) hx hy
  · intro Y hY X hX
    exact analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pair (analyticAt_id.pow 2) analyticAt_const)
      (sq_pair_mem_slitDomain hX hY)
  · intro Y hY X hX
    exact analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pair ((analyticAt_id.add analyticAt_const).div_const) analyticAt_const)
      (mean_pair_mem_slitDomain hX hY)
  · intro X hX Y hY
    exact analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pair analyticAt_const (analyticAt_id.pow 2))
      (sq_pair_mem_slitDomain hX hY)
  · intro X hX Y hY
    exact analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pair ((analyticAt_const.add analyticAt_id).div_const) analyticAt_id)
      (mean_pair_mem_slitDomain hX hY)


/-! ### Gauss's arithmetic-geometric mean and Borchardt's algorithm -/

/-- Carlson's symmetric complete elliptic integral `R_K(ξ, η) = R_{-1/2}(1/2, 1/2; ξ, η)`
(Example 6.10-2, equation (4)). -/
def carlsonRK (ξ η : ℂ) : ℂ := carlsonR (-1 / 2) (pair (1 / 2) (1 / 2)) (pair ξ η)

/-- Carlson's degenerate elliptic integral `R_C(ξ, η) = R_{-1/2}(1/2, 1; ξ, η)`
(equation (6.9-14)). -/
def carlsonRC (ξ η : ℂ) : ℂ := carlsonR (-1 / 2) (pair (1 / 2) 1) (pair ξ η)

/-- Legendre's duplication ratio equals one at `β = 1/2`. -/
theorem quadraticGammaRatio_one_half : quadraticGammaRatio (1 / 2) = 1 := by
  unfold quadraticGammaRatio
  rw [Complex.Gamma_one_half_eq, show (1 : ℂ) - 2 * (1 / 2) = 0 by ring, cpow_zero, one_mul,
    Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
  push_cast
  exact mul_inv_cancel₀ ((cpow_ne_zero_iff).mpr (Or.inl (by exact_mod_cast Real.pi_pos.ne')))

/-- On equal slit-plane nodes the ordinary R-function of two nodes is a power, for convergent
parameters: `R_t(b; z, z) = z^t`. -/
theorem carlsonR_pair_self (t : ℂ) {b : Fin 2 → ℂ} (hb : b ∈ mvBetaConvergent) {z : ℂ}
    (hz : z ∈ slitPlane) : carlsonR t b (pair z z) = z ^ t := by
  have hzz : pair z z = fun _ : Fin 2 => z := by
    funext i; fin_cases i <;> rfl
  have hc : 0 < (∑ i, b i).re := by
    rw [re_sum]; exact Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  unfold carlsonR
  rw [hzz, regCarlsonR_const_node t b hz, mul_comm, mul_assoc,
    inv_mul_cancel₀ (Gamma_ne_zero_of_re_pos hc), mul_one]

/-- `R_K` is symmetric in its two nodes on the slit plane. -/
theorem carlsonRK_comm {ξ η : ℂ} (hξ : ξ ∈ slitPlane) (hη : η ∈ slitPlane) :
    carlsonRK ξ η = carlsonRK η ξ := by
  unfold carlsonRK carlsonR
  rw [regCarlsonR_pair_swap _ _ _ hη hξ]

/-- **Invariance of `R_K`** under the arithmetic-geometric mean step (Example 6.10-2,
equation (5)): `R_K(x², y²) = R_K(((x+y)/2)², xy)` for `re x, re y > 0`. -/
theorem carlsonRK_sq_eq (x y : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    carlsonRK (x ^ 2) (y ^ 2) = carlsonRK (((x + y) / 2) ^ 2) (x * y) := by
  have h := regRSlit_secondQuadratic (-1 / 2) (1 / 2) x y hx hy
  rw [quadraticGammaRatio_one_half, one_mul,
    show 2 * (1 / 2 : ℂ) + -1 / 2 = 1 / 2 by ring,
    show (1 / 2 : ℂ) - 1 / 2 - -1 / 2 = 1 / 2 by ring] at h
  unfold carlsonRK carlsonR
  rw [h]
  rfl

/-- The value of `R_K` on the diagonal: `R_K(z, z) = z^{-1/2}` for slit-plane `z`. -/
theorem carlsonRK_self {z : ℂ} (hz : z ∈ slitPlane) : carlsonRK z z = z ^ (-1 / 2 : ℂ) :=
  carlsonR_pair_self _ (fun i => by fin_cases i <;> norm_num [pair]) hz

/-- `R_K` is continuous at every pair of slit-plane nodes. -/
theorem continuousAt_carlsonRK {ξ η : ℂ} (hξ : ξ ∈ slitPlane) (hη : η ∈ slitPlane) :
    ContinuousAt (fun w : Fin 2 → ℂ => carlsonR (-1 / 2) (pair (1 / 2) (1 / 2)) w) (pair ξ η) := by
  have hmem : pair ξ η ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hξ
    · exact hη
  exact continuousAt_const.mul
    ((analyticOnNhd_regCarlsonR _ _ _ hmem).continuousAt)

/-- **Gauss's formula** (Example 6.10-2, equation (8)): for positive reals,
`R_K(x², y²) = 1 / M(x, y)`, where `M` is Gauss's arithmetic-geometric mean. -/
theorem carlsonRK_sq_eq_inv_agm {x y : NNReal} (hx : 0 < x) (hy : 0 < y) :
    carlsonRK (((x : ℝ) : ℂ) ^ 2) (((y : ℝ) : ℂ) ^ 2) = ((NNReal.agm x y : ℝ) : ℂ)⁻¹ := by
  set g : ℕ → NNReal := fun n => (NNReal.agmSequences x y n).1
  set a : ℕ → NNReal := fun n => (NNReal.agmSequences x y n).2
  have hg0 : 0 < g 0 := by
    simp only [g, NNReal.agmSequences_zero]
    exact NNReal.sqrt_pos.mpr (mul_pos hx hy)
  have hgpos : ∀ n, 0 < g n := fun n => hg0.trans_le (NNReal.agmSequences_fst_monotone
    (Nat.zero_le n))
  have hapos : ∀ n, 0 < a n := fun n => (hgpos n).trans_le (NNReal.agmSequences_fst_le_snd n n)
  have hre : ∀ w : NNReal, 0 < w → 0 < (((w : ℝ) : ℂ)).re := fun w hw => by
    simpa using hw
  have hslit : ∀ w : NNReal, 0 < w → (((w : ℝ) : ℂ)) ^ 2 ∈ slitPlane := fun w hw =>
    sq_mem_slitPlane_of_re_pos (hre w hw)
  -- one step of the invariance, followed by the symmetry of `R_K`
  have hstep : ∀ u v : NNReal, 0 < u → 0 < v →
      carlsonRK (((u : ℝ) : ℂ) ^ 2) (((v : ℝ) : ℂ) ^ 2) =
        carlsonRK (((NNReal.sqrt (u * v) : ℝ) : ℂ) ^ 2) ((((u + v) / 2 : NNReal) : ℝ) ^ 2 : ℂ) := by
    intro u v hu hv
    rw [carlsonRK_sq_eq _ _ (hre u hu) (hre v hv)]
    have huv : (((NNReal.sqrt (u * v) : ℝ) : ℂ)) ^ 2 = ((u : ℝ) : ℂ) * ((v : ℝ) : ℂ) := by
      rw [← ofReal_pow, ← NNReal.coe_pow, NNReal.sq_sqrt]; push_cast; ring
    have ham : ((((u + v) / 2 : NNReal) : ℝ) ^ 2 : ℂ) = ((((u : ℝ) : ℂ) + (v : ℝ)) / 2) ^ 2 := by
      push_cast; ring
    rw [huv, ham, carlsonRK_comm]
    · exact sq_mem_slitPlane_of_re_pos (by
        simp only [div_ofNat_re, add_re]; linarith [hre u hu, hre v hv])
    · exact mul_mem_slitPlane_of_re_pos (hre u hu) (hre v hv)
  have hinv : ∀ n, carlsonRK (((x : ℝ) : ℂ) ^ 2) (((y : ℝ) : ℂ) ^ 2) =
      carlsonRK (((g n : ℝ) : ℂ) ^ 2) (((a n : ℝ) : ℂ) ^ 2) := by
    intro n
    induction n with
    | zero => exact hstep x y hx hy
    | succ n ih =>
      rw [ih, hstep _ _ (hgpos n) (hapos n)]
      simp only [g, a, NNReal.agmSequences_succ']
  set M := NNReal.agm x y
  have hM : 0 < M := NNReal.agm_pos hx hy
  have hlim : Tendsto (fun n => pair (((g n : ℝ) : ℂ) ^ 2) (((a n : ℝ) : ℂ) ^ 2)) atTop
      (𝓝 (pair (((M : ℝ) : ℂ) ^ 2) (((M : ℝ) : ℂ) ^ 2))) := by
    have hg : Tendsto (fun n => ((g n : ℝ) : ℂ)) atTop (𝓝 ((M : ℝ) : ℂ)) :=
      (continuous_ofReal.comp NNReal.continuous_coe).continuousAt.tendsto.comp
        NNReal.tendsto_agmSequences_fst_agm
    have ha : Tendsto (fun n => ((a n : ℝ) : ℂ)) atTop (𝓝 ((M : ℝ) : ℂ)) :=
      (continuous_ofReal.comp NNReal.continuous_coe).continuousAt.tendsto.comp
        NNReal.tendsto_agmSequences_snd_agm
    refine tendsto_pi_nhds.mpr fun i => ?_
    fin_cases i
    · exact hg.pow 2
    · exact ha.pow 2
  have hc := ((continuousAt_carlsonRK (hslit M hM) (hslit M hM)).tendsto.comp hlim)
  have hc' : Tendsto (fun _ : ℕ => carlsonRK (((x : ℝ) : ℂ) ^ 2) (((y : ℝ) : ℂ) ^ 2)) atTop
      (𝓝 (carlsonRK (((M : ℝ) : ℂ) ^ 2) (((M : ℝ) : ℂ) ^ 2))) := by
    refine hc.congr fun n => ?_
    exact (hinv n).symm
  rw [tendsto_nhds_unique tendsto_const_nhds hc', carlsonRK_self (mem_slitPlane_iff.mpr (Or.inl (by
    rw [← ofReal_pow, ofReal_re]; positivity)))]
  rw [← ofReal_pow, show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), ← ofReal_inv]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul M.coe_nonneg]
  norm_num [Real.rpow_neg_one]


/-- The regularized Borchardt invariance at real nodes `x > y > 0`. -/
private theorem regR_borchardt_real {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
    regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)) =
      regCarlsonR (-1 / 2) (pair (1 / 2) 1)
        (pair ((((x : ℂ) + y) / 2) ^ 2) ((((x : ℂ) + y) / 2) * y)) := by
  set a : ℝ := (x + y) / 2
  have ha : 0 < a := by simp only [a]; linarith
  have hac : (((x : ℂ) + y) / 2) = (a : ℂ) := by simp only [a]; push_cast; ring
  rw [hac]
  have hre : ∀ w : ℝ, 0 < w → 0 < (w : ℂ).re := fun w hw => by simpa using hw
  have h1 := regR_hybridQuadratic (-1 / 2) (1 / 2) x y (hre x (by linarith)) (hre y hy)
  rw [show ((x : ℂ) + y) / 2 = (a : ℂ) from hac] at h1
  have h2 := regCarlsonR_parameterInterchange (-1) 1 (1 / 2) (hre a ha) (hre y hy)
  have h3 := regCarlsonR_parameterInterchange (-1 / 2) (1 / 2) 1
    (x := (a : ℂ) ^ 2) (y := (a : ℂ) * y) (by rw [← ofReal_pow]; exact hre _ (by positivity))
    (by rw [← ofReal_mul]; exact hre _ (by positivity))
  have h4 := regCarlsonR_parameterInterchange (-1) 1 (1 / 2) (x := 1) (y := (y : ℂ) / a)
    (by norm_num) (by rw [← ofReal_div]; exact hre _ (by positivity))
  have hpow : ((a : ℂ) ^ 2) ^ (-1 / 2 : ℂ) = (a : ℂ) ^ (-1 : ℂ) := by
    rw [← ofReal_pow, show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow ha.le]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
  have hq : (a : ℂ) * y / (a : ℂ) ^ 2 = y / a := by
    have : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp
  norm_num at h1 h2 h3 h4
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring] at hpow ⊢
  rw [h1, h2, h3, hq, h4, hpow]


/-- The nodes of the Borchardt step lie in the slit domain. -/
private theorem borchardt_pair_mem_slitDomain {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    pair (((x + y) / 2) ^ 2) (((x + y) / 2) * y) ∈ carlsonRSlitDomain := by
  have ha : 0 < ((x + y) / 2).re := by simp only [div_ofNat_re, add_re]; linarith
  intro i; fin_cases i
  · exact sq_mem_slitPlane_of_re_pos ha
  · exact mul_mem_slitPlane_of_re_pos ha hy

/-- **Invariance of `R_C`** under Borchardt's step (Example 6.10-5, equation (23)):
`R_C(x², y²) = R_C(((x+y)/2)², ((x+y)/2) y)` for `re x, re y > 0`. -/
theorem carlsonRC_sq_eq (x y : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    carlsonRC (x ^ 2) (y ^ 2) = carlsonRC (((x + y) / 2) ^ 2) (((x + y) / 2) * y) := by
  unfold carlsonRC carlsonR
  congr 1
  refine eqOn_rightHalfPlane₂_of_real (F := fun X Y =>
      regCarlsonR (-1 / 2) (pair (1 / 2) 1) (pair (X ^ 2) (Y ^ 2)))
    (G := fun X Y => regCarlsonR (-1 / 2) (pair (1 / 2) 1)
      (pair (((X + Y) / 2) ^ 2) (((X + Y) / 2) * Y)))
    ?_ ?_ ?_ ?_ (fun x y hy hxy => regR_borchardt_real hy hxy) hx hy
  · intro Y hY X hX
    exact analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pair (analyticAt_id.pow 2) analyticAt_const) (sq_pair_mem_slitDomain hX hY)
  · intro Y hY X hX
    exact analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pair (((analyticAt_id.add analyticAt_const).div_const).pow 2)
        (((analyticAt_id.add analyticAt_const).div_const).mul analyticAt_const))
      (borchardt_pair_mem_slitDomain hX hY)
  · intro X hX Y hY
    exact analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pair analyticAt_const (analyticAt_id.pow 2)) (sq_pair_mem_slitDomain hX hY)
  · intro X hX Y hY
    exact analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pair (((analyticAt_const.add analyticAt_id).div_const).pow 2)
        (((analyticAt_const.add analyticAt_id).div_const).mul analyticAt_id))
      (borchardt_pair_mem_slitDomain hX hY)


/-- Borchardt's sequences (Example 6.10-5, equation (24)):
`xₙ₊₁ = (xₙ + yₙ)/2`, `yₙ₊₁ = (xₙ₊₁ yₙ)^{1/2}`. -/
def borchardtSeq (x y : ℝ) : ℕ → ℝ × ℝ
  | 0 => (x, y)
  | n + 1 => (((borchardtSeq x y n).1 + (borchardtSeq x y n).2) / 2,
      Real.sqrt (((borchardtSeq x y n).1 + (borchardtSeq x y n).2) / 2 * (borchardtSeq x y n).2))

/-- The recursion step of Borchardt's sequences. -/
theorem borchardtSeq_succ (x y : ℝ) (n : ℕ) : borchardtSeq x y (n + 1) =
    (((borchardtSeq x y n).1 + (borchardtSeq x y n).2) / 2,
      Real.sqrt (((borchardtSeq x y n).1 + (borchardtSeq x y n).2) / 2 * (borchardtSeq x y n).2)) :=
  rfl

/-- Borchardt's sequences stay above the smaller starting value, and their difference halves
at least at each step. -/
theorem borchardtSeq_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    min x y ≤ (borchardtSeq x y n).1 ∧ min x y ≤ (borchardtSeq x y n).2 ∧
      |(borchardtSeq x y n).1 - (borchardtSeq x y n).2| ≤ |x - y| / 2 ^ n := by
  induction n with
  | zero => simp [borchardtSeq]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    set u := (borchardtSeq x y n).1
    set v := (borchardtSeq x y n).2
    have hm : 0 < min x y := lt_min hx hy
    set w := (u + v) / 2
    have hw : min x y ≤ w := by simp only [w]; linarith
    have hs : Real.sqrt (w * v) ∈ Set.uIcc v w := by
      rcases le_total v w with h | h
      · rw [Set.uIcc_of_le h]
        constructor
        · calc v = Real.sqrt (v * v) := (Real.sqrt_mul_self (by linarith)).symm
            _ ≤ Real.sqrt (w * v) := Real.sqrt_le_sqrt (by nlinarith)
        · calc Real.sqrt (w * v) ≤ Real.sqrt (w * w) := Real.sqrt_le_sqrt (by nlinarith)
            _ = w := Real.sqrt_mul_self (by linarith)
      · rw [Set.uIcc_of_ge h]
        constructor
        · calc w = Real.sqrt (w * w) := (Real.sqrt_mul_self (by linarith)).symm
            _ ≤ Real.sqrt (w * v) := Real.sqrt_le_sqrt (by nlinarith)
        · calc Real.sqrt (w * v) ≤ Real.sqrt (v * v) := Real.sqrt_le_sqrt (by nlinarith)
            _ = v := Real.sqrt_mul_self (by linarith)
    have hs' := Set.mem_uIcc.mp hs
    refine ⟨hw, ?_, ?_⟩
    · show min x y ≤ Real.sqrt (w * v)
      rcases hs' with h | h <;> linarith [h.1, h.2]
    · show |w - Real.sqrt (w * v)| ≤ |x - y| / 2 ^ (n + 1)
      have hwv : |w - Real.sqrt (w * v)| ≤ |w - v| := by
        rcases hs' with h | h
        · rw [abs_of_nonneg (by linarith [h.2]), abs_of_nonneg (by linarith [h.1])]; linarith [h.1]
        · rw [abs_of_nonpos (by linarith [h.1]), abs_of_nonpos (by linarith [h.2])]; linarith [h.2]
      have hwv' : |w - v| = |u - v| / 2 := by
        simp only [w]; rw [show (u + v) / 2 - v = (u - v) / 2 by ring, abs_div]; norm_num
      rw [pow_succ, ← div_div]
      linarith

/-- **Borchardt's algorithm** (Example 6.10-5, equation (26)): for positive `x₀, y₀`,
Borchardt's sequences have a common positive limit `L`, and `R_C(x₀², y₀²) = 1/L`. -/
theorem exists_borchardt_limit {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (fun n => (borchardtSeq x y n).1) atTop (𝓝 L) ∧
      Tendsto (fun n => (borchardtSeq x y n).2) atTop (𝓝 L) ∧
      carlsonRC ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) = ((L : ℂ))⁻¹ := by
  set p := borchardtSeq x y
  have hb := borchardtSeq_bounds hx hy
  have hm : 0 < min x y := lt_min hx hy
  set D := |x - y|
  have hdiff : ∀ n, |(p n).1 - (p n).2| ≤ D / 2 ^ n := fun n => (hb n).2.2
  -- both sequences are Cauchy
  have hc1 : CauchySeq fun n => (p n).1 := by
    refine cauchySeq_of_le_geometric_two (C := D) fun n => ?_
    rw [Real.dist_eq]
    show |(p n).1 - ((p n).1 + (p n).2) / 2| ≤ D / 2 / 2 ^ n
    rw [show (p n).1 - ((p n).1 + (p n).2) / 2 = ((p n).1 - (p n).2) / 2 by ring, abs_div,
      abs_two, div_right_comm]
    exact div_le_div_of_nonneg_right (hdiff n) (by norm_num)
  have hc2 : CauchySeq fun n => (p n).2 := by
    refine cauchySeq_of_le_geometric_two (C := D) fun n => ?_
    rw [Real.dist_eq, abs_sub_comm]
    have h := (hb (n + 1)).2.2
    have h' := hdiff n
    -- `yₙ₊₁` lies between `yₙ` and `xₙ₊₁`
    have hmid : |(p (n + 1)).2 - (p n).2| ≤ |(p (n + 1)).1 - (p n).2| := by
      set u := (p n).1
      set v := (p n).2
      have hv : 0 < v := hm.trans_le (hb n).2.1
      have hu : 0 < u := hm.trans_le (hb n).1
      show |Real.sqrt ((u + v) / 2 * v) - v| ≤ |(u + v) / 2 - v|
      set w := (u + v) / 2
      have hw : 0 < w := by simp only [w]; linarith
      rcases le_total v w with hvw | hvw
      · have h1 : v ≤ Real.sqrt (w * v) := by
          calc v = Real.sqrt (v * v) := (Real.sqrt_mul_self hv.le).symm
            _ ≤ Real.sqrt (w * v) := Real.sqrt_le_sqrt (by nlinarith)
        have h2 : Real.sqrt (w * v) ≤ w := by
          calc Real.sqrt (w * v) ≤ Real.sqrt (w * w) := Real.sqrt_le_sqrt (by nlinarith)
            _ = w := Real.sqrt_mul_self hw.le
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · have h1 : Real.sqrt (w * v) ≤ v := by
          calc Real.sqrt (w * v) ≤ Real.sqrt (v * v) := Real.sqrt_le_sqrt (by nlinarith)
            _ = v := Real.sqrt_mul_self hv.le
        have h2 : w ≤ Real.sqrt (w * v) := by
          calc w = Real.sqrt (w * w) := (Real.sqrt_mul_self hw.le).symm
            _ ≤ Real.sqrt (w * v) := Real.sqrt_le_sqrt (by nlinarith)
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    have hx1 : |(p (n + 1)).1 - (p n).2| = |(p n).1 - (p n).2| / 2 := by
      show |((p n).1 + (p n).2) / 2 - (p n).2| = _
      rw [show ((p n).1 + (p n).2) / 2 - (p n).2 = ((p n).1 - (p n).2) / 2 by ring, abs_div,
        abs_two]
    calc |(p (n + 1)).2 - (p n).2| ≤ |(p n).1 - (p n).2| / 2 := hmid.trans hx1.le
      _ ≤ D / 2 ^ n / 2 := div_le_div_of_nonneg_right h' (by norm_num)
      _ = D / 2 / 2 ^ n := by ring
  obtain ⟨L, hL1⟩ := cauchySeq_tendsto_of_complete hc1
  obtain ⟨L', hL2⟩ := cauchySeq_tendsto_of_complete hc2
  have hdiff0 : Tendsto (fun n => (p n).1 - (p n).2) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => hdiff n) ?_
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ)))).const_mul D
  have hLL : L = L' := sub_eq_zero.mp (tendsto_nhds_unique (hL1.sub hL2) hdiff0)
  subst hLL
  have hLpos : 0 < L := hm.trans_le (ge_of_tendsto hL1 (Eventually.of_forall fun n => (hb n).1))
  refine ⟨L, hLpos, hL1, hL2, ?_⟩
  have hre : ∀ w : ℝ, 0 < w → 0 < (w : ℂ).re := fun w hw => by simpa using hw
  have hpos : ∀ n, 0 < (p n).1 ∧ 0 < (p n).2 := fun n =>
    ⟨hm.trans_le (hb n).1, hm.trans_le (hb n).2.1⟩
  have hinv : ∀ n, carlsonRC ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) =
      carlsonRC (((p n).1 : ℂ) ^ 2) (((p n).2 : ℂ) ^ 2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [ih, carlsonRC_sq_eq _ _ (hre _ (hpos n).1) (hre _ (hpos n).2)]
      congr 1
      · show _ = ((((p n).1 + (p n).2) / 2 : ℝ) : ℂ) ^ 2
        push_cast; ring
      · show _ = ((Real.sqrt (((p n).1 + (p n).2) / 2 * (p n).2) : ℝ) : ℂ) ^ 2
        rw [← ofReal_pow, Real.sq_sqrt (by nlinarith [(hpos n).1, (hpos n).2])]
        push_cast; ring
  have hlim : Tendsto (fun n => pair (((p n).1 : ℂ) ^ 2) (((p n).2 : ℂ) ^ 2)) atTop
      (𝓝 (pair ((L : ℂ) ^ 2) ((L : ℂ) ^ 2))) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    fin_cases i
    · exact ((continuous_ofReal.tendsto L).comp hL1).pow 2
    · exact ((continuous_ofReal.tendsto L).comp hL2).pow 2
  have hslit : (L : ℂ) ^ 2 ∈ slitPlane := sq_mem_slitPlane_of_re_pos (hre L hLpos)
  have hmem : pair ((L : ℂ) ^ 2) ((L : ℂ) ^ 2) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i <;> exact hslit
  have hcont : ContinuousAt (fun w : Fin 2 → ℂ => carlsonR (-1 / 2) (pair (1 / 2) 1) w)
      (pair ((L : ℂ) ^ 2) ((L : ℂ) ^ 2)) :=
    continuousAt_const.mul ((analyticOnNhd_regCarlsonR _ _ _ hmem).continuousAt)
  have hc' : Tendsto (fun _ : ℕ => carlsonRC ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)) atTop
      (𝓝 (carlsonRC ((L : ℂ) ^ 2) ((L : ℂ) ^ 2))) :=
    (hcont.tendsto.comp hlim).congr fun n => (hinv n).symm
  rw [tendsto_nhds_unique tendsto_const_nhds hc']
  unfold carlsonRC
  rw [carlsonR_pair_self _ (fun i => by fin_cases i <;> norm_num [pair])
    (mem_slitPlane_iff.mpr (Or.inl (by rw [← ofReal_pow]; exact hre _ (by positivity))))]
  rw [← ofReal_pow, show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), ← ofReal_inv]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
  norm_num [Real.rpow_neg_one]

/-! ### Elementary values of `R_C` -/

open MeasureTheory

/-- The real integral behind `R_C` for `0 < x < y`:
`∫₀¹ (1 - v² + x v²)^{-1/2} (1 - v² + y v²)^{-1} dv = arctan(√(y-x) / √x) / √(y-x)`. -/
theorem integral_carlsonRC_of_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    ∫ v in (0 : ℝ)..1, (Real.sqrt (1 - v ^ 2 + x * v ^ 2))⁻¹ * (1 - v ^ 2 + y * v ^ 2)⁻¹ =
      Real.arctan (Real.sqrt (y - x) / Real.sqrt x) / Real.sqrt (y - x) := by
  set c := Real.sqrt (y - x)
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hc2 : c ^ 2 = y - x := Real.sq_sqrt (by linarith)
  have hh : ∀ v ∈ uIcc (0 : ℝ) 1, 0 < 1 - v ^ 2 + x * v ^ 2 := by
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    have h1 : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    rcases eq_or_lt_of_le hv.1 with h | h
    · subst h; norm_num
    · have := mul_pos hx (pow_pos h 2)
      linarith
  have hk : ∀ v ∈ uIcc (0 : ℝ) 1, 0 < 1 - v ^ 2 + y * v ^ 2 := by
    intro v hv
    have := hh v hv
    nlinarith [sq_nonneg v]
  set F : ℝ → ℝ := fun v => Real.arctan (c * v / Real.sqrt (1 - v ^ 2 + x * v ^ 2)) / c
  have hF : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt F
      ((Real.sqrt (1 - v ^ 2 + x * v ^ 2))⁻¹ * (1 - v ^ 2 + y * v ^ 2)⁻¹) v := by
    intro v hv
    have h0 := hh v hv
    have hs0 : 0 < Real.sqrt (1 - v ^ 2 + x * v ^ 2) := Real.sqrt_pos.mpr h0
    have hs2 : Real.sqrt (1 - v ^ 2 + x * v ^ 2) ^ 2 = 1 - v ^ 2 + x * v ^ 2 := Real.sq_sqrt h0.le
    have hq : HasDerivAt (fun v : ℝ => 1 - v ^ 2 + x * v ^ 2) (-(2 * v) + x * (2 * v)) v := by
      have := ((hasDerivAt_pow 2 v).const_sub 1).fun_add ((hasDerivAt_pow 2 v).const_mul x)
      convert this using 1
      push_cast; ring
    have hs := hq.sqrt h0.ne'
    have hg := (((hasDerivAt_id v).const_mul c).fun_div hs hs0.ne').arctan
    have := hg.div_const c
    refine this.congr_deriv ?_
    have hk0 := hk v hv
    simp only [id]
    generalize Real.sqrt (1 - v ^ 2 + x * v ^ 2) = s at hs0 hs2 ⊢
    have hs0' : s ≠ 0 := hs0.ne'
    have hk0' : 1 - v ^ 2 + y * v ^ 2 ≠ 0 := hk0.ne'
    have hA : s ^ 2 + c ^ 2 * v ^ 2 = 1 - v ^ 2 + y * v ^ 2 := by rw [hs2, hc2]; ring
    have hA' : s ^ 2 + c ^ 2 * v ^ 2 ≠ 0 := by rw [hA]; exact hk0'
    field_simp
    rw [show s ^ 2 + c ^ 2 * v ^ 2 = 1 - v ^ 2 + v ^ 2 * y by rw [hA]; ring,
      div_self (by rw [show 1 - v ^ 2 + v ^ 2 * y = 1 - v ^ 2 + y * v ^ 2 by ring]; exact hk0')]
    linear_combination hs2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF]
  · simp [F, Real.sqrt_one]
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul ?_ ?_
    · exact ContinuousOn.inv₀ (by fun_prop) fun v hv => (Real.sqrt_pos.mpr (hh v hv)).ne'
    · exact ContinuousOn.inv₀ (by fun_prop) fun v hv => (hk v hv).ne'


/-- For positive real nodes, `R_C(x, y) = ∫₀¹ (1 - v² + x v²)^{-1/2} (1 - v² + y v²)^{-1} dv`. -/
theorem carlsonRC_eq_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    carlsonRC x y = ((∫ v in (0 : ℝ)..1,
      (Real.sqrt (1 - v ^ 2 + x * v ^ 2))⁻¹ * (1 - v ^ 2 + y * v ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hz : pair (x : ℂ) (y : ℂ) ∈ Carlson.carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr hx
    · exact ofReal_mem_slitPlane.mpr hy
  have hsum : ∑ i, pair (1 / 2 : ℂ) 1 i = 3 / 2 := by simp [pair, Fin.sum_univ_two]; norm_num
  unfold carlsonRC carlsonR
  rw [hsum, regCarlsonR_eq_unitIntervalIntegral (by norm_num) (by rw [hsum]; norm_num) hz, hsum,
    Carlson.carlsonRUnitIntervalIntegral]
  norm_num
  -- the real integrand
  set f : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ)) * ((1 - u + u * x) ^ (-(1 / 2 : ℝ)) *
    (1 - u + u * y)⁻¹)
  have hint : ∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ (-(1 / 2 : ℂ)) *
      ((1 - (u : ℂ) + u * x) ^ (-(1 / 2 : ℂ)) * (1 - (u : ℂ) + u * y) ^ (-1 : ℂ)) =
      ((∫ u in Ioo (0 : ℝ) 1, f u : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have h1 : 0 < 1 - u + u * x := by nlinarith [hu.1, hu.2]
    have h2 : 0 < 1 - u + u * y := by nlinarith [hu.1, hu.2]
    simp only [f]
    rw [show (1 - (u : ℂ) + u * x) = ((1 - u + u * x : ℝ) : ℂ) by push_cast; ring,
      show (1 - (u : ℂ) + u * y) = ((1 - u + u * y : ℝ) : ℂ) by push_cast; ring,
      show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow hu.1.le, ← ofReal_cpow h1.le, show (-(1 : ℂ)) = ((-1 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow h2.le, Real.rpow_neg_one]
    push_cast; ring
  rw [hint, show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  have hG : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  rw [show (1 / 2 : ℂ) * Gamma (1 / 2) * ((Gamma (1 / 2))⁻¹ * ((∫ u in Ioo (0 : ℝ) 1, f u : ℝ) : ℂ)) =
      (((1 / 2) * ∫ u in Ioo (0 : ℝ) 1, f u : ℝ) : ℂ) by field_simp; push_cast; ring]
  congr 1
  -- the substitution `u = v²`
  have himage : (fun v : ℝ => v ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
    ext u; constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨by nlinarith [hv.1], by nlinarith [hv.1, hv.2]⟩
    · intro hu
      refine ⟨Real.sqrt u, ⟨Real.sqrt_pos.mpr hu.1, ?_⟩, Real.sq_sqrt hu.1.le⟩
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt hu.1.le hu.2
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := Ioo (0 : ℝ) 1)
    (f := fun v : ℝ => v ^ 2) (f' := fun v => 2 * v) measurableSet_Ioo
    (fun v _ => by simpa using (hasDerivAt_pow 2 v).hasDerivWithinAt)
    (fun a ha b hb h => by
      simp only at h
      nlinarith [ha.1, hb.1, sq_nonneg (a - b), sq_nonneg (a + b)]) f
  rw [himage] at hcv
  rw [hcv, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  have h1 : 0 < 1 - v ^ 2 + x * v ^ 2 := by nlinarith [hv.1, hv.2, sq_nonneg v]
  simp only [f, smul_eq_mul, abs_of_pos (by linarith [hv.1] : (0 : ℝ) < 2 * v)]
  have hsq : (v ^ 2) ^ (-(1 / 2 : ℝ)) = v⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hv.1.le]
  have hsq2 : (1 - v ^ 2 + v ^ 2 * x) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (1 - v ^ 2 + x * v ^ 2))⁻¹ := by
    rw [Real.rpow_neg (by nlinarith), ← Real.sqrt_eq_rpow]; ring_nf
  rw [hsq, hsq2]
  have hv0 : v ≠ 0 := hv.1.ne'
  field_simp


/-- The real integral behind `R_C` for `0 < y < x`:
`∫₀¹ (1 - v² + x v²)^{-1/2} (1 - v² + y v²)^{-1} dv = log((√x + √(x-y)) / √y) / √(x-y)`. -/
theorem integral_carlsonRC_of_gt {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    ∫ v in (0 : ℝ)..1, (Real.sqrt (1 - v ^ 2 + x * v ^ 2))⁻¹ * (1 - v ^ 2 + y * v ^ 2)⁻¹ =
      Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt y) / Real.sqrt (x - y) := by
  set c := Real.sqrt (x - y)
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hc2 : c ^ 2 = x - y := Real.sq_sqrt (by linarith)
  have hk : ∀ v ∈ uIcc (0 : ℝ) 1, 0 < 1 - v ^ 2 + y * v ^ 2 := by
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    have h1 : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    rcases eq_or_lt_of_le hv.1 with h | h
    · subst h; norm_num
    · have := mul_pos hy (pow_pos h 2)
      linarith
  have hh : ∀ v ∈ uIcc (0 : ℝ) 1, 0 < 1 - v ^ 2 + x * v ^ 2 := by
    intro v hv
    have := hk v hv
    nlinarith [sq_nonneg v]
  -- `s - c v > 0`
  have hsc : ∀ v ∈ uIcc (0 : ℝ) 1, c * v < Real.sqrt (1 - v ^ 2 + x * v ^ 2) := by
    intro v hv
    have h0 := hh v hv
    have hs2 : Real.sqrt (1 - v ^ 2 + x * v ^ 2) ^ 2 = 1 - v ^ 2 + x * v ^ 2 := Real.sq_sqrt h0.le
    have hs0 : 0 < Real.sqrt (1 - v ^ 2 + x * v ^ 2) := Real.sqrt_pos.mpr h0
    have hkv := hk v hv
    rw [uIcc_of_le zero_le_one] at hv
    have hcv : 0 ≤ c * v := mul_nonneg hc.le hv.1
    nlinarith [sq_nonneg (Real.sqrt (1 - v ^ 2 + x * v ^ 2) - c * v)]
  set F : ℝ → ℝ := fun v => (Real.log (Real.sqrt (1 - v ^ 2 + x * v ^ 2) + c * v) -
    Real.log (Real.sqrt (1 - v ^ 2 + x * v ^ 2) - c * v)) / (2 * c)
  have hF : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt F
      ((Real.sqrt (1 - v ^ 2 + x * v ^ 2))⁻¹ * (1 - v ^ 2 + y * v ^ 2)⁻¹) v := by
    intro v hv
    have h0 := hh v hv
    have hs0 : 0 < Real.sqrt (1 - v ^ 2 + x * v ^ 2) := Real.sqrt_pos.mpr h0
    have hs2 : Real.sqrt (1 - v ^ 2 + x * v ^ 2) ^ 2 = 1 - v ^ 2 + x * v ^ 2 := Real.sq_sqrt h0.le
    have hq : HasDerivAt (fun v : ℝ => 1 - v ^ 2 + x * v ^ 2) (-(2 * v) + x * (2 * v)) v := by
      have := ((hasDerivAt_pow 2 v).const_sub 1).fun_add ((hasDerivAt_pow 2 v).const_mul x)
      convert this using 1
      push_cast; ring
    have hs := hq.sqrt h0.ne'
    have hm := hsc v hv
    have hp : 0 < Real.sqrt (1 - v ^ 2 + x * v ^ 2) + c * v := by
      rw [uIcc_of_le zero_le_one] at hv; nlinarith [hv.1]
    have hn : 0 < Real.sqrt (1 - v ^ 2 + x * v ^ 2) - c * v := by linarith
    have h1 := (hs.fun_add ((hasDerivAt_id v).const_mul c)).log hp.ne'
    have h2 := (hs.fun_sub ((hasDerivAt_id v).const_mul c)).log hn.ne'
    have := (h1.fun_sub h2).div_const (2 * c)
    refine this.congr_deriv ?_
    have hkv := hk v hv
    simp only [id]
    generalize Real.sqrt (1 - v ^ 2 + x * v ^ 2) = s at hs0 hs2 hp hn hm ⊢
    have hA : (s + c * v) * (s - c * v) = 1 - v ^ 2 + y * v ^ 2 := by
      nlinarith [hs2, hc2]
    have hk0 : 1 - v ^ 2 + y * v ^ 2 ≠ 0 := hkv.ne'
    have hpn : s + c * v ≠ 0 := hp.ne'
    have hnn : s - c * v ≠ 0 := hn.ne'
    have hc0 : c ≠ 0 := hc.ne'
    field_simp
    have hpn' : s + v * c ≠ 0 := by rw [mul_comm]; exact hpn
    have hnn' : s - v * c ≠ 0 := by rw [mul_comm]; exact hnn
    have hk' : 1 - v ^ 2 + v ^ 2 * y ≠ 0 := by rw [mul_comm (v ^ 2)]; exact hk0
    rw [div_sub_div _ _ hpn' hnn', div_eq_div_iff (mul_ne_zero hpn' hnn') hk']
    linear_combination (2 * c * (-v ^ 2 + v ^ 2 * y)) * hs2 + (2 * c * v ^ 2) * hc2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF]
  · simp only [F]
    norm_num
    have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
    have hsy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    have hsy0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have hcx : c < Real.sqrt x := by
      rw [show c = Real.sqrt (x - y) from rfl]
      exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have hp : 0 < Real.sqrt x + c := by linarith
    have hn : 0 < Real.sqrt x - c := by linarith
    have hprod : Real.sqrt x - c = Real.sqrt y ^ 2 / (Real.sqrt x + c) := by
      rw [eq_div_iff hp.ne']; nlinarith [hsx, hsy, hc2]
    rw [hprod, Real.log_div (by positivity) hp.ne', Real.log_div hp.ne' hsy0.ne',
      Real.log_pow]
    field_simp
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul ?_ ?_
    · exact ContinuousOn.inv₀ (by fun_prop) fun v hv => (Real.sqrt_pos.mpr (hh v hv)).ne'
    · exact ContinuousOn.inv₀ (by fun_prop) fun v hv => (hk v hv).ne'


/-- **Formula (6.9-15)**: `R_C(x, y) = (y - x)^{-1/2} arccos (x/y)^{1/2}` for `0 < x < y`. -/
theorem carlsonRC_of_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    carlsonRC x y = ((Real.arccos (Real.sqrt (x / y)) / Real.sqrt (y - x) : ℝ) : ℂ) := by
  have hy : 0 < y := hx.trans hxy
  rw [carlsonRC_eq_integral hx hy, integral_carlsonRC_of_lt hx hxy]
  congr 2
  have hz : 0 < Real.sqrt (x / y) := Real.sqrt_pos.mpr (div_pos hx hy)
  rw [Real.arccos_eq_arctan hz]
  congr 1
  have h1 : 1 - Real.sqrt (x / y) ^ 2 = (y - x) / y := by
    rw [Real.sq_sqrt (div_pos hx hy).le]; field_simp
  rw [h1, Real.sqrt_div' _ hy.le, Real.sqrt_div' _ hy.le]
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  field_simp

/-- **Formula (6.9-16)**: `R_C(x, y) = (x - y)^{-1/2} log ((x^{1/2} + (x - y)^{1/2}) / y^{1/2})`
for `0 < y < x`. -/
theorem carlsonRC_of_gt {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    carlsonRC x y =
      ((Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt y) / Real.sqrt (x - y) : ℝ) : ℂ) := by
  rw [carlsonRC_eq_integral (hy.trans hyx) hy, integral_carlsonRC_of_gt hy hyx]

/-- `arcsin x = x R_C(1 - x², 1)` for `0 < x < 1` (Carlson (6.9-15)). -/
theorem arcsin_eq_mul_carlsonRC {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (Real.arcsin x : ℂ) = x * carlsonRC (1 - x ^ 2 : ℝ) 1 := by
  have h1 : 0 < 1 - x ^ 2 := by nlinarith
  have h2 : 1 - x ^ 2 < 1 := by nlinarith
  rw [show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by simp, carlsonRC_of_lt h1 h2]
  rw [show (1 : ℝ) - (1 - x ^ 2) = x ^ 2 by ring, Real.sqrt_sq hx.le, div_one,
    Real.arccos_eq_arcsin (Real.sqrt_nonneg _), Real.sq_sqrt h1.le,
    show 1 - (1 - x ^ 2) = x ^ 2 by ring, Real.sqrt_sq hx.le]
  have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

/-- `log x = (x - 1) R_C(((x + 1)/2)², x)` for `x > 1` (Carlson (6.9-16)). -/
theorem log_eq_mul_carlsonRC {x : ℝ} (hx : 1 < x) :
    (Real.log x : ℂ) = (x - 1) * carlsonRC (((x + 1) / 2) ^ 2 : ℝ) x := by
  have hx0 : 0 < x := by linarith
  have hlt : x < ((x + 1) / 2) ^ 2 := by nlinarith
  rw [carlsonRC_of_gt hx0 hlt]
  rw [Real.sqrt_sq (by linarith), show ((x + 1) / 2) ^ 2 - x = ((x - 1) / 2) ^ 2 by ring,
    Real.sqrt_sq (by linarith), show (x + 1) / 2 + (x - 1) / 2 = x by ring]
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlog : Real.log (x / Real.sqrt x) = Real.log x / 2 := by
    rw [Real.log_div hx0.ne' hsx.ne', Real.log_sqrt hx0.le]; ring
  rw [hlog]
  have : (x : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hx.ne'
  push_cast
  field_simp

end Carlson.TwoVariable
