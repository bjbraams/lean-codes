/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.LandenExercises
public import Carlson.Elliptic.LandenAlgorithm

/-!
# `R_E` along the arithmetic-geometric mean (Carlson's Exercises 9.5-3 and 9.5-4)

Along Gauss's AGM sequence `x_{n+1} = (xₙ + yₙ)/2`, `y_{n+1} = (xₙ yₙ)^{1/2}` (Example 6.10-2),
`R_K(xₙ², yₙ²) = 1/M` is constant, and the Landen transformation of `R_E` (Exercise 9.5-2) gives
the recursion for `A(n) = 2^{n+1} [R_E(xₙ², yₙ²) - xₙ² R_K(xₙ², yₙ²)]`. Homogeneity writes `A(n)`
as `2^{n+1} xₙ g(yₙ/xₙ)` with `g(s) = R_E(1, s²) - R_K(1, s²)` analytic and `g(1) = 0`; the
quadratic convergence `|x_{n+1} - y_{n+1}| ≤ |xₙ - yₙ|²/(8 min(x, y))` then gives `A(n) → 0`.

## Main results

* `Carlson.agmSeq`, `Carlson.agmSeq_gap_succ`: the AGM sequence and its quadratic convergence.
* `Carlson.agmA_sub_agmA_succ`, `Carlson.tendsto_agmA`, `Carlson.hasSum_agmA_zero`:
  Exercise 9.5-3.
* `Carlson.carlsonRE_eq_agm`, `Carlson.carlsonRE_eq_agm_div`: Exercise 9.5-4,
  `R_E(x², y²) = B/M`.
* `Carlson.tendsto_descGauss_self`: Algorithm 9.5-3 in the boundary case `t₀ = a₀`, where it
  reduces to Gauss's `R_K(a₀² - c₀², a₀²) = 1/M`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §9.5.
-/

open Complex Filter
open scoped Real Topology

@[expose] public noncomputable section

namespace Carlson

open TwoVariable (pair carlsonRK carlsonRK_sq_eq)

/-- One step of Gauss's arithmetic-geometric mean, `(x, y) ↦ ((x + y)/2, √(xy))`. -/
def agmStep (p : ℝ × ℝ) : ℝ × ℝ := ((p.1 + p.2) / 2, Real.sqrt (p.1 * p.2))

/-- The arithmetic-geometric mean sequence `(xₙ, yₙ)` of Example 6.10-2. -/
def agmSeq (x y : ℝ) (n : ℕ) : ℝ × ℝ := agmStep^[n] (x, y)

theorem agmSeq_zero (x y : ℝ) : agmSeq x y 0 = (x, y) := rfl

theorem agmSeq_succ (x y : ℝ) (n : ℕ) : agmSeq x y (n + 1) = agmStep (agmSeq x y n) := by
  simp only [agmSeq, Function.iterate_succ_apply']

section Bounds

variable {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
include hx hy

/-- Both members of the AGM sequence stay above `min x y`. -/
theorem min_le_agmSeq (n : ℕ) :
    min x y ≤ (agmSeq x y n).1 ∧ min x y ≤ (agmSeq x y n).2 := by
  induction n with
  | zero => exact ⟨min_le_left _ _, min_le_right _ _⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hm : 0 < min x y := lt_min hx hy
    rw [agmSeq_succ]
    refine ⟨by simp only [agmStep]; linarith, ?_⟩
    simp only [agmStep]
    rw [show min x y = Real.sqrt (min x y * min x y) by
      rw [Real.sqrt_mul_self hm.le]]
    exact Real.sqrt_le_sqrt (mul_le_mul h1 h2 hm.le (hm.le.trans h1))

/-- Both members of the AGM sequence stay below `max x y`. -/
theorem agmSeq_le_max (n : ℕ) :
    (agmSeq x y n).1 ≤ max x y ∧ (agmSeq x y n).2 ≤ max x y := by
  induction n with
  | zero => exact ⟨le_max_left _ _, le_max_right _ _⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨p1, p2⟩ := min_le_agmSeq hx hy n
    have hm : 0 < min x y := lt_min hx hy
    rw [agmSeq_succ]
    refine ⟨by simp only [agmStep]; linarith, ?_⟩
    simp only [agmStep]
    rw [show max x y = Real.sqrt (max x y * max x y) by
      rw [Real.sqrt_mul_self (hm.le.trans (min_le_max))]]
    exact Real.sqrt_le_sqrt (mul_le_mul h1 h2 (hm.le.trans p2) (hm.le.trans (min_le_max)))

/-- The AGM sequence is positive. -/
theorem agmSeq_pos (n : ℕ) : 0 < (agmSeq x y n).1 ∧ 0 < (agmSeq x y n).2 := by
  have hm : 0 < min x y := lt_min hx hy
  obtain ⟨h1, h2⟩ := min_le_agmSeq hx hy n
  exact ⟨hm.trans_le h1, hm.trans_le h2⟩

/-- The squared geometric mean: `y_{n+1}² = xₙ yₙ`. -/
theorem agmSeq_succ_snd_sq (n : ℕ) :
    (agmSeq x y (n + 1)).2 ^ 2 = (agmSeq x y n).1 * (agmSeq x y n).2 := by
  obtain ⟨h1, h2⟩ := agmSeq_pos hx hy n
  rw [agmSeq_succ]; simp only [agmStep]
  rw [Real.sq_sqrt (by positivity)]

/-- The gap `|xₙ - yₙ|` contracts quadratically:
`|x_{n+1} - y_{n+1}| ≤ |xₙ - yₙ|²/(8 m)` and `≤ |xₙ - yₙ|/2`, with `m = min x y`. -/
theorem agmSeq_gap_succ (n : ℕ) :
    |(agmSeq x y (n + 1)).1 - (agmSeq x y (n + 1)).2| ≤
        |(agmSeq x y n).1 - (agmSeq x y n).2| ^ 2 / (8 * min x y) ∧
      |(agmSeq x y (n + 1)).1 - (agmSeq x y (n + 1)).2| ≤
        |(agmSeq x y n).1 - (agmSeq x y n).2| / 2 := by
  obtain ⟨h1, h2⟩ := agmSeq_pos hx hy n
  obtain ⟨m1, m2⟩ := min_le_agmSeq hx hy n
  have hm : 0 < min x y := lt_min hx hy
  set a := (agmSeq x y n).1
  set b := (agmSeq x y n).2
  set ra := Real.sqrt a
  set rb := Real.sqrt b
  have hra : ra ^ 2 = a := Real.sq_sqrt h1.le
  have hrb : rb ^ 2 = b := Real.sq_sqrt h2.le
  have hra0 : 0 < ra := Real.sqrt_pos.mpr h1
  have hrb0 : 0 < rb := Real.sqrt_pos.mpr h2
  have hgap : (agmSeq x y (n + 1)).1 - (agmSeq x y (n + 1)).2 = (ra - rb) ^ 2 / 2 := by
    rw [agmSeq_succ]; simp only [agmStep]
    rw [Real.sqrt_mul h1.le]
    change (a + b) / 2 - ra * rb = (ra - rb) ^ 2 / 2
    nlinarith [hra, hrb]
  have hd : |a - b| = |ra - rb| * (ra + rb) := by
    rw [show a - b = (ra - rb) * (ra + rb) by nlinarith [hra, hrb], abs_mul,
      abs_of_pos (by positivity : 0 < ra + rb)]
  rw [hgap, abs_of_nonneg (by positivity)]
  have hsum : 4 * min x y ≤ (ra + rb) ^ 2 := by nlinarith [hra, hrb, sq_nonneg (ra - rb)]
  have hsq : (ra - rb) ^ 2 = |ra - rb| ^ 2 := (sq_abs _).symm
  constructor
  · rw [hd, hsq, mul_pow, div_le_div_iff₀ (by norm_num) (by positivity)]
    have := sq_nonneg |ra - rb|
    nlinarith
  · rw [hd, hsq]
    have h0 := abs_nonneg (ra - rb)
    have hle : |ra - rb| ≤ ra + rb := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [mul_le_mul_of_nonneg_left hle h0]

/-- `2ⁿ |xₙ - yₙ| ≤ C 2^{-n}`; in particular `2ⁿ |xₙ - yₙ| → 0`. -/
theorem two_pow_mul_agmSeq_gap_le (n : ℕ) :
    2 ^ (n + 1) * |(agmSeq x y (n + 1)).1 - (agmSeq x y (n + 1)).2| ≤
      |x - y| ^ 2 / (4 * min x y) * (1 / 2) ^ n := by
  have hm : 0 < min x y := lt_min hx hy
  have hlin : ∀ k, |(agmSeq x y k).1 - (agmSeq x y k).2| ≤ |x - y| / 2 ^ k := by
    intro k
    induction k with
    | zero => simp [agmSeq_zero]
    | succ k ih =>
      calc _ ≤ |(agmSeq x y k).1 - (agmSeq x y k).2| / 2 := (agmSeq_gap_succ hx hy k).2
        _ ≤ |x - y| / 2 ^ k / 2 := by gcongr
        _ = _ := by rw [pow_succ]; ring
  have h := (agmSeq_gap_succ hx hy n).1
  have hk := hlin n
  have h0 := abs_nonneg ((agmSeq x y n).1 - (agmSeq x y n).2)
  calc 2 ^ (n + 1) * |(agmSeq x y (n + 1)).1 - (agmSeq x y (n + 1)).2|
      ≤ 2 ^ (n + 1) * (|(agmSeq x y n).1 - (agmSeq x y n).2| ^ 2 / (8 * min x y)) := by gcongr
    _ ≤ 2 ^ (n + 1) * ((|x - y| / 2 ^ n) ^ 2 / (8 * min x y)) := by gcongr
    _ = _ := by
      rw [one_div_pow, pow_succ]
      field_simp
      ring

end Bounds

section Second

variable {x y : ℝ} (hx : 0 < x) (hy : 0 < y)

/-- The AGM member `xₙ`, as a complex number. -/
abbrev agmX (x y : ℝ) (n : ℕ) : ℂ := ((agmSeq x y n).1 : ℂ)

/-- The AGM member `yₙ`, as a complex number. -/
abbrev agmY (x y : ℝ) (n : ℕ) : ℂ := ((agmSeq x y n).2 : ℂ)

include hx hy

omit hx hy in
private theorem X_succ (n : ℕ) : agmX x y (n + 1) = (agmX x y n + agmY x y n) / 2 := by
  simp only [agmX, agmY, agmSeq_succ, agmStep]; push_cast; ring

private theorem Y_succ_sq (n : ℕ) : agmY x y (n + 1) ^ 2 = agmX x y n * agmY x y n := by
  simp only [agmX, agmY]; exact_mod_cast agmSeq_succ_snd_sq hx hy n

private theorem X_re_pos (n : ℕ) : 0 < (agmX x y n).re := by simpa using (agmSeq_pos hx hy n).1
private theorem Y_re_pos (n : ℕ) : 0 < (agmY x y n).re := by simpa using (agmSeq_pos hx hy n).2

/-- `R_K(xₙ², yₙ²)` does not depend on `n` (Example 6.10-2). -/
theorem carlsonRK_agmSeq (n : ℕ) :
    carlsonRK (agmX x y n ^ 2) (agmY x y n ^ 2) = carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) := by
  induction n with
  | zero => simp [agmX, agmY, agmSeq_zero]
  | succ n ih =>
    rw [← ih, carlsonRK_sq_eq _ _ (X_re_pos hx hy n) (Y_re_pos hx hy n), X_succ,
      Y_succ_sq hx hy]

/-- Carlson's `A(n) = 2^{n+1} [R_E(xₙ², yₙ²) - xₙ² R_K(xₙ², yₙ²)]` of Exercise 9.5-3. -/
def agmA (x y : ℝ) (n : ℕ) : ℂ :=
  2 ^ (n + 1) * (carlsonRE (agmX x y n ^ 2) (agmY x y n ^ 2) -
    agmX x y n ^ 2 * carlsonRK (agmX x y n ^ 2) (agmY x y n ^ 2))

/-- **Exercise 9.5-3**, the recursion: `A(n) - A(n + 1) = 2ⁿ (yₙ² - xₙ²) R_K(x², y²)`, where
`R_K(x², y²) = 1/M` (`TwoVariable.carlsonRK_sq_eq_inv_agm`). -/
theorem agmA_sub_agmA_succ (n : ℕ) :
    agmA x y n - agmA x y (n + 1) =
      2 ^ n * (agmY x y n ^ 2 - agmX x y n ^ 2) * carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) := by
  have hE := carlsonRE_sq_eq (X_re_pos hx hy n) (Y_re_pos hx hy n)
  unfold agmA
  rw [carlsonRK_agmSeq hx hy (n + 1), carlsonRK_agmSeq hx hy n, X_succ, Y_succ_sq hx hy, hE,
    carlsonRK_agmSeq hx hy n, pow_succ]
  ring

omit hx hy in
/-- The function `g(s) = R_E(1, s²) - R_K(1, s²)`, which vanishes at `s = 1`. -/
private def agmG (s : ℂ) : ℂ := carlsonRE 1 (s ^ 2) - carlsonRK 1 (s ^ 2)

omit hx hy in
private theorem agmG_one : agmG 1 = 0 := by
  have hb : ∀ i, 0 < ((pair (1 / 2 : ℂ) (1 / 2)) i).re := by
    intro i; fin_cases i <;> norm_num [pair]
  simp only [agmG, one_pow, carlsonRE, carlsonRK,
    TwoVariable.carlsonR_pair_self _ hb one_mem_slitPlane, one_cpow, sub_self]

omit hx hy in
private theorem isBigO_agmG : agmG =O[𝓝 1] fun s => s - 1 := by
  have hz : ∀ s : ℂ, (s ^ 2) ∈ slitPlane → pair (1 : ℂ) (s ^ 2) ∈ carlsonRSlitDomain :=
    fun s hs i => by fin_cases i
                     · exact one_mem_slitPlane
                     · exact hs
  have hpair : AnalyticAt ℂ (fun s : ℂ => pair (1 : ℂ) (s ^ 2)) 1 := by
    rw [analyticAt_pi_iff]; intro i; fin_cases i
    · exact analyticAt_const
    · exact (analyticAt_id.pow 2)
  have h1 : (1 : ℂ) ^ 2 ∈ slitPlane := by simp
  have hE : AnalyticAt ℂ (fun s : ℂ => carlsonRE 1 (s ^ 2)) 1 := by
    have := analyticAt_regCarlsonR_comp (t := fun _ : ℂ => (1 / 2 : ℂ))
      (b := fun _ : ℂ => pair (1 / 2 : ℂ) (1 / 2)) analyticAt_const analyticAt_const hpair (hz 1 h1)
    exact (analyticAt_const.mul this).congr (Eventually.of_forall fun s => rfl)
  have hK : AnalyticAt ℂ (fun s : ℂ => carlsonRK 1 (s ^ 2)) 1 := by
    have := analyticAt_regCarlsonR_comp (t := fun _ : ℂ => (-1 / 2 : ℂ))
      (b := fun _ : ℂ => pair (1 / 2 : ℂ) (1 / 2)) analyticAt_const analyticAt_const hpair (hz 1 h1)
    exact (analyticAt_const.mul this).congr (Eventually.of_forall fun s => rfl)
  have hd := (hE.sub hK).differentiableAt.hasFDerivAt.isBigO_sub
  have h0 : carlsonRE 1 ((1 : ℂ) ^ 2) - carlsonRK 1 ((1 : ℂ) ^ 2) = 0 := agmG_one
  refine hd.congr_left fun s => ?_
  simp only [Pi.sub_apply]
  rw [h0, sub_zero]; rfl

omit hx hy in
/-- Homogeneity: `R_E(a², b²) - a² R_K(a², b²) = a g(b/a)` for real `a, b > 0`. -/
private theorem carlsonRE_sub_carlsonRK_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    carlsonRE ((a : ℂ) ^ 2) ((b : ℂ) ^ 2) - (a : ℂ) ^ 2 * carlsonRK ((a : ℂ) ^ 2) ((b : ℂ) ^ 2) =
      a * agmG ((b / a : ℝ) : ℂ) := by
  have hl : 0 < a ^ 2 := by positivity
  have hs1 : ((b / a : ℝ) : ℂ) ^ 2 ∈ slitPlane := by
    rw [← ofReal_pow]; exact ofReal_mem_slitPlane.mpr (by positivity)
  have hs : pair (1 : ℂ) (((b / a : ℝ) : ℂ) ^ 2) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact one_mem_slitPlane
    · exact hs1
  have hsc : ∀ i, ((a ^ 2 : ℝ) : ℂ) * pair (1 : ℂ) (((b / a : ℝ) : ℂ) ^ 2) i =
      pair ((a : ℂ) ^ 2) ((b : ℂ) ^ 2) i := by
    have : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
    intro i; fin_cases i <;> (simp [pair]; try field_simp)
  have hE := carlsonR_smul_of_pos (1 / 2) (pair (1 / 2) (1 / 2)) hl hs
  have hK := carlsonR_smul_of_pos (-1 / 2) (pair (1 / 2) (1 / 2)) hl hs
  simp only [hsc] at hE hK
  have hpE : ((a ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = a := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hl.le,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq ha.le]
  have hpK : ((a ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = (a : ℂ)⁻¹ := by
    rw [ofReal_cpow_neg_half hl, Real.sqrt_sq ha.le, ofReal_inv]
  rw [hpE] at hE
  rw [hpK] at hK
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  unfold agmG carlsonRE carlsonRK
  rw [show (fun i => pair ((a : ℂ) ^ 2) ((b : ℂ) ^ 2) i) =
      pair ((a : ℂ) ^ 2) ((b : ℂ) ^ 2) from rfl]
    at hE hK
  rw [hE, hK]
  field_simp

/-- **Exercise 9.5-3**: `A(n) → 0` as `n → ∞`. -/
theorem tendsto_agmA : Tendsto (agmA x y) atTop (𝓝 0) := by
  have hm : 0 < min x y := lt_min hx hy
  obtain ⟨C, hC⟩ := isBigO_agmG.bound
  set gap : ℕ → ℝ := fun n => |(agmSeq x y n).1 - (agmSeq x y n).2|
  -- `2^{n+1} gap n → 0`
  have hgap : Tendsto (fun n => 2 ^ (n + 1) * gap n) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have hb : Tendsto (fun n : ℕ => 2 * (|x - y| ^ 2 / (4 * min x y) * (1 / 2 : ℝ) ^ n)) atTop
        (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (|x - y| ^ 2 / (4 * min x y))).const_mul 2
      simpa only [mul_zero] using this
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hb
    have := two_pow_mul_agmSeq_gap_le hx hy n
    calc 2 ^ (n + 1 + 1) * gap (n + 1) = 2 * (2 ^ (n + 1) * gap (n + 1)) := by ring
      _ ≤ _ := by gcongr
  -- the ratio `yₙ/xₙ → 1`
  have hratio : Tendsto (fun n => (((agmSeq x y n).2 / (agmSeq x y n).1 : ℝ) : ℂ)) atTop (𝓝 1) := by
    have hg0 : Tendsto gap atTop (𝓝 0) := by
      refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) hgap
      have : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
      simp only [gap]; nlinarith [abs_nonneg ((agmSeq x y n).1 - (agmSeq x y n).2)]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa only [zero_div] using hg0.div_const (min x y))
    obtain ⟨h1, h2⟩ := agmSeq_pos hx hy n
    obtain ⟨m1, -⟩ := min_le_agmSeq hx hy n
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      show (agmSeq x y n).2 / (agmSeq x y n).1 - 1 =
        -((agmSeq x y n).1 - (agmSeq x y n).2) / (agmSeq x y n).1 by field_simp; ring,
      abs_div, abs_neg, abs_of_pos h1]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hm m1
  have hev := hratio.eventually hC
  refine squeeze_zero_norm' ?_ (by simpa using hgap.const_mul C)
  filter_upwards [hev] with n hn
  obtain ⟨h1, h2⟩ := agmSeq_pos hx hy n
  have hA : agmA x y n = 2 ^ (n + 1) * ((agmSeq x y n).1 *
      agmG (((agmSeq x y n).2 / (agmSeq x y n).1 : ℝ) : ℂ)) := by
    rw [agmA, carlsonRE_sub_carlsonRK_eq h1 h2]
  rw [hA, norm_mul, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg h1.le]
  have hn' : ‖agmG (((agmSeq x y n).2 / (agmSeq x y n).1 : ℝ) : ℂ)‖ ≤
      C * (gap n / (agmSeq x y n).1) := by
    refine hn.trans (le_of_eq ?_)
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      show (agmSeq x y n).2 / (agmSeq x y n).1 - 1 =
        -((agmSeq x y n).1 - (agmSeq x y n).2) / (agmSeq x y n).1 by field_simp; ring,
      abs_div, abs_neg, abs_of_pos h1]
  calc ‖(2 : ℂ)‖ ^ (n + 1) * ((agmSeq x y n).1 *
        ‖agmG (((agmSeq x y n).2 / (agmSeq x y n).1 : ℝ) : ℂ)‖)
      ≤ 2 ^ (n + 1) * ((agmSeq x y n).1 * (C * (gap n / (agmSeq x y n).1))) := by
        rw [Complex.norm_two]; gcongr
    _ = C * (2 ^ (n + 1) * gap n) := by have := h1.ne'; field_simp

/-- **Exercise 9.5-3**: `A(0) = ∑ₙ 2ⁿ (yₙ² - xₙ²) R_K(x², y²)`, with `R_K(x², y²) = 1/M`. -/
theorem hasSum_agmA_zero :
    HasSum (fun n => 2 ^ n * (agmY x y n ^ 2 - agmX x y n ^ 2) *
      carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)) (agmA x y 0) := by
  set f : ℕ → ℂ := fun n => 2 ^ n * (agmY x y n ^ 2 - agmX x y n ^ 2) *
    carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)
  have hm : 0 < min x y := lt_min hx hy
  -- summability from the quadratic convergence
  have hsum : Summable f := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_norm_bounded ((summable_geometric_two).mul_left
      (|x - y| ^ 2 / (4 * min x y) * (2 * max x y) * ‖carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)‖))
      fun n => ?_
    obtain ⟨u1, u2⟩ := agmSeq_le_max hx hy (n + 1)
    obtain ⟨p1, p2⟩ := agmSeq_pos hx hy (n + 1)
    have hb := two_pow_mul_agmSeq_gap_le hx hy n
    simp only [f, agmX, agmY, norm_mul, norm_pow, Complex.norm_two]
    rw [show ((agmSeq x y (n + 1)).2 : ℂ) ^ 2 - ((agmSeq x y (n + 1)).1 : ℂ) ^ 2 =
        (((agmSeq x y (n + 1)).2 - (agmSeq x y (n + 1)).1) *
          ((agmSeq x y (n + 1)).2 + (agmSeq x y (n + 1)).1) : ℝ) by push_cast; ring,
      norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith : 0 <
        (agmSeq x y (n + 1)).2 + (agmSeq x y (n + 1)).1), abs_sub_comm]
    have hK := norm_nonneg (carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2))
    have hg := abs_nonneg ((agmSeq x y (n + 1)).1 - (agmSeq x y (n + 1)).2)
    calc (2 : ℝ) ^ (n + 1) * (|(agmSeq x y (n + 1)).1 - (agmSeq x y (n + 1)).2| *
          ((agmSeq x y (n + 1)).2 + (agmSeq x y (n + 1)).1)) *
          ‖carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)‖
        = (2 ^ (n + 1) * |(agmSeq x y (n + 1)).1 - (agmSeq x y (n + 1)).2|) *
          ((agmSeq x y (n + 1)).2 + (agmSeq x y (n + 1)).1) *
          ‖carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)‖ := by ring
      _ ≤ (|x - y| ^ 2 / (4 * min x y) * (1 / 2) ^ n) * (2 * max x y) *
          ‖carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)‖ := by gcongr; linarith
      _ = _ := by ring
  -- the partial sums telescope
  have htel : ∀ N, ∑ n ∈ Finset.range N, f n = agmA x y 0 - agmA x y N := fun N => by
    rw [← Finset.sum_range_sub' (agmA x y)]
    exact Finset.sum_congr rfl fun n _ => (agmA_sub_agmA_succ hx hy n).symm
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (𝓝 (agmA x y 0)) := by
    simp_rw [htel]
    simpa using (tendsto_agmA hx hy).const_sub (agmA x y 0)
  rw [← tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim]
  exact hsum.hasSum

/-- **Exercise 9.5-4**: with `B = x₁² - ∑_{n ≥ 2} 2^{n-1} (xₙ² - yₙ²)`,
`R_E(x², y²) = B R_K(x², y²) = B/M`. -/
theorem carlsonRE_eq_agm :
    carlsonRE ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) =
      (agmX x y 1 ^ 2 - ∑' m, 2 ^ (m + 1) * (agmX x y (m + 2) ^ 2 - agmY x y (m + 2) ^ 2)) *
        carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) := by
  have h := hasSum_agmA_zero hx hy
  have h2 := (hasSum_nat_add_iff' 2).mpr h
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h2
  set K := carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2)
  have hK : K ≠ 0 := by
    have hinv := TwoVariable.carlsonRK_sq_eq_inv_agm (x := ⟨x, hx.le⟩) (y := ⟨y, hy.le⟩)
      (by exact_mod_cast hx) (by exact_mod_cast hy)
    have e : K = ((NNReal.agm ⟨x, hx.le⟩ ⟨y, hy.le⟩ : ℝ) : ℂ)⁻¹ := hinv
    rw [e]
    refine inv_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ?_))
    exact_mod_cast NNReal.agm_pos (by exact_mod_cast hx) (by exact_mod_cast hy)
  have hS : HasSum (fun m => 2 ^ (m + 1) * (agmX x y (m + 2) ^ 2 - agmY x y (m + 2) ^ 2))
      (-(agmA x y 0 - (2 ^ 0 * (agmY x y 0 ^ 2 - agmX x y 0 ^ 2) * K +
        2 ^ 1 * (agmY x y 1 ^ 2 - agmX x y 1 ^ 2) * K)) / (2 * K)) := by
    convert (h2.mul_right (-(1 / (2 * K)))) using 1
    · funext m; field_simp; ring_nf
    · field_simp
  rw [hS.tsum_eq]
  have hA : agmA x y 0 = 2 * (carlsonRE ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) - (x : ℂ) ^ 2 * K) := by
    simp [agmA, agmX, agmY, agmSeq_zero, K]
  have hX1 : agmX x y 1 = ((x : ℂ) + y) / 2 := by simp [agmX, agmSeq_succ, agmSeq_zero, agmStep]
  have hY1 : agmY x y 1 ^ 2 = (x : ℂ) * y := by
    have := Y_succ_sq hx hy 0
    simpa [agmX, agmY, agmSeq_zero] using this
  have hX0 : agmX x y 0 = x := by simp [agmX, agmSeq_zero]
  have hY0 : agmY x y 0 = y := by simp [agmY, agmSeq_zero]
  rw [hA, hX1, hY1, hX0, hY0]
  field_simp
  ring

/-- **Exercise 9.5-4** in Carlson's form `R_E(x², y²) = B/M`, with `M = M(x, y)` Gauss's
arithmetic-geometric mean. -/
theorem carlsonRE_eq_agm_div :
    carlsonRE ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) =
      (agmX x y 1 ^ 2 - ∑' m, 2 ^ (m + 1) * (agmX x y (m + 2) ^ 2 - agmY x y (m + 2) ^ 2)) /
        (NNReal.agm ⟨x, hx.le⟩ ⟨y, hy.le⟩ : ℝ) := by
  have hinv := TwoVariable.carlsonRK_sq_eq_inv_agm (x := ⟨x, hx.le⟩) (y := ⟨y, hy.le⟩)
    (by exact_mod_cast hx) (by exact_mod_cast hy)
  have e : carlsonRK ((x : ℂ) ^ 2) ((y : ℂ) ^ 2) =
      ((NNReal.agm ⟨x, hx.le⟩ ⟨y, hy.le⟩ : ℝ) : ℂ)⁻¹ := hinv
  rw [carlsonRE_eq_agm hx hy, e, div_eq_mul_inv]

end Second

/-! ### Algorithm 9.5-3 with `t₀ = a₀` -/

/-- **Carlson's Algorithm 9.5-3 with `t₀ = a₀`**: for `a₀ > c₀ > 0` the descending Gauss
transformations started at `t₀ = a₀` keep `tₙ = aₙ`, both tend to the same limit `T = M > 0`, and
`R_F(t₀² - a₀², t₀² - c₀², t₀²)`, whose first argument vanishes and which is therefore read as
`(π/2) R_K(a₀² - c₀², a₀²)` by (9.2-2), equals `(1/M) arcsin(M/T) = π/(2M)`. -/
theorem tendsto_descGauss_self {a₀ c₀ : ℝ} (hc : 0 < c₀) (hac : c₀ < a₀) :
    ∃ T M : ℝ, T = M ∧ 0 < M ∧ (∀ n, descGaussT a₀ a₀ c₀ n = (landenAC a₀ c₀ n).1) ∧
      Tendsto (descGaussT a₀ a₀ c₀) atTop (𝓝 T) ∧
      Tendsto (fun n => (landenAC a₀ c₀ n).1) atTop (𝓝 M) ∧
      (π / 2 : ℂ) * carlsonRK ((a₀ ^ 2 - c₀ ^ 2 : ℝ) : ℂ) ((a₀ ^ 2 : ℝ) : ℂ) =
        ((Real.arcsin (M / T) / M : ℝ) : ℂ) := by
  obtain ⟨M, hM, hMlim, hclim, -⟩ := landenAC_tendsto hc hac
  set a : ℕ → ℝ := fun n => (landenAC a₀ c₀ n).1
  set c : ℕ → ℝ := fun n => (landenAC a₀ c₀ n).2
  set b : ℕ → ℝ := fun n => √(a n ^ 2 - c n ^ 2)
  have hpos : ∀ n, 0 < c n ∧ c n < a n := fun n => landenAC_pos hc hac n
  have hsucc : ∀ n, landenAC a₀ c₀ (n + 1) = landenACStep (a n, c n) := fun n =>
    Function.iterate_succ_apply' _ _ _
  have ha_succ : ∀ n, a (n + 1) = (a n + b n) / 2 := fun n => by
    simp only [a, hsucc]; rfl
  have hb_pos : ∀ n, 0 < b n := fun n => by
    obtain ⟨h1, h2⟩ := hpos n
    exact Real.sqrt_pos.2 (by nlinarith)
  have hb_succ : ∀ n, b (n + 1) ^ 2 = a n * b n := fun n => by
    obtain ⟨h1, h2⟩ := hpos n
    have hab := landenACStep_b h1 h2
    have hnn : 0 ≤ a (n + 1) ^ 2 - c (n + 1) ^ 2 := by
      obtain ⟨h1', h2'⟩ := hpos (n + 1); nlinarith
    rw [Real.sq_sqrt hnn]
    simp only [a, c, hsucc]
    exact hab
  -- `tₙ = aₙ`
  have ht : ∀ n, descGaussT a₀ a₀ c₀ n = a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [descGaussT, ih, ha_succ]
  -- invariance of `R_K(aₙ², bₙ²)`
  have hre : ∀ {r : ℝ}, 0 < r → 0 < (r : ℂ).re := fun hr => by simpa using hr
  have hinv : ∀ n, carlsonRK ((a n : ℂ) ^ 2) ((b n : ℂ) ^ 2) =
      carlsonRK ((a 0 : ℂ) ^ 2) ((b 0 : ℂ) ^ 2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [← ih, carlsonRK_sq_eq _ _ (hre ((hpos n).1.trans (hpos n).2)) (hre (hb_pos n)), ha_succ,
        show (b (n + 1) : ℂ) ^ 2 = ((b (n + 1) ^ 2 : ℝ) : ℂ) by push_cast; ring, hb_succ]
      push_cast; ring_nf
  -- the limit
  have hblim : Tendsto b atTop (𝓝 M) := by
    have := ((hMlim.pow 2).sub (hclim.pow 2)).sqrt
    simpa [Real.sqrt_sq hM.le] using this
  have hM2 : ((M : ℂ) ^ 2) ∈ slitPlane := by
    rw [← ofReal_pow]; exact ofReal_mem_slitPlane.2 (by positivity)
  have hvec : Tendsto (fun n => pair ((a n : ℂ) ^ 2) ((b n : ℂ) ^ 2)) atTop
      (𝓝 (pair ((M : ℂ) ^ 2) ((M : ℂ) ^ 2))) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · simpa [pair] using ((continuous_ofReal.tendsto M).comp hMlim).pow 2
    · simpa [pair] using ((continuous_ofReal.tendsto M).comp hblim).pow 2
  have hlim := (TwoVariable.continuousAt_carlsonRK hM2 hM2).tendsto.comp hvec
  have hconst : carlsonRK ((a 0 : ℂ) ^ 2) ((b 0 : ℂ) ^ 2) = carlsonRK ((M : ℂ) ^ 2) ((M : ℂ) ^ 2) :=
    tendsto_nhds_unique tendsto_const_nhds (hlim.congr fun n => hinv n)
  rw [TwoVariable.carlsonRK_self hM2] at hconst
  have hM2' : ((M : ℂ) ^ 2) ^ (-1 / 2 : ℂ) = ((M⁻¹ : ℝ) : ℂ) := by
    rw [← ofReal_pow, show (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hM.le]
  rw [hM2'] at hconst
  refine ⟨M, M, rfl, hM, ht, ?_, hMlim, ?_⟩
  · exact hMlim.congr fun n => (ht n).symm
  · have hb0 : (b 0 : ℂ) ^ 2 = ((a₀ ^ 2 - c₀ ^ 2 : ℝ) : ℂ) := by
      rw [← ofReal_pow, Real.sq_sqrt (by have := hpos 0; nlinarith [this.1, this.2])]; rfl
    have ha0 : (a 0 : ℂ) ^ 2 = ((a₀ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hb0, ha0] at hconst
    rw [TwoVariable.carlsonRK_comm (ofReal_mem_slitPlane.2 (by nlinarith))
      (ofReal_mem_slitPlane.2 (pow_pos (hc.trans hac) 2)), hconst, div_self hM.ne',
      Real.arcsin_one]
    push_cast
    ring

end Carlson
