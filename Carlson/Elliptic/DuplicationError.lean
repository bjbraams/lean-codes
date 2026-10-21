/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Addition
public import Carlson.Elliptic.ZeroVariable
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quantitative acceleration of the duplication algorithm

For positive real initial square roots, the arithmetic mean in Carlson (9.6-11)
approximates the common limit with error bounded by a constant times `16^(-n)`.
The bound below holds at every iteration, with an explicit constant depending only
on the initial minimum and squared differences. It complements the exact contraction
identities (9.6-10). It does not assert the leading coefficient or the next remainder
in the more precise expansion (9.6-12).
-/

open Filter Set
open scoped Topology Real

@[expose] public noncomputable section

namespace Carlson

/-- The accelerated approximation (9.6-11), the arithmetic mean of the square roots. -/
def dupMean (p : ℝ × ℝ × ℝ) : ℝ := (p.1 + p.2.1 + p.2.2) / 3

/-- Sum of the absolute squared differences, a convenient measure of the initial spread. -/
def dupSquaredSpread (p : ℝ × ℝ × ℝ) : ℝ :=
  |p.1 ^ 2 - p.2.1 ^ 2| + |p.1 ^ 2 - p.2.2 ^ 2| + |p.2.1 ^ 2 - p.2.2 ^ 2|

/-- The squared spread decays exactly by `4^(-n)`, including nonnegative initial data. -/
theorem dupSquaredSpread_dupSeq {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (n : ℕ) :
    dupSquaredSpread (dupSeq x y z n) = dupSquaredSpread (x, y, z) / 4 ^ n := by
  obtain ⟨h1, h2, h3⟩ := dupSeq_sq_sub hx hy hz n
  simp only [dupSquaredSpread, h1, h2, h3, abs_div, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ 4 ^ n)]
  ring

/-- A positive lower bound on all coordinates is preserved by duplication. -/
private theorem dupStep_ge {m : ℝ} (hm : 0 < m) {p : ℝ × ℝ × ℝ}
    (hp : m ≤ p.1 ∧ m ≤ p.2.1 ∧ m ≤ p.2.2) :
    m ≤ (dupStep p).1 ∧ m ≤ (dupStep p).2.1 ∧ m ≤ (dupStep p).2.2 := by
  have hbound {u v : ℝ} (hu : 2 * m ≤ u) (hv : 2 * m ≤ v) :
      m ≤ 1 / 2 * √u * √v := by
    calc
      m = 1 / 2 * √(2 * m) * √(2 * m) := by
        nlinarith [Real.mul_self_sqrt (show 0 ≤ 2 * m by positivity)]
      _ ≤ _ := by gcongr
  exact ⟨hbound (by linarith [hp.1, hp.2.1]) (by linarith [hp.1, hp.2.2]),
    hbound (by linarith [hp.1, hp.2.1]) (by linarith [hp.2.1, hp.2.2]),
    hbound (by linarith [hp.1, hp.2.2]) (by linarith [hp.2.1, hp.2.2])⟩

/-- The quadratic arithmetic/geometric mean deficit in one coordinate, estimated by
the corresponding squared-node difference. -/
private theorem dupCoordinate_deficit_le {m x y z S : ℝ} (hm : 0 < m)
    (hx : m ≤ x) (hy : m ≤ y) (hz : m ≤ z) (hS : |y ^ 2 - z ^ 2| ≤ S) :
    0 ≤ (2 * x + y + z) / 4 - 1 / 2 * √(x + y) * √(x + z) ∧
      (2 * x + y + z) / 4 - 1 / 2 * √(x + y) * √(x + z) ≤ S ^ 2 / (32 * m ^ 3) := by
  set A := √(x + y)
  set B := √(x + z)
  set e := (2 * x + y + z) / 4 - 1 / 2 * A * B
  have hA : A ^ 2 = x + y := Real.sq_sqrt (by linarith)
  have hB : B ^ 2 = x + z := Real.sq_sqrt (by linarith)
  have hA₀ : 0 ≤ A := Real.sqrt_nonneg _
  have hB₀ : 0 ≤ B := Real.sqrt_nonneg _
  have he : e = (A - B) ^ 2 / 4 := by dsimp [e]; nlinarith
  have he₀ : 0 ≤ e := by rw [he]; positivity
  have heq : e * (4 * (A + B) ^ 2) = (y - z) ^ 2 := by
    calc
      _ = (A ^ 2 - B ^ 2) ^ 2 := by rw [he]; ring
      _ = _ := by rw [hA, hB]; ring
  have hden : 8 * m ≤ 4 * (A + B) ^ 2 := by
    nlinarith [mul_nonneg hA₀ hB₀]
  have hsmall : e * (8 * m) ≤ (y - z) ^ 2 := by
    nlinarith [mul_nonneg he₀ (sub_nonneg.mpr hden)]
  have hgap : 2 * m * |y - z| ≤ S := by
    calc
      _ ≤ |y - z| * (y + z) := by nlinarith [abs_nonneg (y - z)]
      _ = |y ^ 2 - z ^ 2| := by
        rw [show y ^ 2 - z ^ 2 = (y - z) * (y + z) by ring,
          abs_mul, abs_of_pos (by linarith : 0 < y + z)]
      _ ≤ _ := hS
  have hgap₂ := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * m * |y - z|) hgap 2
  simp only [mul_pow, sq_abs] at hgap₂
  refine ⟨he₀, (le_div_iff₀ (by positivity : 0 < 32 * m ^ 3)).mpr ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hsmall (sq_nonneg (2 * m))]

/-- Duplication decreases the arithmetic mean by at most a quadratic spread error. -/
theorem dupMean_sub_step_le {m : ℝ} (hm : 0 < m) {p : ℝ × ℝ × ℝ}
    (hp : m ≤ p.1 ∧ m ≤ p.2.1 ∧ m ≤ p.2.2) :
    0 ≤ dupMean p - dupMean (dupStep p) ∧
      dupMean p - dupMean (dupStep p) ≤ dupSquaredSpread p ^ 2 / (32 * m ^ 3) := by
  have h1 := dupCoordinate_deficit_le hm hp.1 hp.2.1 hp.2.2
    (show |p.2.1 ^ 2 - p.2.2 ^ 2| ≤ dupSquaredSpread p by
      unfold dupSquaredSpread; linarith [abs_nonneg (p.1 ^ 2 - p.2.1 ^ 2),
        abs_nonneg (p.1 ^ 2 - p.2.2 ^ 2)])
  have h2 := dupCoordinate_deficit_le hm hp.2.1 hp.1 hp.2.2
    (show |p.1 ^ 2 - p.2.2 ^ 2| ≤ dupSquaredSpread p by
      unfold dupSquaredSpread; linarith [abs_nonneg (p.1 ^ 2 - p.2.1 ^ 2),
        abs_nonneg (p.2.1 ^ 2 - p.2.2 ^ 2)])
  have h3 := dupCoordinate_deficit_le hm hp.2.2 hp.1 hp.2.1
    (show |p.1 ^ 2 - p.2.1 ^ 2| ≤ dupSquaredSpread p by
      unfold dupSquaredSpread; linarith [abs_nonneg (p.1 ^ 2 - p.2.2 ^ 2),
        abs_nonneg (p.2.1 ^ 2 - p.2.2 ^ 2)])
  dsimp only [dupMean, dupStep]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **Quantitative acceleration in (9.6-11)**: at every iteration the arithmetic mean
approximates the common limit with an explicit `16^(-n)` error bound.
Here `m` is any positive lower bound on the initial coordinates. -/
theorem abs_dupMean_sub_limit_le {x y z m L : ℝ} (hm : 0 < m)
    (hx : m ≤ x) (hy : m ≤ y) (hz : m ≤ z)
    (hL : Tendsto (fun n => dupMean (dupSeq x y z n)) atTop (𝓝 L)) (n : ℕ) :
    |dupMean (dupSeq x y z n) - L| ≤
      dupSquaredSpread (x, y, z) ^ 2 / (30 * m ^ 3 * 16 ^ n) := by
  have hbound : ∀ j, m ≤ (dupSeq x y z j).1 ∧ m ≤ (dupSeq x y z j).2.1 ∧
      m ≤ (dupSeq x y z j).2.2 := by
    intro j
    induction j with
    | zero => exact ⟨hx, hy, hz⟩
    | succ j ih =>
      have hsucc : dupSeq x y z (j + 1) = dupStep (dupSeq x y z j) :=
        Function.iterate_succ_apply' dupStep j (x, y, z)
      rw [hsucc]
      exact dupStep_ge hm ih
  have hstep (j : ℕ) :
      dist (dupMean (dupSeq x y z j)) (dupMean (dupSeq x y z (j + 1))) ≤
        (dupSquaredSpread (x, y, z) ^ 2 / (32 * m ^ 3)) * (1 / 16 : ℝ) ^ j := by
    have he := dupMean_sub_step_le hm (hbound j)
    have hsucc : dupSeq x y z (j + 1) = dupStep (dupSeq x y z j) :=
      Function.iterate_succ_apply' dupStep j (x, y, z)
    rw [hsucc, Real.dist_eq, abs_of_nonneg he.1]
    apply he.2.trans_eq
    rw [dupSquaredSpread_dupSeq (hm.trans_le hx).le (hm.trans_le hy).le (hm.trans_le hz).le]
    have hpow : ((4 : ℝ) ^ j) ^ 2 = 16 ^ j := by
      rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
      norm_num
    rw [div_pow, hpow, div_pow]
    ring
  have h := dist_le_of_le_geometric_of_tendsto (1 / 16 : ℝ)
    (dupSquaredSpread (x, y, z) ^ 2 / (32 * m ^ 3)) (by norm_num) hstep hL n
  rw [Real.dist_eq] at h
  convert h using 1
  rw [div_pow]
  field_simp
  ring

/-- The accelerated approximation converges to the reciprocal of `R_F`, with a
uniform geometric error bound from the initial minimum onward. -/
theorem exists_dupMean_error_bound {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ∃ L : ℝ, 0 < L ∧
      carlsonRF ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ) = ((L⁻¹ : ℝ) : ℂ) ∧
      ∀ n : ℕ, |dupMean (dupSeq x y z n) - L| ≤
        dupSquaredSpread (x, y, z) ^ 2 / (30 * (min x (min y z)) ^ 3 * 16 ^ n) := by
  obtain ⟨L, hL, h1, h2, h3, hRF⟩ := tendsto_dupSeq hx hy hz
  refine ⟨L, hL, hRF, fun n => abs_dupMean_sub_limit_le (lt_min hx (lt_min hy hz))
    (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) ?_ n⟩
  have he : (L + L + L) / 3 = L := by ring
  simpa only [dupMean, he] using ((h1.add h2).add h3).div_const 3

/-- **Algorithm 9.6-2 with one zero coordinate**: the positive real iteration started
at `(x,y,0)` converges to a positive common limit. The elliptic value at this boundary
is written as `(π/2) R_K(x²,y²)`, consistently with (8.3-17). -/
theorem tendsto_dupSeq_zero {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun n => (dupSeq x y 0 n).1) atTop (𝓝 L) ∧
      Tendsto (fun n => (dupSeq x y 0 n).2.1) atTop (𝓝 L) ∧
      Tendsto (fun n => (dupSeq x y 0 n).2.2) atTop (𝓝 L) ∧
      (Real.pi / 2 : ℂ) * TwoVariable.carlsonRK ((x ^ 2 : ℝ) : ℂ) ((y ^ 2 : ℝ) : ℂ) =
        ((L⁻¹ : ℝ) : ℂ) := by
  let q := dupStep (x, y, 0)
  have hq₁ : 0 < q.1 := by dsimp [q, dupStep]; positivity
  have hq₂ : 0 < q.2.1 := by dsimp [q, dupStep]; positivity
  have hq₃ : 0 < q.2.2 := by dsimp [q, dupStep]; positivity
  obtain ⟨L, hL, h1, h2, h3, hRF⟩ := tendsto_dupSeq hq₁ hq₂ hq₃
  have hshift (n : ℕ) : dupSeq x y 0 (n + 1) = dupSeq q.1 q.2.1 q.2.2 n := by
    change dupStep^[n + 1] (x, y, 0) = dupStep^[n] (q.1, q.2.1, q.2.2)
    rw [Function.iterate_succ_apply]
  refine ⟨L, hL, (tendsto_add_atTop_iff_nat 1).mp ?_,
    (tendsto_add_atTop_iff_nat 1).mp ?_, (tendsto_add_atTop_iff_nat 1).mp ?_, ?_⟩
  · simpa only [hshift] using h1
  · simpa only [hshift] using h2
  · simpa only [hshift] using h3
  have hs₁ : q.1 ^ 2 = x * (x + y) / 4 := by
    dsimp [q, dupStep]
    simp only [add_zero]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hx.le]
    ring
  have hs₂ : q.2.1 ^ 2 = y * (x + y) / 4 := by
    dsimp [q, dupStep]
    simp only [add_zero]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hy.le]
    ring
  have hs₃ : q.2.2 ^ 2 = x * y / 4 := by
    dsimp [q, dupStep]
    simp only [zero_add]
    rw [mul_pow, mul_pow, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]
    ring
  have hdup := carlsonRK_duplication_ofReal (pow_pos hx 2) (pow_pos hy 2)
  rw [Real.sqrt_sq hx.le, Real.sqrt_sq hy.le] at hdup
  have hscale := carlsonRF_mul_of_pos (l := 4) (by norm_num)
    (Complex.ofReal_mem_slitPlane.mpr (pow_pos hq₁ 2))
    (Complex.ofReal_mem_slitPlane.mpr (pow_pos hq₂ 2))
    (Complex.ofReal_mem_slitPlane.mpr (pow_pos hq₃ 2))
  norm_num only [Complex.ofReal_ofNat] at hscale
  have hfourHalf : (4 : ℂ) ^ (1 / 2 : ℂ) = 2 := by
    have hs : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simpa only [hs, Complex.ofReal_ofNat] using ofReal_cpow_half (r := 4) (by norm_num)
  have hfour : (4 : ℂ) ^ (-(1 / 2) : ℂ) = 1 / 2 := by
    rw [Complex.cpow_neg, hfourHalf]
    norm_num
  have he₁ : ((x ^ 2 + x * y : ℝ) : ℂ) = 4 * ((q.1 ^ 2 : ℝ) : ℂ) := by
    rw [hs₁]; push_cast; ring
  have he₂ : ((y ^ 2 + x * y : ℝ) : ℂ) = 4 * ((q.2.1 ^ 2 : ℝ) : ℂ) := by
    rw [hs₂]; push_cast; ring
  have he₃ : ((x * y : ℝ) : ℂ) = 4 * ((q.2.2 ^ 2 : ℝ) : ℂ) := by
    rw [hs₃]; push_cast; ring
  rw [he₁, he₂, he₃, hscale] at hdup
  norm_num only [Complex.ofReal_ofNat, hfour] at hdup
  rw [hdup, hRF]
  ring

end Carlson
