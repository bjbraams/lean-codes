/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Addition
public import Carlson.Elliptic.ZeroVariable
public import ToMathlib.Analysis.Complex.GeometricMean
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Complex duplication iteration

Carlson's Algorithm 9.6-2 uses the product of principal square roots of pairwise sums.
The real-part geometric-mean inequality preserves a positive lower bound on the real
parts of all three coordinates. Squared differences contract exactly by a factor of four.
These estimates prove convergence to a common right-half-plane limit `L` with
`R_F(x²,y²,z²)=1/L`, and give an explicit `4^(-n)` coordinate error bound. Pairwise
sums with positive real parts suffice for convergence. The zero-coordinate boundary
value is represented by `(π/2) R_K(x²,y²)`.
-/

open Complex Filter Set
open scoped Topology Real

@[expose] public noncomputable section

namespace Carlson

/-- One step of Algorithm 9.6-2 for complex square roots of the elliptic arguments. -/
def complexDupStep (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (1 / 2 * (p.1 + p.2.1) ^ (1 / 2 : ℂ) * (p.1 + p.2.2) ^ (1 / 2 : ℂ),
    1 / 2 * (p.2.1 + p.1) ^ (1 / 2 : ℂ) * (p.2.1 + p.2.2) ^ (1 / 2 : ℂ),
    1 / 2 * (p.2.2 + p.1) ^ (1 / 2 : ℂ) * (p.2.2 + p.2.1) ^ (1 / 2 : ℂ))

/-- The complex duplication sequence of Algorithm 9.6-2. -/
def complexDupSeq (x y z : ℂ) (n : ℕ) : ℂ × ℂ × ℂ := complexDupStep^[n] (x, y, z)

/-- Squared coordinates after a complex duplication step. -/
theorem complexDupStep_sq (p : ℂ × ℂ × ℂ) :
    (complexDupStep p).1 ^ 2 = (p.1 + p.2.1) * (p.1 + p.2.2) / 4 ∧
      (complexDupStep p).2.1 ^ 2 = (p.2.1 + p.1) * (p.2.1 + p.2.2) / 4 ∧
      (complexDupStep p).2.2 ^ 2 = (p.2.2 + p.1) * (p.2.2 + p.2.1) / 4 := by
  dsimp only [complexDupStep]
  rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow]
  simp only [cpow_half_sq]
  constructor
  · ring
  constructor <;> ring

/-- The exact contraction identities (9.6-10), with no restriction on complex inputs. -/
theorem complexDupStep_sq_sub (p : ℂ × ℂ × ℂ) :
    (complexDupStep p).1 ^ 2 - (complexDupStep p).2.1 ^ 2 = (p.1 ^ 2 - p.2.1 ^ 2) / 4 ∧
      (complexDupStep p).1 ^ 2 - (complexDupStep p).2.2 ^ 2 = (p.1 ^ 2 - p.2.2 ^ 2) / 4 ∧
      (complexDupStep p).2.1 ^ 2 - (complexDupStep p).2.2 ^ 2 =
        (p.2.1 ^ 2 - p.2.2 ^ 2) / 4 := by
  obtain ⟨h1, h2, h3⟩ := complexDupStep_sq p
  rw [h1, h2, h3]
  constructor
  · ring
  constructor <;> ring

/-- Formula (9.6-9) over the complex numbers: only two new square roots are needed. -/
theorem complexDupStep_thd_eq {x y z : ℂ} (hxy : x + y ≠ 0) :
    (complexDupStep (x, y, z)).2.2 =
      2 * (complexDupStep (x, y, z)).1 * (complexDupStep (x, y, z)).2.1 / (x + y) := by
  have hs := cpow_half_sq (x + y)
  simp only [complexDupStep, add_comm y x, add_comm z x, add_comm z y]
  field_simp
  linear_combination -((x + z) ^ (1 / 2 : ℂ) * (y + z) ^ (1 / 2 : ℂ)) * hs

/-- A positive lower bound on real parts is preserved by the complex iteration. -/
theorem complexDupStep_re_ge {m : ℝ} (hm : 0 < m) {p : ℂ × ℂ × ℂ}
    (hp : m ≤ p.1.re ∧ m ≤ p.2.1.re ∧ m ≤ p.2.2.re) :
    m ≤ (complexDupStep p).1.re ∧ m ≤ (complexDupStep p).2.1.re ∧
      m ≤ (complexDupStep p).2.2.re := by
  have hbound {u v : ℂ} (hu : 2 * m ≤ u.re) (hv : 2 * m ≤ v.re) :
      m ≤ (1 / 2 * u ^ (1 / 2 : ℂ) * v ^ (1 / 2 : ℂ)).re := by
    have h := sqrt_re_mul_le_re_cpow_half_mul (by linarith : 0 < u.re)
      (by linarith : 0 < v.re)
    have hs : 2 * m ≤ Real.sqrt (u.re * v.re) := by
      apply (Real.le_sqrt (by positivity)
        (mul_nonneg (by linarith : 0 ≤ u.re) (by linarith : 0 ≤ v.re))).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]
    have he (w : ℂ) : ((1 / 2 : ℂ) * w).re = (1 / 2 : ℝ) * w.re := by
      rw [mul_re]
      norm_num
    rw [mul_assoc, he]
    linarith
  refine ⟨hbound ?_ ?_, hbound ?_ ?_, hbound ?_ ?_⟩ <;>
    simp only [add_re] <;> linarith [hp.1, hp.2.1, hp.2.2]

/-- A common upper bound on coordinate norms is preserved by complex duplication. -/
theorem complexDupStep_norm_le {M : ℝ} (hM : 0 ≤ M) {p : ℂ × ℂ × ℂ}
    (hp : ‖p.1‖ ≤ M ∧ ‖p.2.1‖ ≤ M ∧ ‖p.2.2‖ ≤ M) :
    ‖(complexDupStep p).1‖ ≤ M ∧ ‖(complexDupStep p).2.1‖ ≤ M ∧
      ‖(complexDupStep p).2.2‖ ≤ M := by
  have hsum {a b : ℂ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) : ‖a + b‖ ≤ 2 * M :=
    (norm_add_le _ _).trans (by linarith)
  have hbound {w a b : ℂ} (hw : w ^ 2 = a * b / 4)
      (ha : ‖a‖ ≤ 2 * M) (hb : ‖b‖ ≤ 2 * M) : ‖w‖ ≤ M := by
    have h := congrArg norm hw
    norm_num only [norm_pow, norm_div, norm_mul, norm_ofNat] at h
    have hprod := mul_le_mul ha hb (norm_nonneg b) (by positivity : 0 ≤ 2 * M)
    nlinarith [norm_nonneg w]
  obtain ⟨h1, h2, h3⟩ := complexDupStep_sq p
  exact ⟨hbound h1 (hsum hp.1 hp.2.1) (hsum hp.1 hp.2.2),
    hbound h2 (hsum hp.2.1 hp.1) (hsum hp.2.1 hp.2.2),
    hbound h3 (hsum hp.2.2 hp.1) (hsum hp.2.2 hp.2.1)⟩

/-- Every iterate retains the initial lower real-part and upper norm bounds. -/
theorem complexDupSeq_bounds {x y z : ℂ} {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hlo : m ≤ x.re ∧ m ≤ y.re ∧ m ≤ z.re)
    (hhi : ‖x‖ ≤ M ∧ ‖y‖ ≤ M ∧ ‖z‖ ≤ M) (n : ℕ) :
    (m ≤ (complexDupSeq x y z n).1.re ∧ m ≤ (complexDupSeq x y z n).2.1.re ∧
      m ≤ (complexDupSeq x y z n).2.2.re) ∧
      (‖(complexDupSeq x y z n).1‖ ≤ M ∧ ‖(complexDupSeq x y z n).2.1‖ ≤ M ∧
        ‖(complexDupSeq x y z n).2.2‖ ≤ M) := by
  induction n with
  | zero => exact ⟨hlo, hhi⟩
  | succ n ih =>
    have hs : complexDupSeq x y z (n + 1) = complexDupStep (complexDupSeq x y z n) :=
      Function.iterate_succ_apply' complexDupStep n (x, y, z)
    rw [hs]
    exact ⟨complexDupStep_re_ge hm ih.1, complexDupStep_norm_le hM ih.2⟩

/-- **Carlson (9.6-10)** for arbitrary complex initial coordinates and every degree. -/
theorem complexDupSeq_sq_sub (x y z : ℂ) (n : ℕ) :
    let p := complexDupSeq x y z n
    p.1 ^ 2 - p.2.1 ^ 2 = (x ^ 2 - y ^ 2) / 4 ^ n ∧
      p.1 ^ 2 - p.2.2 ^ 2 = (x ^ 2 - z ^ 2) / 4 ^ n ∧
      p.2.1 ^ 2 - p.2.2 ^ 2 = (y ^ 2 - z ^ 2) / 4 ^ n := by
  induction n with
  | zero => simp [complexDupSeq]
  | succ n ih =>
    dsimp only at ih ⊢
    have hs : complexDupSeq x y z (n + 1) = complexDupStep (complexDupSeq x y z n) :=
      Function.iterate_succ_apply' complexDupStep n (x, y, z)
    rw [hs]
    have h := complexDupStep_sq_sub (complexDupSeq x y z n)
    rw [h.1, h.2.1, h.2.2, ih.1, ih.2.1, ih.2.2]
    simp [pow_succ, div_div]

/-- The complex duplication map preserves strictly positive real parts. -/
theorem complexDupStep_re_pos {p : ℂ × ℂ × ℂ}
    (hp : 0 < p.1.re ∧ 0 < p.2.1.re ∧ 0 < p.2.2.re) :
    0 < (complexDupStep p).1.re ∧ 0 < (complexDupStep p).2.1.re ∧
      0 < (complexDupStep p).2.2.re := by
  let m := min p.1.re (min p.2.1.re p.2.2.re)
  have hm : 0 < m := lt_min hp.1 (lt_min hp.2.1 hp.2.2)
  have h := complexDupStep_re_ge hm
    ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  exact ⟨hm.trans_le h.1, hm.trans_le h.2.1, hm.trans_le h.2.2⟩

/-- `R_F` is invariant under one complex step, on square roots in the right half-plane. -/
theorem carlsonRF_complexDupStep {p : ℂ × ℂ × ℂ}
    (hp : 0 < p.1.re ∧ 0 < p.2.1.re ∧ 0 < p.2.2.re) :
    carlsonRF ((complexDupStep p).1 ^ 2) ((complexDupStep p).2.1 ^ 2)
        ((complexDupStep p).2.2 ^ 2) = carlsonRF (p.1 ^ 2) (p.2.1 ^ 2) (p.2.2 ^ 2) := by
  have hsl {a : ℂ} (ha : 0 < a.re) : a ^ 2 ∈ slitPlane := by
    simpa only [sq] using mul_mem_slitPlane_of_re_pos ha ha
  have hsqrt {a : ℂ} (ha : 0 < a.re) : (a ^ 2) ^ (1 / 2 : ℂ) = a := by
    simpa only [one_div] using sq_cpow_two_inv ha
  have hlambda : dupLambda (p.1 ^ 2) (p.2.1 ^ 2) (p.2.2 ^ 2) =
      p.1 * p.2.1 + p.1 * p.2.2 + p.2.1 * p.2.2 := by
    simp only [dupLambda, hsqrt hp.1, hsqrt hp.2.1, hsqrt hp.2.2]
  have hdup := carlsonRF_duplication (hsl hp.1) (hsl hp.2.1) (hsl hp.2.2)
  rw [hlambda] at hdup
  have hnext := complexDupStep_re_pos hp
  have hscale := carlsonRF_mul_of_pos (l := 4) (by norm_num)
    (hsl hnext.1) (hsl hnext.2.1) (hsl hnext.2.2)
  norm_num only [ofReal_ofNat] at hscale
  have hfour : (4 : ℂ) ^ (-(1 / 2) : ℂ) = 1 / 2 := by
    have hh : (4 : ℂ) ^ (1 / 2 : ℂ) = 2 := by
      have hs : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      simpa only [hs, ofReal_ofNat] using ofReal_cpow_half (r := 4) (by norm_num)
    rw [Complex.cpow_neg, hh]
    norm_num
  rw [hfour] at hscale
  obtain ⟨h1, h2, h3⟩ := complexDupStep_sq p
  have he1 : p.1 ^ 2 + (p.1 * p.2.1 + p.1 * p.2.2 + p.2.1 * p.2.2) =
      4 * (complexDupStep p).1 ^ 2 := by rw [h1]; ring
  have he2 : p.2.1 ^ 2 + (p.1 * p.2.1 + p.1 * p.2.2 + p.2.1 * p.2.2) =
      4 * (complexDupStep p).2.1 ^ 2 := by rw [h2]; ring
  have he3 : p.2.2 ^ 2 + (p.1 * p.2.1 + p.1 * p.2.2 + p.2.1 * p.2.2) =
      4 * (complexDupStep p).2.2 ^ 2 := by rw [h3]; ring
  rw [he1, he2, he3, hscale] at hdup
  linear_combination -hdup

/-- The sum of the norms of the three squared-coordinate differences. -/
def complexDupSquaredSpread (p : ℂ × ℂ × ℂ) : ℝ :=
  ‖p.1 ^ 2 - p.2.1 ^ 2‖ + ‖p.1 ^ 2 - p.2.2 ^ 2‖ + ‖p.2.1 ^ 2 - p.2.2 ^ 2‖

/-- The complex squared spread contracts exactly by `4^(-n)`. -/
theorem complexDupSquaredSpread_seq (x y z : ℂ) (n : ℕ) :
    complexDupSquaredSpread (complexDupSeq x y z n) =
      complexDupSquaredSpread (x, y, z) / 4 ^ n := by
  obtain ⟨h1, h2, h3⟩ := complexDupSeq_sq_sub x y z n
  simp only [complexDupSquaredSpread, h1, h2, h3, norm_div, norm_pow]
  norm_num only [norm_ofNat]
  ring

/-- In a right half-plane, squared differences control ordinary differences uniformly. -/
private theorem norm_sub_le_norm_sq_sub {m : ℝ} (hm : 0 < m) {x y : ℂ}
    (hx : m ≤ x.re) (hy : m ≤ y.re) :
    ‖x - y‖ ≤ ‖x ^ 2 - y ^ 2‖ / (2 * m) := by
  have hsum : 2 * m ≤ ‖x + y‖ := by
    have hre := (le_abs_self (x + y).re).trans (abs_re_le_norm (x + y))
    rw [add_re] at hre
    linarith
  have he : ‖x ^ 2 - y ^ 2‖ = ‖x - y‖ * ‖x + y‖ := by
    rw [← norm_mul]
    congr 1
    ring
  apply (le_div_iff₀ (by positivity : 0 < 2 * m)).mpr
  rw [he]
  nlinarith [norm_nonneg (x - y)]

/-- A coordinate changes by at most a constant times the squared spread in one step. -/
private theorem norm_dupCoordinate_sub_le {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    {w x y z : ℂ} (hw : w ^ 2 = (x + y) * (x + z) / 4)
    (hwre : m ≤ w.re) (hx : m ≤ x.re) (hy : m ≤ y.re) (hz : m ≤ z.re)
    (hxM : ‖x‖ ≤ M) (hzM : ‖z‖ ≤ M) :
    ‖w - x‖ ≤ M * (‖x ^ 2 - y ^ 2‖ + ‖x ^ 2 - z ^ 2‖) / (8 * m ^ 2) := by
  have he : w ^ 2 - x ^ 2 = ((y - x) * (x + z) + 2 * x * (z - x)) / 4 := by
    rw [hw]
    ring
  have hsum : ‖x + z‖ ≤ 2 * M := (norm_add_le _ _).trans (by linarith)
  have hsq : ‖w ^ 2 - x ^ 2‖ ≤ M * (‖x - y‖ + ‖x - z‖) / 2 := by
    rw [he, norm_div]
    norm_num only [norm_ofNat]
    calc
      _ ≤ (‖(y - x) * (x + z)‖ + ‖2 * x * (z - x)‖) / 4 := by
        gcongr
        exact norm_add_le _ _
      _ = (‖x - y‖ * ‖x + z‖ + 2 * ‖x‖ * ‖x - z‖) / 4 := by
        simp only [norm_mul, norm_sub_rev]
        norm_num
      _ ≤ (‖x - y‖ * (2 * M) + 2 * M * ‖x - z‖) / 4 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ‖w ^ 2 - x ^ 2‖ / (2 * m) := norm_sub_le_norm_sq_sub hm hwre hx
    _ ≤ (M * (‖x - y‖ + ‖x - z‖) / 2) / (2 * m) := by gcongr
    _ ≤ (M * (‖x ^ 2 - y ^ 2‖ / (2 * m) + ‖x ^ 2 - z ^ 2‖ / (2 * m)) / 2) /
        (2 * m) := by
      gcongr
      · exact norm_sub_le_norm_sq_sub hm hx hy
      · exact norm_sub_le_norm_sq_sub hm hx hz
    _ = _ := by field_simp; ring

/-- Uniform one-step displacement bound for the complex algorithm. -/
theorem complexDupStep_dist_le {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    {p : ℂ × ℂ × ℂ} (hlo : m ≤ p.1.re ∧ m ≤ p.2.1.re ∧ m ≤ p.2.2.re)
    (hhi : ‖p.1‖ ≤ M ∧ ‖p.2.1‖ ≤ M ∧ ‖p.2.2‖ ≤ M) :
    dist p.1 (complexDupStep p).1 ≤ M * complexDupSquaredSpread p / (8 * m ^ 2) ∧
      dist p.2.1 (complexDupStep p).2.1 ≤ M * complexDupSquaredSpread p / (8 * m ^ 2) ∧
      dist p.2.2 (complexDupStep p).2.2 ≤ M * complexDupSquaredSpread p / (8 * m ^ 2) := by
  obtain ⟨hs1, hs2, hs3⟩ := complexDupStep_sq p
  have hre := complexDupStep_re_ge hm hlo
  have h1 := norm_dupCoordinate_sub_le hm hM hs1 hre.1 hlo.1 hlo.2.1 hlo.2.2 hhi.1 hhi.2.2
  have h2 := norm_dupCoordinate_sub_le hm hM hs2 hre.2.1 hlo.2.1 hlo.1 hlo.2.2 hhi.2.1 hhi.2.2
  have h3 := norm_dupCoordinate_sub_le hm hM hs3 hre.2.2 hlo.2.2 hlo.1 hlo.2.1 hhi.2.2 hhi.2.1
  simp only [dist_eq_norm, norm_sub_rev] at h1 h2 h3 ⊢
  refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_⟩ <;>
    apply div_le_div_of_nonneg_right _ (by positivity) <;>
    apply mul_le_mul_of_nonneg_left _ hM <;>
    unfold complexDupSquaredSpread <;>
    linarith [norm_nonneg (p.1 ^ 2 - p.2.1 ^ 2),
      norm_nonneg (p.1 ^ 2 - p.2.2 ^ 2), norm_nonneg (p.2.1 ^ 2 - p.2.2 ^ 2)]

/-- The three complex square roots converge to the same point in the right half-plane.
This is the convergence part of Carlson's Algorithm 9.6-2 for strictly positive real parts. -/
theorem exists_tendsto_complexDupSeq {x y z : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) (hz : 0 < z.re) :
    ∃ L : ℂ, 0 < L.re ∧
      Tendsto (fun n => (complexDupSeq x y z n).1) atTop (𝓝 L) ∧
      Tendsto (fun n => (complexDupSeq x y z n).2.1) atTop (𝓝 L) ∧
      Tendsto (fun n => (complexDupSeq x y z n).2.2) atTop (𝓝 L) := by
  let m := min x.re (min y.re z.re)
  let M := max ‖x‖ (max ‖y‖ ‖z‖)
  let S := complexDupSquaredSpread (x, y, z)
  let q := complexDupSeq x y z
  have hm : 0 < m := lt_min hx (lt_min hy hz)
  have hM : 0 ≤ M := (norm_nonneg x).trans (le_max_left _ _)
  have hb (n : ℕ) := complexDupSeq_bounds hm hM
    ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
    ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩ n
  have hs (n : ℕ) : q (n + 1) = complexDupStep (q n) :=
    Function.iterate_succ_apply' complexDupStep n (x, y, z)
  have hstep (n : ℕ) : dist (q n).1 (q (n + 1)).1 ≤
      (M * S / (8 * m ^ 2)) * (1 / 4 : ℝ) ^ n := by
    rw [hs]
    apply (complexDupStep_dist_le hm hM (hb n).1 (hb n).2).1.trans_eq
    rw [complexDupSquaredSpread_seq, div_pow]
    dsimp only [S]
    ring
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 4 : ℝ) (M * S / (8 * m ^ 2)) (by norm_num) hstep)
  have hLre : 0 < L.re := hm.trans_le (ge_of_tendsto
    (continuous_re.tendsto L |>.comp hL) (Eventually.of_forall fun n => (hb n).1.1))
  have hpow : Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hgap (n : ℕ) :
      dist (q n).1 (q n).2.1 ≤ S / (2 * m) * (1 / 4 : ℝ) ^ n ∧
        dist (q n).1 (q n).2.2 ≤ S / (2 * m) * (1 / 4 : ℝ) ^ n := by
    have h1 := norm_sub_le_norm_sq_sub hm (hb n).1.1 (hb n).1.2.1
    have h2 := norm_sub_le_norm_sq_sub hm (hb n).1.1 (hb n).1.2.2
    have hS1 : ‖(q n).1 ^ 2 - (q n).2.1 ^ 2‖ ≤ complexDupSquaredSpread (q n) := by
      unfold complexDupSquaredSpread
      linarith [norm_nonneg ((q n).1 ^ 2 - (q n).2.2 ^ 2),
        norm_nonneg ((q n).2.1 ^ 2 - (q n).2.2 ^ 2)]
    have hS2 : ‖(q n).1 ^ 2 - (q n).2.2 ^ 2‖ ≤ complexDupSquaredSpread (q n) := by
      unfold complexDupSquaredSpread
      linarith [norm_nonneg ((q n).1 ^ 2 - (q n).2.1 ^ 2),
        norm_nonneg ((q n).2.1 ^ 2 - (q n).2.2 ^ 2)]
    have he : complexDupSquaredSpread (q n) / (2 * m) =
        S / (2 * m) * (1 / 4 : ℝ) ^ n := by
      rw [complexDupSquaredSpread_seq, div_pow]
      dsimp only [S]
      ring
    rw [dist_eq_norm, dist_eq_norm]
    exact ⟨(h1.trans (by gcongr)).trans_eq he, (h2.trans (by gcongr)).trans_eq he⟩
  have hzero : Tendsto (fun n => S / (2 * m) * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul (S / (2 * m))
  exact ⟨L, hLre, hL,
    hL.congr_dist (squeeze_zero (fun n => dist_nonneg) (fun n => (hgap n).1) hzero),
    hL.congr_dist (squeeze_zero (fun n => dist_nonneg) (fun n => (hgap n).2) hzero)⟩

/-- **Carlson's Algorithm 9.6-2** for complex initial square roots in the right half-plane:
all three coordinates converge to `L`, with positive real part, and `R_F(x²,y²,z²)=1/L`. -/
theorem tendsto_complexDupSeq {x y z : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) (hz : 0 < z.re) :
    ∃ L : ℂ, 0 < L.re ∧
      Tendsto (fun n => (complexDupSeq x y z n).1) atTop (𝓝 L) ∧
      Tendsto (fun n => (complexDupSeq x y z n).2.1) atTop (𝓝 L) ∧
      Tendsto (fun n => (complexDupSeq x y z n).2.2) atTop (𝓝 L) ∧
      carlsonRF (x ^ 2) (y ^ 2) (z ^ 2) = L⁻¹ := by
  obtain ⟨L, hL, h1, h2, h3⟩ := exists_tendsto_complexDupSeq hx hy hz
  refine ⟨L, hL, h1, h2, h3, ?_⟩
  let q := complexDupSeq x y z
  have hs (n : ℕ) : q (n + 1) = complexDupStep (q n) :=
    Function.iterate_succ_apply' complexDupStep n (x, y, z)
  have hpos : ∀ n, 0 < (q n).1.re ∧ 0 < (q n).2.1.re ∧ 0 < (q n).2.2.re := by
    intro n
    induction n with
    | zero => exact ⟨hx, hy, hz⟩
    | succ n ih => rw [hs]; exact complexDupStep_re_pos ih
  have hinv : ∀ n, carlsonRF ((q n).1 ^ 2) ((q n).2.1 ^ 2) ((q n).2.2 ^ 2) =
      carlsonRF (x ^ 2) (y ^ 2) (z ^ 2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [hs, carlsonRF_complexDupStep (hpos n), ih]
  have hLsq : L ^ 2 ∈ slitPlane := by
    simpa only [sq] using mul_mem_slitPlane_of_re_pos hL hL
  have hRF : ContinuousAt (fun w : Fin 3 → ℂ => carlsonRF (w 0) (w 1) (w 2))
      ![L ^ 2, L ^ 2, L ^ 2] := by
    have hsl : (![L ^ 2, L ^ 2, L ^ 2] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
      intro i; fin_cases i <;> exact hLsq
    have hcont := (analyticOnNhd_regCarlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ))
      _ hsl).continuousAt
    have he : (fun w : Fin 3 → ℂ => carlsonRF (w 0) (w 1) (w 2)) =
        fun w => Gamma (3 / 2) * regCarlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) w := by
      funext w
      rw [carlsonRF_eq]
      congr 2
      funext i; fin_cases i <;> rfl
    rw [he]
    exact continuousAt_const.mul hcont
  have hvec : Tendsto (fun n : ℕ =>
      (![(q n).1 ^ 2, (q n).2.1 ^ 2, (q n).2.2 ^ 2] : Fin 3 → ℂ)) atTop
      (𝓝 ![L ^ 2, L ^ 2, L ^ 2]) := by
    rw [tendsto_pi_nhds]
    intro i; fin_cases i
    · exact h1.pow 2
    · exact h2.pow 2
    · exact h3.pow 2
  have hlim := hRF.tendsto.comp hvec
  simp only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, hinv] at hlim
  have he := tendsto_nhds_unique tendsto_const_nhds hlim
  rw [he, carlsonRF_self hLsq, show (-1 / 2 : ℂ) = -(1 / 2) by ring, Complex.cpow_neg]
  have hroot : (L ^ 2) ^ (1 / 2 : ℂ) = L := by
    simpa only [one_div] using sq_cpow_two_inv hL
  rw [hroot]

/-- An explicit `4^(-n)` error bound for all three complex coordinates.
The constants `m` and `M` bound the initial real parts below and norms above. -/
theorem complexDupSeq_dist_limit_le {x y z L : ℂ} {m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M)
    (hlo : m ≤ x.re ∧ m ≤ y.re ∧ m ≤ z.re)
    (hhi : ‖x‖ ≤ M ∧ ‖y‖ ≤ M ∧ ‖z‖ ≤ M)
    (h1 : Tendsto (fun n => (complexDupSeq x y z n).1) atTop (𝓝 L))
    (h2 : Tendsto (fun n => (complexDupSeq x y z n).2.1) atTop (𝓝 L))
    (h3 : Tendsto (fun n => (complexDupSeq x y z n).2.2) atTop (𝓝 L)) (n : ℕ) :
    dist (complexDupSeq x y z n).1 L ≤
        M * complexDupSquaredSpread (x, y, z) / (6 * m ^ 2 * 4 ^ n) ∧
      dist (complexDupSeq x y z n).2.1 L ≤
        M * complexDupSquaredSpread (x, y, z) / (6 * m ^ 2 * 4 ^ n) ∧
      dist (complexDupSeq x y z n).2.2 L ≤
        M * complexDupSquaredSpread (x, y, z) / (6 * m ^ 2 * 4 ^ n) := by
  let q := complexDupSeq x y z
  let C := M * complexDupSquaredSpread (x, y, z) / (8 * m ^ 2)
  have hstep (k : ℕ) :
      dist (q k).1 (q (k + 1)).1 ≤ C * (1 / 4 : ℝ) ^ k ∧
      dist (q k).2.1 (q (k + 1)).2.1 ≤ C * (1 / 4 : ℝ) ^ k ∧
      dist (q k).2.2 (q (k + 1)).2.2 ≤ C * (1 / 4 : ℝ) ^ k := by
    have hs : q (k + 1) = complexDupStep (q k) :=
      Function.iterate_succ_apply' complexDupStep k (x, y, z)
    rw [hs]
    have hb := complexDupSeq_bounds hm hM hlo hhi k
    have hd := complexDupStep_dist_le hm hM hb.1 hb.2
    have he : M * complexDupSquaredSpread (q k) / (8 * m ^ 2) = C * (1 / 4 : ℝ) ^ k := by
      rw [complexDupSquaredSpread_seq, div_pow]
      dsimp only [C]
      ring
    dsimp only [q] at he
    rw [he] at hd
    exact hd
  have he : C * (1 / 4 : ℝ) ^ n / (1 - 1 / 4) =
      M * complexDupSquaredSpread (x, y, z) / (6 * m ^ 2 * 4 ^ n) := by
    dsimp only [C]
    rw [div_pow]
    field_simp
    ring
  exact ⟨(dist_le_of_le_geometric_of_tendsto (1 / 4 : ℝ) C (by norm_num)
      (fun k => (hstep k).1) h1 n).trans_eq he,
    (dist_le_of_le_geometric_of_tendsto (1 / 4 : ℝ) C (by norm_num)
      (fun k => (hstep k).2.1) h2 n).trans_eq he,
    (dist_le_of_le_geometric_of_tendsto (1 / 4 : ℝ) C (by norm_num)
      (fun k => (hstep k).2.2) h3 n).trans_eq he⟩

/-- Convergence also holds whenever the three pairwise sums have positive real parts.
This includes the allowed zero-coordinate cases of Algorithm 9.6-2. -/
theorem exists_tendsto_complexDupSeq_of_pairwise_re_pos {x y z : ℂ}
    (hxy : 0 < (x + y).re) (hxz : 0 < (x + z).re) (hyz : 0 < (y + z).re) :
    ∃ L : ℂ, 0 < L.re ∧
      Tendsto (fun n => (complexDupSeq x y z n).1) atTop (𝓝 L) ∧
      Tendsto (fun n => (complexDupSeq x y z n).2.1) atTop (𝓝 L) ∧
      Tendsto (fun n => (complexDupSeq x y z n).2.2) atTop (𝓝 L) ∧
      carlsonRF ((complexDupStep (x, y, z)).1 ^ 2)
        ((complexDupStep (x, y, z)).2.1 ^ 2) ((complexDupStep (x, y, z)).2.2 ^ 2) = L⁻¹ := by
  let p := complexDupStep (x, y, z)
  have hhalf (u v : ℂ) (hu : 0 < u.re) (hv : 0 < v.re) :
      0 < (1 / 2 * u ^ (1 / 2 : ℂ) * v ^ (1 / 2 : ℂ)).re := by
    have h := re_cpow_half_mul_pos hu hv
    have he (w : ℂ) : ((1 / 2 : ℂ) * w).re = (1 / 2 : ℝ) * w.re := by
      rw [mul_re]; norm_num
    rw [mul_assoc, he]
    positivity
  have hp1 : 0 < p.1.re := hhalf _ _ hxy hxz
  have hp2 : 0 < p.2.1.re := hhalf _ _ (by simpa only [add_comm] using hxy) hyz
  have hp3 : 0 < p.2.2.re := hhalf _ _ (by simpa only [add_comm] using hxz)
    (by simpa only [add_comm] using hyz)
  obtain ⟨L, hL, h1, h2, h3, hRF⟩ := tendsto_complexDupSeq hp1 hp2 hp3
  have hshift (n : ℕ) : complexDupSeq x y z (n + 1) =
      complexDupSeq p.1 p.2.1 p.2.2 n := by
    change complexDupStep^[n + 1] (x, y, z) = complexDupStep^[n] (p.1, p.2.1, p.2.2)
    rw [Function.iterate_succ_apply]
  exact ⟨L, hL, (tendsto_add_atTop_iff_nat 1).mp (by simpa only [hshift] using h1),
    (tendsto_add_atTop_iff_nat 1).mp (by simpa only [hshift] using h2),
    (tendsto_add_atTop_iff_nat 1).mp (by simpa only [hshift] using h3), hRF⟩

/-- **Algorithm 9.6-2 at the complex zero-coordinate boundary**. The value of `R_F`
at this boundary is written as `(π/2) R_K(x²,y²)`, as in (8.3-17). -/
theorem tendsto_complexDupSeq_zero {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    ∃ L : ℂ, 0 < L.re ∧
      Tendsto (fun n => (complexDupSeq x y 0 n).1) atTop (𝓝 L) ∧
      Tendsto (fun n => (complexDupSeq x y 0 n).2.1) atTop (𝓝 L) ∧
      Tendsto (fun n => (complexDupSeq x y 0 n).2.2) atTop (𝓝 L) ∧
      (π / 2 : ℂ) * TwoVariable.carlsonRK (x ^ 2) (y ^ 2) = L⁻¹ := by
  obtain ⟨L, hL, h1, h2, h3, hRF⟩ := exists_tendsto_complexDupSeq_of_pairwise_re_pos
    (x := x) (y := y) (z := 0) (by rw [add_re]; linarith) (by simpa) (by simpa)
  refine ⟨L, hL, h1, h2, h3, ?_⟩
  have hsl {a : ℂ} (ha : 0 < a.re) : a ^ 2 ∈ slitPlane := by
    simpa only [sq] using mul_mem_slitPlane_of_re_pos ha ha
  have hsqrt {a : ℂ} (ha : 0 < a.re) : (a ^ 2) ^ (1 / 2 : ℂ) = a := by
    simpa only [one_div] using sq_cpow_two_inv ha
  have hdup := carlsonRK_duplication (hsl hx) (hsl hy)
  rw [hsqrt hx, hsqrt hy] at hdup
  have hs := complexDupStep_sq (x, y, 0)
  dsimp only at hs
  simp only [add_zero, zero_add] at hs
  have hp : 0 < (complexDupStep (x, y, 0)).1.re ∧
      0 < (complexDupStep (x, y, 0)).2.1.re ∧ 0 < (complexDupStep (x, y, 0)).2.2.re := by
    have hpos (u v : ℂ) (hu : 0 < u.re) (hv : 0 < v.re) :
        0 < (1 / 2 * u ^ (1 / 2 : ℂ) * v ^ (1 / 2 : ℂ)).re := by
      have he (w : ℂ) : ((1 / 2 : ℂ) * w).re = (1 / 2 : ℝ) * w.re := by
        rw [mul_re]; norm_num
      rw [mul_assoc, he]
      exact mul_pos (by norm_num) (re_cpow_half_mul_pos hu hv)
    exact ⟨hpos _ _ (by rw [add_re]; linarith) (by simpa),
      hpos _ _ (by rw [add_re]; linarith) (by simpa), hpos _ _ (by simpa) (by simpa)⟩
  have hscale := carlsonRF_mul_of_pos (l := 4) (by norm_num)
    (hsl hp.1) (hsl hp.2.1) (hsl hp.2.2)
  norm_num only [ofReal_ofNat] at hscale
  have hfour : (4 : ℂ) ^ (-(1 / 2) : ℂ) = 1 / 2 := by
    have hh : (4 : ℂ) ^ (1 / 2 : ℂ) = 2 := by
      have hs : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      simpa only [hs, ofReal_ofNat] using ofReal_cpow_half (r := 4) (by norm_num)
    rw [Complex.cpow_neg, hh]
    norm_num
  rw [hfour] at hscale
  have he1 : x ^ 2 + x * y = 4 * (complexDupStep (x, y, 0)).1 ^ 2 := by rw [hs.1]; ring
  have he2 : y ^ 2 + x * y = 4 * (complexDupStep (x, y, 0)).2.1 ^ 2 := by rw [hs.2.1]; ring
  have he3 : x * y = 4 * (complexDupStep (x, y, 0)).2.2 ^ 2 := by rw [hs.2.2]; ring
  rw [he1, he2, he3, hscale, hRF] at hdup
  simpa using hdup

end Carlson
