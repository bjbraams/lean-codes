/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Landen
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Ascending Landen and descending Gauss transformations (Carlson's Algorithms 9.5-2, 9.5-3)

Both algorithms share the step `a' = (a + (a² - c²)^{1/2})/2`, `c' = c²/(4a')`. With
`b = (a² - c²)^{1/2}`, this is `a' = (a + b)/2`, `c' = (a - b)/2` and `b' = (ab)^{1/2}`. So `a` and
`b` run through the arithmetic–geometric mean iteration, `a → M > 0`, and `c → 0` quadratically.

* **Ascending Landen transformations** (Algorithm 9.5-2). With
  `2s' = s + (s² + c²)^{1/2}`, `R_F(s², s² + c², s² + a²)` is invariant. Hence
  `R_F(s₀², s₀² + c₀², s₀² + a₀²) = R_C(S² + M², S²) = (1/M) arcsinh(M/S)`.
* **Descending Gauss transformations** (Algorithm 9.5-3). With
  `2t' = t + (t² - c²)^{1/2}`, `R_F(t² - a², t² - c², t²)` is invariant. Hence
  `R_F(t₀² - a₀², t₀² - c₀², t₀²) = R_C(T² - M², T²) = (1/M) arcsin(M/T)`.

Each step is an instance of Landen's transformation (9.5-4). The formalization assumes
`s₀ > 0`, where Carlson allows `s₀ = 0`, and `t₀ > a₀`, where Carlson allows `t₀ = a₀`. In both
excluded cases a variable of `R_F` vanishes.

## Main results

* `Carlson.tendsto_ascLanden`: Algorithm 9.5-2.
* `Carlson.tendsto_descGauss`: Algorithm 9.5-3.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §9.5.
-/

open Complex Set Filter
open scoped Real Topology
@[expose] public noncomputable section

namespace Carlson

/-! ### The common `(a, c)` step -/

/-- The common step `a' = (a + (a² - c²)^{1/2})/2`, `c' = c²/(4a')` of Algorithms 9.5-2, 9.5-3. -/
def landenACStep (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + √(p.1 ^ 2 - p.2 ^ 2)) / 2, p.2 ^ 2 / (4 * ((p.1 + √(p.1 ^ 2 - p.2 ^ 2)) / 2)))

section ACStep

variable {a c : ℝ} (hc : 0 < c) (hac : c < a)
include hc hac

private theorem sqrt_sub_pos : 0 < √(a ^ 2 - c ^ 2) := Real.sqrt_pos.mpr (by nlinarith)

private theorem sqrt_sub_lt : √(a ^ 2 - c ^ 2) < a := by
  rw [Real.sqrt_lt' (by linarith)]; nlinarith

theorem landenACStep_snd :
    (landenACStep (a, c)).2 = (a - √(a ^ 2 - c ^ 2)) / 2 := by
  have hb := sqrt_sub_pos hc hac
  have hb2 : √(a ^ 2 - c ^ 2) ^ 2 = a ^ 2 - c ^ 2 := Real.sq_sqrt (by nlinarith)
  have ha : 0 < a := by linarith
  simp only [landenACStep]
  rw [div_eq_iff (by positivity)]
  linear_combination hb2

theorem landenACStep_lt : 0 < (landenACStep (a, c)).2 ∧
    (landenACStep (a, c)).2 < (landenACStep (a, c)).1 := by
  have hb := sqrt_sub_pos hc hac
  have hb' := sqrt_sub_lt hc hac
  rw [landenACStep_snd hc hac]
  exact ⟨by linarith, by simp only [landenACStep]; linarith⟩

/-- `b' = (ab)^{1/2}` for `b = (a² - c²)^{1/2}`. -/
theorem landenACStep_b :
    (landenACStep (a, c)).1 ^ 2 - (landenACStep (a, c)).2 ^ 2 = a * √(a ^ 2 - c ^ 2) := by
  rw [landenACStep_snd hc hac]
  simp only [landenACStep]
  ring

end ACStep

/-- The iterates of the common step. -/
def landenAC (a c : ℝ) (n : ℕ) : ℝ × ℝ := landenACStep^[n] (a, c)

section ACConvergence

variable {a₀ c₀ : ℝ} (hc : 0 < c₀) (hac : c₀ < a₀)
include hc hac

omit hc hac in
private theorem landenAC_succ (n : ℕ) :
    landenAC a₀ c₀ (n + 1) = landenACStep (landenAC a₀ c₀ n) :=
  Function.iterate_succ_apply' _ _ _

theorem landenAC_pos (n : ℕ) :
    0 < (landenAC a₀ c₀ n).2 ∧ (landenAC a₀ c₀ n).2 < (landenAC a₀ c₀ n).1 := by
  induction n with
  | zero => exact ⟨hc, hac⟩
  | succ n ih =>
    rw [landenAC_succ]
    exact landenACStep_lt (a := (landenAC a₀ c₀ n).1) (c := (landenAC a₀ c₀ n).2) ih.1 ih.2

/-- The geometric companion `b_n = (a_n² - c_n²)^{1/2}`. -/
def landenB (a₀ c₀ : ℝ) (n : ℕ) : ℝ :=
  √((landenAC a₀ c₀ n).1 ^ 2 - (landenAC a₀ c₀ n).2 ^ 2)

private theorem landenB_pos (n : ℕ) : 0 < landenB a₀ c₀ n :=
  sqrt_sub_pos (landenAC_pos hc hac n).1 (landenAC_pos hc hac n).2

private theorem landenB_lt (n : ℕ) : landenB a₀ c₀ n < (landenAC a₀ c₀ n).1 :=
  sqrt_sub_lt (landenAC_pos hc hac n).1 (landenAC_pos hc hac n).2

omit hc hac in
private theorem landenAC_fst_succ (n : ℕ) :
    (landenAC a₀ c₀ (n + 1)).1 = ((landenAC a₀ c₀ n).1 + landenB a₀ c₀ n) / 2 := by
  rw [landenAC_succ]; rfl

private theorem landenAC_snd_succ (n : ℕ) :
    (landenAC a₀ c₀ (n + 1)).2 = ((landenAC a₀ c₀ n).1 - landenB a₀ c₀ n) / 2 := by
  rw [landenAC_succ]
  exact landenACStep_snd (landenAC_pos hc hac n).1 (landenAC_pos hc hac n).2

private theorem landenB_succ (n : ℕ) :
    landenB a₀ c₀ (n + 1) = √((landenAC a₀ c₀ n).1 * landenB a₀ c₀ n) := by
  have h := landenACStep_b (landenAC_pos hc hac n).1 (landenAC_pos hc hac n).2
  rw [landenB, landenAC_succ, h]
  rfl

private theorem landenB_mono (n : ℕ) : landenB a₀ c₀ n ≤ landenB a₀ c₀ (n + 1) := by
  rw [landenB_succ hc hac]
  have hb := landenB_pos hc hac n
  have hlt := landenB_lt hc hac n
  calc landenB a₀ c₀ n = √(landenB a₀ c₀ n * landenB a₀ c₀ n) := (Real.sqrt_mul_self hb.le).symm
    _ ≤ _ := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hlt.le hb.le)

private theorem landenAC_fst_anti (n : ℕ) : (landenAC a₀ c₀ (n + 1)).1 ≤ (landenAC a₀ c₀ n).1 := by
  rw [landenAC_fst_succ]
  linarith [landenB_lt hc hac n]

/-- `a_{n+1} - b_{n+1} ≤ (a_n - b_n)/2`. -/
private theorem landenAC_gap (n : ℕ) :
    (landenAC a₀ c₀ (n + 1)).1 - landenB a₀ c₀ (n + 1) ≤
      ((landenAC a₀ c₀ n).1 - landenB a₀ c₀ n) / 2 := by
  rw [landenAC_fst_succ, landenB_succ hc hac]
  have hb := landenB_pos hc hac n
  have hlt := landenB_lt hc hac n
  have : landenB a₀ c₀ n ≤ √((landenAC a₀ c₀ n).1 * landenB a₀ c₀ n) := by
    calc landenB a₀ c₀ n = √(landenB a₀ c₀ n * landenB a₀ c₀ n) :=
          (Real.sqrt_mul_self hb.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hlt.le hb.le)
  linarith

private theorem landenAC_gap_le (n : ℕ) :
    (landenAC a₀ c₀ n).1 - landenB a₀ c₀ n ≤ (a₀ - landenB a₀ c₀ 0) / 2 ^ n := by
  induction n with
  | zero => simp [landenAC]
  | succ n ih =>
    calc _ ≤ ((landenAC a₀ c₀ n).1 - landenB a₀ c₀ n) / 2 := landenAC_gap hc hac n
      _ ≤ (a₀ - landenB a₀ c₀ 0) / 2 ^ n / 2 := by linarith
      _ = _ := by rw [pow_succ]; ring

/-- The `a_n` decrease to a positive limit `M` and `c_n → 0`, with `c_{n+1} ≤ (a₀ - b₀)/2^{n+1}`. -/
theorem landenAC_tendsto : ∃ M : ℝ, 0 < M ∧
    Tendsto (fun n => (landenAC a₀ c₀ n).1) atTop (𝓝 M) ∧
    Tendsto (fun n => (landenAC a₀ c₀ n).2) atTop (𝓝 0) ∧
    ∀ n, (landenAC a₀ c₀ (n + 1)).2 ≤ (a₀ - landenB a₀ c₀ 0) / 2 ^ (n + 1) := by
  have hanti : Antitone fun n => (landenAC a₀ c₀ n).1 :=
    antitone_nat_of_succ_le (landenAC_fst_anti hc hac)
  have hbmono : Monotone (landenB a₀ c₀) := monotone_nat_of_le_succ (landenB_mono hc hac)
  have hlow : ∀ n, landenB a₀ c₀ 0 ≤ (landenAC a₀ c₀ n).1 := fun n =>
    (hbmono (Nat.zero_le n)).trans (landenB_lt hc hac n).le
  obtain ⟨M, hM⟩ : ∃ M, Tendsto (fun n => (landenAC a₀ c₀ n).1) atTop (𝓝 M) :=
    ⟨_, tendsto_atTop_ciInf hanti ⟨landenB a₀ c₀ 0, fun _ ⟨n, hn⟩ => hn ▸ hlow n⟩⟩
  have hMpos : 0 < M := lt_of_lt_of_le (landenB_pos hc hac 0) (ge_of_tendsto' hM hlow)
  have hcbound : ∀ n, (landenAC a₀ c₀ (n + 1)).2 ≤ (a₀ - landenB a₀ c₀ 0) / 2 ^ (n + 1) := by
    intro n
    rw [landenAC_snd_succ hc hac, pow_succ]
    have h := landenAC_gap_le hc hac n
    rw [show (a₀ - landenB a₀ c₀ 0) / (2 ^ n * 2) = (a₀ - landenB a₀ c₀ 0) / 2 ^ n / 2 by ring]
    linarith
  refine ⟨M, hMpos, hM, ?_, hcbound⟩
  have hgeom : Tendsto (fun n : ℕ => (a₀ - landenB a₀ c₀ 0) / 2 ^ (n + 1)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    simpa [div_eq_mul_inv, inv_pow] using this.const_mul (a₀ - landenB a₀ c₀ 0)
  rw [← tendsto_add_atTop_iff_nat 1]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom
    (fun n => (landenAC_pos hc hac (n + 1)).1.le) hcbound

end ACConvergence

theorem landenACStep_snd_le {a c : ℝ} (hc : 0 < c) (hac : c < a) :
    (landenACStep (a, c)).2 ≤ c / 2 := by
  rw [landenACStep_snd hc hac]
  have hb := sqrt_sub_pos hc hac
  have hb2 : √(a ^ 2 - c ^ 2) ^ 2 = a ^ 2 - c ^ 2 := Real.sq_sqrt (by nlinarith)
  -- `a - b = c²/(a + b) ≤ c`
  have : (a - √(a ^ 2 - c ^ 2)) * (a + √(a ^ 2 - c ^ 2)) = c ^ 2 := by linear_combination -hb2
  nlinarith

theorem landenAC_snd_le {a₀ c₀ : ℝ} (hc : 0 < c₀) (hac : c₀ < a₀) (n : ℕ) :
    (landenAC a₀ c₀ n).2 ≤ c₀ / 2 ^ n := by
  induction n with
  | zero => simp [landenAC]
  | succ n ih =>
    rw [show landenAC a₀ c₀ (n + 1) = landenACStep (landenAC a₀ c₀ n) from
      Function.iterate_succ_apply' _ _ _]
    have h := landenACStep_snd_le (landenAC_pos hc hac n).1 (landenAC_pos hc hac n).2
    rw [pow_succ]
    calc _ ≤ (landenAC a₀ c₀ n).2 / 2 := h
      _ ≤ c₀ / 2 ^ n / 2 := by linarith
      _ = _ := by ring

/-- `R_F` is continuous at every point with positive real coordinates. -/
theorem continuousAt_carlsonRF_ofReal {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    ContinuousAt (fun w : Fin 3 → ℂ => carlsonRF (w 0) (w 1) (w 2))
      ![(p : ℂ), (q : ℂ), (r : ℂ)] := by
  have hs : (![(p : ℂ), (q : ℂ), (r : ℂ)] : Fin 3 → ℂ) ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact ofReal_mem_slitPlane.mpr hp
    · exact ofReal_mem_slitPlane.mpr hq
    · exact ofReal_mem_slitPlane.mpr hr
  have := (analyticOnNhd_regCarlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) _ hs).continuousAt
  have hc2 : ContinuousAt (fun w : Fin 3 → ℂ =>
      Gamma (3 / 2) * regCarlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) w) _ :=
    continuousAt_const.mul this
  refine hc2.congr (Filter.Eventually.of_forall fun w => ?_)
  show Gamma (3 / 2) * regCarlsonR (-1 / 2) (fun _ : Fin 3 => (1 / 2 : ℂ)) w =
    carlsonRF (w 0) (w 1) (w 2)
  rw [carlsonRF_eq]
  congr 2
  funext i; fin_cases i <;> rfl

/-- Limits of `R_F` along real functions with positive limits. -/
theorem tendsto_carlsonRF_ofReal {α : Type*} {l : Filter α} {f g h : α → ℝ} {p q r : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hf : Tendsto f l (𝓝 p)) (hg : Tendsto g l (𝓝 q))
    (hh : Tendsto h l (𝓝 r)) :
    Tendsto (fun n => carlsonRF (f n : ℂ) (g n : ℂ) (h n : ℂ)) l
      (𝓝 (carlsonRF (p : ℂ) (q : ℂ) (r : ℂ))) := by
  have hvec : Tendsto (fun n => (![(f n : ℂ), (g n : ℂ), (h n : ℂ)] : Fin 3 → ℂ)) l
      (𝓝 ![(p : ℂ), (q : ℂ), (r : ℂ)]) := by
    rw [tendsto_pi_nhds]
    intro i; fin_cases i
    · exact (continuous_ofReal.tendsto _).comp hf
    · exact (continuous_ofReal.tendsto _).comp hg
    · exact (continuous_ofReal.tendsto _).comp hh
  exact (continuousAt_carlsonRF_ofReal hp hq hr).tendsto.comp hvec

/-! ### Algorithm 9.5-2: ascending Landen transformations -/

/-- The sequence `s_n` of Algorithm 9.5-2: `2s_{n+1} = s_n + (s_n² + c_n²)^{1/2}`. -/
def ascLandenS (s₀ a₀ c₀ : ℝ) : ℕ → ℝ
  | 0 => s₀
  | n + 1 => (ascLandenS s₀ a₀ c₀ n + √(ascLandenS s₀ a₀ c₀ n ^ 2 + (landenAC a₀ c₀ n).2 ^ 2)) / 2

/-- One ascending Landen step preserves `R_F(s², s² + c², s² + a²)`. -/
theorem carlsonRF_ascStep {s a c : ℝ} (hs : 0 < s) (hc : 0 < c) (hac : c < a) :
    carlsonRF (((((s + √(s ^ 2 + c ^ 2)) / 2)) ^ 2 : ℝ) : ℂ)
      ((((s + √(s ^ 2 + c ^ 2)) / 2) ^ 2 + (landenACStep (a, c)).2 ^ 2 : ℝ) : ℂ)
      ((((s + √(s ^ 2 + c ^ 2)) / 2) ^ 2 + (landenACStep (a, c)).1 ^ 2 : ℝ) : ℂ) =
    carlsonRF ((s ^ 2 : ℝ) : ℂ) ((s ^ 2 + c ^ 2 : ℝ) : ℂ) ((s ^ 2 + a ^ 2 : ℝ) : ℂ) := by
  set R := √(s ^ 2 + c ^ 2)
  set b := √(a ^ 2 - c ^ 2)
  have hR2 : R ^ 2 = s ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = a ^ 2 - c ^ 2 := Real.sq_sqrt (by nlinarith)
  have hR0 : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hb0 : 0 < b := sqrt_sub_pos hc hac
  have hbl : b < a := sqrt_sub_lt hc hac
  have hc' := landenACStep_snd hc hac
  set s' := (s + R) / 2
  set a' := (landenACStep (a, c)).1
  set c' := (landenACStep (a, c)).2
  have ha' : a' = (a + b) / 2 := rfl
  have hs' : 0 < s' := by positivity
  set z := √(s ^ 2 + a ^ 2)
  set v := √(s' ^ 2 + a' ^ 2)
  set w := √(s' ^ 2 + c' ^ 2)
  have hz2 : z ^ 2 = s ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hv2' : v ^ 2 = s' ^ 2 + a' ^ 2 := Real.sq_sqrt (by positivity)
  have hw2' : w ^ 2 = s' ^ 2 + c' ^ 2 := Real.sq_sqrt (by positivity)
  have hprod : (s' ^ 2 + a' ^ 2) * (s' ^ 2 + c' ^ 2) = (s ^ 2 + a ^ 2) * s' ^ 2 := by
    rw [hc', ha']; simp only [s']
    linear_combination (((s + R) / 2) ^ 2 + s * ((s + R) / 2) - c ^ 2 / 4) / 4 * hR2 +
      (((s + R) / 2) ^ 2 / 2 - (a ^ 2 - b ^ 2 + c ^ 2) / 16) * hb2
  have h := carlsonRF_landen (x := s) (y := R) (z := z) (v := v) (w := w) hs hR0
    (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_pos.mpr (by positivity))
    (by rw [hv2', hw2', hz2, hc', ha']; simp only [s']
        linear_combination (1 / 2 : ℝ) * hR2 + (1 / 2 : ℝ) * hb2)
    (by rw [← Real.sqrt_mul (by positivity), hprod, Real.sqrt_mul (by positivity),
          Real.sqrt_sq hs'.le])
  rw [hR2, hz2, hv2', hw2'] at h
  have hsl : ∀ r : ℝ, 0 < r → ((r : ℂ)) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  rw [h, carlsonRF_comm_right (hsl _ (by positivity)) (hsl _ (by positivity))
    (hsl _ (by positivity))]

/-- **Carlson's Algorithm 9.5-2 (ascending Landen transformations)**: for `s₀ > 0` and
`a₀ > c₀ > 0`, `s_n → S > 0`, `a_n → M > 0`, `c_n → 0`, and
`R_F(s₀², s₀² + c₀², s₀² + a₀²) = R_C(S² + M², S²) = (1/M) arcsinh(M/S)`. -/
theorem tendsto_ascLanden {s₀ a₀ c₀ : ℝ} (hs : 0 < s₀) (hc : 0 < c₀) (hac : c₀ < a₀) :
    ∃ S M : ℝ, 0 < S ∧ 0 < M ∧ Tendsto (ascLandenS s₀ a₀ c₀) atTop (𝓝 S) ∧
      Tendsto (fun n => (landenAC a₀ c₀ n).1) atTop (𝓝 M) ∧
      Tendsto (fun n => (landenAC a₀ c₀ n).2) atTop (𝓝 0) ∧
      carlsonRF ((s₀ ^ 2 : ℝ) : ℂ) ((s₀ ^ 2 + c₀ ^ 2 : ℝ) : ℂ) ((s₀ ^ 2 + a₀ ^ 2 : ℝ) : ℂ) =
        TwoVariable.carlsonRC ((S ^ 2 + M ^ 2 : ℝ) : ℂ) ((S ^ 2 : ℝ) : ℂ) ∧
      carlsonRF ((s₀ ^ 2 : ℝ) : ℂ) ((s₀ ^ 2 + c₀ ^ 2 : ℝ) : ℂ) ((s₀ ^ 2 + a₀ ^ 2 : ℝ) : ℂ) =
        ((Real.arsinh (M / S) / M : ℝ) : ℂ) := by
  obtain ⟨M, hM, hMlim, hclim, -⟩ := landenAC_tendsto hc hac
  set σ := ascLandenS s₀ a₀ c₀
  set cc := fun n => (landenAC a₀ c₀ n).2
  have hcpos : ∀ n, 0 < cc n := fun n => (landenAC_pos hc hac n).1
  have hσ_succ : ∀ n, σ (n + 1) = (σ n + √(σ n ^ 2 + cc n ^ 2)) / 2 := fun n => rfl
  have hσ_pos : ∀ n, 0 < σ n := by
    intro n; induction n with
    | zero => exact hs
    | succ n ih => rw [hσ_succ]; have := Real.sqrt_nonneg (σ n ^ 2 + cc n ^ 2); linarith
  have hσ_mono : Monotone σ := monotone_nat_of_le_succ fun n => by
    rw [hσ_succ]
    have : σ n ≤ √(σ n ^ 2 + cc n ^ 2) :=
      calc σ n = √(σ n ^ 2) := (Real.sqrt_sq (hσ_pos n).le).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [hcpos n])
    linarith
  have hσ_bd : ∀ n, σ n ≤ s₀ + c₀ * (1 - 1 / 2 ^ n) := by
    intro n; induction n with
    | zero => simp [σ, ascLandenS]
    | succ n ih =>
      rw [hσ_succ]
      have h1 : √(σ n ^ 2 + cc n ^ 2) ≤ σ n + cc n := by
        rw [Real.sqrt_le_left (by linarith [hσ_pos n, hcpos n])]
        nlinarith [hσ_pos n, hcpos n]
      have h2 := landenAC_snd_le hc hac n
      have h3 : c₀ * (1 - 1 / 2 ^ n) + c₀ / 2 ^ n / 2 = c₀ * (1 - 1 / 2 ^ (n + 1)) := by
        rw [pow_succ]; field_simp; ring
      have : cc n ≤ c₀ / 2 ^ n := h2
      linarith
  obtain ⟨S, hSlim⟩ : ∃ S, Tendsto σ atTop (𝓝 S) := by
    refine ⟨_, tendsto_atTop_ciSup hσ_mono ⟨s₀ + c₀, fun _ ⟨n, hn⟩ => hn ▸ ?_⟩⟩
    have := hσ_bd n
    have : 0 ≤ c₀ / 2 ^ n := by positivity
    have : c₀ * (1 - 1 / 2 ^ n) ≤ c₀ := by
      have : 0 < 1 / (2 : ℝ) ^ n := by positivity
      nlinarith
    linarith
  have hS : 0 < S := lt_of_lt_of_le hs (hσ_mono.ge_of_tendsto hSlim 0)
  -- the invariant
  have hinv : ∀ n, carlsonRF ((σ n ^ 2 : ℝ) : ℂ) ((σ n ^ 2 + cc n ^ 2 : ℝ) : ℂ)
      ((σ n ^ 2 + (landenAC a₀ c₀ n).1 ^ 2 : ℝ) : ℂ) =
      carlsonRF ((s₀ ^ 2 : ℝ) : ℂ) ((s₀ ^ 2 + c₀ ^ 2 : ℝ) : ℂ) ((s₀ ^ 2 + a₀ ^ 2 : ℝ) : ℂ) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih =>
      rw [← ih, hσ_succ]
      have hstep := carlsonRF_ascStep (hσ_pos n) (landenAC_pos hc hac n).1
        (landenAC_pos hc hac n).2
      simp only [cc]
      rw [show landenAC a₀ c₀ (n + 1) = landenACStep (landenAC a₀ c₀ n) from
        Function.iterate_succ_apply' _ _ _]
      simpa only [Prod.mk.eta] using hstep
  have hf1 : Tendsto (fun n => σ n ^ 2) atTop (𝓝 (S ^ 2)) := hSlim.pow 2
  have hf2 : Tendsto (fun n => σ n ^ 2 + cc n ^ 2) atTop (𝓝 (S ^ 2)) := by
    simpa using hf1.add (hclim.pow 2)
  have hf3 : Tendsto (fun n => σ n ^ 2 + (landenAC a₀ c₀ n).1 ^ 2) atTop (𝓝 (S ^ 2 + M ^ 2)) :=
    hf1.add (hMlim.pow 2)
  have hlim := tendsto_carlsonRF_ofReal (pow_pos hS 2) (pow_pos hS 2)
    (show 0 < S ^ 2 + M ^ 2 by positivity) hf1 hf2 hf3
  simp only [hinv] at hlim
  have hval := tendsto_nhds_unique tendsto_const_nhds hlim
  have hsl : ∀ r : ℝ, 0 < r → ((r : ℂ)) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  have hRC : carlsonRF ((S ^ 2 : ℝ) : ℂ) ((S ^ 2 : ℝ) : ℂ) ((S ^ 2 + M ^ 2 : ℝ) : ℂ) =
      TwoVariable.carlsonRC ((S ^ 2 + M ^ 2 : ℝ) : ℂ) ((S ^ 2 : ℝ) : ℂ) := by
    rw [← carlsonRF_comm_right (hsl _ (by positivity)) (hsl _ (by positivity))
      (hsl _ (by positivity)), ← carlsonRF_comm_left (hsl _ (by positivity))
      (hsl _ (by positivity)) (hsl _ (by positivity)),
      carlsonRF_self_right (hsl _ (by positivity)) (hsl _ (by positivity))]
  refine ⟨S, M, hS, hM, hSlim, hMlim, hclim, by rw [hval, hRC], ?_⟩
  rw [hval, hRC, TwoVariable.carlsonRC_of_gt (by positivity) (by nlinarith)]
  congr 1
  rw [show S ^ 2 + M ^ 2 - S ^ 2 = M ^ 2 by ring, Real.sqrt_sq hM.le, Real.sqrt_sq hS.le,
    Real.arsinh]
  congr 2
  rw [show 1 + (M / S) ^ 2 = (S ^ 2 + M ^ 2) / S ^ 2 by field_simp,
    Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq hS.le]
  field_simp
  ring

/-! ### Algorithm 9.5-3: descending Gauss transformations -/

/-- The sequence `t_n` of Algorithm 9.5-3: `2t_{n+1} = t_n + (t_n² - c_n²)^{1/2}`. -/
def descGaussT (t₀ a₀ c₀ : ℝ) : ℕ → ℝ
  | 0 => t₀
  | n + 1 => (descGaussT t₀ a₀ c₀ n + √(descGaussT t₀ a₀ c₀ n ^ 2 - (landenAC a₀ c₀ n).2 ^ 2)) / 2

/-- One descending Gauss step: `t' - a' ≥ t - a`, and `R_F(t² - a², t² - c², t²)` is preserved. -/
private theorem descStep {t a c : ℝ} (hc : 0 < c) (hac : c < a) (hta : a < t) :
    t - a ≤ (t + √(t ^ 2 - c ^ 2)) / 2 - (landenACStep (a, c)).1 ∧
    carlsonRF (((((t + √(t ^ 2 - c ^ 2)) / 2) ^ 2 - (landenACStep (a, c)).1 ^ 2 : ℝ) : ℂ))
      ((((t + √(t ^ 2 - c ^ 2)) / 2) ^ 2 - (landenACStep (a, c)).2 ^ 2 : ℝ) : ℂ)
      ((((t + √(t ^ 2 - c ^ 2)) / 2) ^ 2 : ℝ) : ℂ) =
    carlsonRF ((t ^ 2 - a ^ 2 : ℝ) : ℂ) ((t ^ 2 - c ^ 2 : ℝ) : ℂ) ((t ^ 2 : ℝ) : ℂ) := by
  have ht : 0 < t := by linarith
  set R := √(t ^ 2 - c ^ 2)
  set b := √(a ^ 2 - c ^ 2)
  have hR2 : R ^ 2 = t ^ 2 - c ^ 2 := Real.sq_sqrt (by nlinarith)
  have hb2 : b ^ 2 = a ^ 2 - c ^ 2 := Real.sq_sqrt (by nlinarith)
  have hR0 : 0 < R := Real.sqrt_pos.mpr (by nlinarith)
  have hb0 : 0 < b := sqrt_sub_pos hc hac
  have hbl : b < a := sqrt_sub_lt hc hac
  have hRt : R < t := by rw [Real.sqrt_lt' ht]; nlinarith
  have hc' := landenACStep_snd hc hac
  set a' := (landenACStep (a, c)).1
  set c' := (landenACStep (a, c)).2
  have ha' : a' = (a + b) / 2 := rfl
  set t' := (t + R) / 2 with ht'def
  -- `R - b ≥ t - a`
  have hRb : t - a ≤ R - b := by
    have h1 : (R - b) * (R + b) = (t - a) * (t + a) := by linear_combination hR2 - hb2
    nlinarith
  have hgap : t - a ≤ t' - a' := by rw [ha', ht'def]; linarith
  refine ⟨hgap, ?_⟩
  have hta' : a' < t' := by linarith
  have hca' : c' < a' := (landenACStep_lt hc hac).2
  have hc'0 : 0 < c' := (landenACStep_lt hc hac).1
  have ht' : 0 < t' := by positivity
  have ha'0 : 0 < a' := by linarith
  have p1 : 0 < t ^ 2 - a ^ 2 := by
    rw [show t ^ 2 - a ^ 2 = (t - a) * (t + a) by ring]
    exact mul_pos (by linarith) (by linarith)
  have p2 : 0 < t ^ 2 - c ^ 2 := by
    rw [show t ^ 2 - c ^ 2 = (t - c) * (t + c) by ring]
    exact mul_pos (by linarith) (by linarith)
  have p3 : 0 < t' ^ 2 - a' ^ 2 := by
    rw [show t' ^ 2 - a' ^ 2 = (t' - a') * (t' + a') by ring]
    exact mul_pos (by linarith) (by linarith)
  have p4 : 0 < t' ^ 2 - c' ^ 2 := by
    rw [show t' ^ 2 - c' ^ 2 = (t' - c') * (t' + c') by ring]
    exact mul_pos (by linarith) (by linarith)
  set z := √(t ^ 2 - a ^ 2)
  set v := √(t' ^ 2 - a' ^ 2)
  set w := √(t' ^ 2 - c' ^ 2)
  have hz2 : z ^ 2 = t ^ 2 - a ^ 2 := Real.sq_sqrt p1.le
  have hv2' : v ^ 2 = t' ^ 2 - a' ^ 2 := Real.sq_sqrt p3.le
  have hw2' : w ^ 2 = t' ^ 2 - c' ^ 2 := Real.sq_sqrt p4.le
  have hprod : (t' ^ 2 - a' ^ 2) * (t' ^ 2 - c' ^ 2) = (t ^ 2 - a ^ 2) * t' ^ 2 := by
    rw [hc', ha']; simp only [t']
    linear_combination (((t + R) / 2) ^ 2 + t * ((t + R) / 2) + c ^ 2 / 4) / 4 * hR2 -
      (((t + R) / 2) ^ 2 / 2 + (a ^ 2 - b ^ 2 + c ^ 2) / 16) * hb2
  have h := carlsonRF_landen (x := t) (y := R) (z := z) (v := v) (w := w) ht hR0
    (Real.sqrt_pos.mpr p1) (Real.sqrt_pos.mpr p3) (Real.sqrt_pos.mpr p4)
    (by rw [hv2', hw2', hz2, hc', ha']; simp only [t']
        linear_combination (1 / 2 : ℝ) * hR2 - (1 / 2 : ℝ) * hb2)
    (by rw [← Real.sqrt_mul p3.le, hprod, Real.sqrt_mul p1.le, Real.sqrt_sq ht'.le])
  rw [hR2, hz2, hv2', hw2'] at h
  have hsl : ∀ r : ℝ, 0 < r → ((r : ℂ)) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  -- reorder both sides: `R_F(x, y, z) = R_F(z, y, x)`
  have hswap : ∀ p q r : ℝ, 0 < p → 0 < q → 0 < r →
      carlsonRF (p : ℂ) (q : ℂ) (r : ℂ) = carlsonRF (r : ℂ) (q : ℂ) (p : ℂ) := by
    intro p q r hp hq hr
    rw [carlsonRF_comm_left (hsl q hq) (hsl p hp) (hsl r hr),
      carlsonRF_comm_right (hsl q hq) (hsl r hr) (hsl p hp),
      carlsonRF_comm_left (hsl r hr) (hsl q hq) (hsl p hp)]
  rw [hswap _ _ _ p3 p4 (pow_pos ht' 2),
    carlsonRF_comm_right (hsl _ (pow_pos ht' 2)) (hsl _ p3) (hsl _ p4), ← h,
    hswap _ _ _ (pow_pos ht 2) p2 p1]

/-- **Carlson's Algorithm 9.5-3 (descending Gauss transformations)**: for `t₀ > a₀ > c₀ > 0`,
`t_n → T`, `a_n → M` with `T > M > 0`, `c_n → 0`, and
`R_F(t₀² - a₀², t₀² - c₀², t₀²) = R_C(T² - M², T²) = (1/M) arcsin(M/T)`. -/
theorem tendsto_descGauss {t₀ a₀ c₀ : ℝ} (hc : 0 < c₀) (hac : c₀ < a₀) (hta : a₀ < t₀) :
    ∃ T M : ℝ, M < T ∧ 0 < M ∧ Tendsto (descGaussT t₀ a₀ c₀) atTop (𝓝 T) ∧
      Tendsto (fun n => (landenAC a₀ c₀ n).1) atTop (𝓝 M) ∧
      Tendsto (fun n => (landenAC a₀ c₀ n).2) atTop (𝓝 0) ∧
      carlsonRF ((t₀ ^ 2 - a₀ ^ 2 : ℝ) : ℂ) ((t₀ ^ 2 - c₀ ^ 2 : ℝ) : ℂ) ((t₀ ^ 2 : ℝ) : ℂ) =
        TwoVariable.carlsonRC ((T ^ 2 - M ^ 2 : ℝ) : ℂ) ((T ^ 2 : ℝ) : ℂ) ∧
      carlsonRF ((t₀ ^ 2 - a₀ ^ 2 : ℝ) : ℂ) ((t₀ ^ 2 - c₀ ^ 2 : ℝ) : ℂ) ((t₀ ^ 2 : ℝ) : ℂ) =
        ((Real.arcsin (M / T) / M : ℝ) : ℂ) := by
  obtain ⟨M, hM, hMlim, hclim, -⟩ := landenAC_tendsto hc hac
  set τ := descGaussT t₀ a₀ c₀
  set aa := fun n => (landenAC a₀ c₀ n).1
  set cc := fun n => (landenAC a₀ c₀ n).2
  have hτ_succ : ∀ n, τ (n + 1) = (τ n + √(τ n ^ 2 - cc n ^ 2)) / 2 := fun n => rfl
  have haa_succ : ∀ n, aa (n + 1) = (landenACStep (aa n, cc n)).1 := fun n => by
    simp only [aa, cc]
    rw [show landenAC a₀ c₀ (n + 1) = landenACStep (landenAC a₀ c₀ n) from
      Function.iterate_succ_apply' _ _ _]
  have hgap : ∀ n, t₀ - a₀ ≤ τ n - aa n := by
    intro n; induction n with
    | zero => simp [τ, aa, descGaussT, landenAC]
    | succ n ih =>
      have hlt : aa n < τ n := by linarith
      have h := (descStep (landenAC_pos hc hac n).1 (landenAC_pos hc hac n).2 hlt).1
      rw [hτ_succ, haa_succ]
      linarith
  have haa_lt : ∀ n, aa n < τ n := fun n => by linarith [hgap n]
  have hτ_anti : Antitone τ := antitone_nat_of_succ_le fun n => by
    rw [hτ_succ]
    have : √(τ n ^ 2 - cc n ^ 2) ≤ τ n := by
      rw [Real.sqrt_le_left (by linarith [haa_lt n, (landenAC_pos hc hac n).2,
        (landenAC_pos hc hac n).1])]
      nlinarith [(landenAC_pos hc hac n).1]
    linarith
  have hlow : ∀ n, M + (t₀ - a₀) ≤ τ n := by
    intro n
    have hstep : ∀ k, aa (k + 1) ≤ aa k := fun k => by
      rw [haa_succ]
      show (aa k + √(aa k ^ 2 - cc k ^ 2)) / 2 ≤ aa k
      linarith [sqrt_sub_lt (landenAC_pos hc hac k).1 (landenAC_pos hc hac k).2]
    have hMa : M ≤ aa n := (antitone_nat_of_succ_le hstep).le_of_tendsto hMlim n
    linarith [hgap n]
  obtain ⟨T, hTlim⟩ : ∃ T, Tendsto τ atTop (𝓝 T) :=
    ⟨_, tendsto_atTop_ciInf hτ_anti ⟨M + (t₀ - a₀), fun _ ⟨n, hn⟩ => hn ▸ hlow n⟩⟩
  have hMT : M < T := by
    have := ge_of_tendsto' hTlim hlow
    linarith
  -- the invariant
  have hinv : ∀ n, carlsonRF ((τ n ^ 2 - aa n ^ 2 : ℝ) : ℂ) ((τ n ^ 2 - cc n ^ 2 : ℝ) : ℂ)
      ((τ n ^ 2 : ℝ) : ℂ) =
      carlsonRF ((t₀ ^ 2 - a₀ ^ 2 : ℝ) : ℂ) ((t₀ ^ 2 - c₀ ^ 2 : ℝ) : ℂ) ((t₀ ^ 2 : ℝ) : ℂ) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih =>
      rw [← ih, hτ_succ]
      have hstep := (descStep (landenAC_pos hc hac n).1 (landenAC_pos hc hac n).2
        (haa_lt n)).2
      simp only [aa, cc] at hstep ⊢
      rw [show landenAC a₀ c₀ (n + 1) = landenACStep (landenAC a₀ c₀ n) from
        Function.iterate_succ_apply' _ _ _]
      exact hstep
  have hT : 0 < T := by linarith
  have hlim := tendsto_carlsonRF_ofReal (show 0 < T ^ 2 - M ^ 2 by nlinarith) (pow_pos hT 2)
    (pow_pos hT 2) ((hTlim.pow 2).sub (hMlim.pow 2))
    (by simpa using (hTlim.pow 2).sub (hclim.pow 2)) (hTlim.pow 2)
  simp only [hinv] at hlim
  have hval := tendsto_nhds_unique tendsto_const_nhds hlim
  have hsl : ∀ r : ℝ, 0 < r → ((r : ℂ)) ∈ slitPlane := fun r hr => ofReal_mem_slitPlane.mpr hr
  have hRC : carlsonRF ((T ^ 2 - M ^ 2 : ℝ) : ℂ) ((T ^ 2 : ℝ) : ℂ) ((T ^ 2 : ℝ) : ℂ) =
      TwoVariable.carlsonRC ((T ^ 2 - M ^ 2 : ℝ) : ℂ) ((T ^ 2 : ℝ) : ℂ) :=
    carlsonRF_self_right (hsl _ (by nlinarith)) (hsl _ (by positivity))
  refine ⟨T, M, hMT, hM, hTlim, hMlim, hclim, by rw [hval, hRC], ?_⟩
  rw [hval, hRC, TwoVariable.carlsonRC_of_lt (by nlinarith) (by nlinarith)]
  congr 1
  rw [show T ^ 2 - (T ^ 2 - M ^ 2) = M ^ 2 by ring, Real.sqrt_sq hM.le]
  congr 1
  have hMT1 : 0 ≤ M / T := div_nonneg hM.le hT.le
  rw [Real.arccos_eq_arcsin (Real.sqrt_nonneg _),
    Real.sq_sqrt (div_nonneg (by nlinarith) (sq_nonneg T))]
  congr 1
  rw [show 1 - (T ^ 2 - M ^ 2) / T ^ 2 = (M / T) ^ 2 by field_simp; ring, Real.sqrt_sq hMT1]

end Carlson
