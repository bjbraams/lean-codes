/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CurveIndex.Homotopy
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The boundary of a parallelogram as a smooth cycle, and its index

The boundary of the parallelogram with vertices `c, c + w1, c + w1 + w2, c + w2` is realized
as a single `C^∞` closed curve, by gluing the four edges with `Real.smoothTransition`: each
edge is traversed with a reparametrization that is flat (all derivatives vanish) at its two
endpoints, so the concatenation is smooth across the corners with no case analysis on
differentiability there.

For a point `w` outside the closed parallelogram, the analytic index of the boundary about
`w` vanishes: `parallelogramLoop` is nullhomotopic within the closed (convex) parallelogram
by coning it toward the vertex `c`, a straight-line homotopy that avoids every exterior point
automatically, by convexity.

**Not proved here**: that the index equals `1` at every point of the *open* parallelogram.
Unlike the exterior case, this needs genuine information about the orientation of `w1, w2`
(swapping them reverses the traversal and negates the index) and a computation of the total
turning of the boundary about an interior point, for which the exterior nullhomotopy gives no
information. See `REMINDERS.md` for the intended strategy and the reason it was not completed.

## Main definitions

* `Complex.parallelogramFun c w1 w2`: the `C^∞` parametrization `ℝ → ℂ`.
* `Complex.parallelogramLoop c w1 w2`: the parallelogram boundary as a `Path c c`.
* `Complex.closedParallelogram c w1 w2`: the closed (filled) parallelogram.

## Main results

* `Complex.curveIndex_parallelogramLoop_eq_zero`: the index of the parallelogram boundary
  vanishes at every point outside the closed parallelogram.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Section IV.2 (polygons as chains).
-/

public noncomputable section

open Set Metric Filter
open scoped Topology unitInterval

namespace Complex

/-- The `C^∞` parametrization of the parallelogram boundary with vertices
`c, c + w1, c + w1 + w2, c + w2`, traversed once counterclockwise (for that ordering of
`w1, w2`). Each of the four terms is flat (all derivatives vanish) at its own transition,
so the sum glues smoothly across the corners. -/
def parallelogramFun (c w1 w2 : ℂ) (s : ℝ) : ℂ :=
  c + ((Real.smoothTransition (4 * s - 0) - Real.smoothTransition (4 * s - 2) : ℝ) : ℂ) * w1
    + ((Real.smoothTransition (4 * s - 1) - Real.smoothTransition (4 * s - 3) : ℝ) : ℂ) * w2

/-- `parallelogramFun` is `C^∞` on all of `ℝ`. -/
theorem contDiff_parallelogramFun (c w1 w2 : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (parallelogramFun c w1 w2) := by
  unfold parallelogramFun
  have hst : ∀ k : ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Real.smoothTransition (4 * s - k)) :=
    fun k => Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hor : ∀ k1 k2 : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => ((Real.smoothTransition (4 * s - k1)
        - Real.smoothTransition (4 * s - k2) : ℝ) : ℂ)) :=
    fun k1 k2 => Complex.ofRealCLM.contDiff.comp ((hst k1).sub (hst k2))
  exact (contDiff_const.add ((hor 0 2).mul contDiff_const)).add ((hor 1 3).mul contDiff_const)

/-- `parallelogramFun` is continuous, as it is `C^∞`. -/
theorem continuous_parallelogramFun (c w1 w2 : ℂ) : Continuous (parallelogramFun c w1 w2) :=
  (contDiff_parallelogramFun c w1 w2).continuous

/-- `parallelogramFun` is unaffected by clamping its argument into `[0, 1]`: it already takes
the value at `0` for all `s ≤ 0` and the value at `1` for all `s ≥ 1`. -/
theorem parallelogramFun_projIcc (c w1 w2 : ℂ) (s : ℝ) :
    parallelogramFun c w1 w2 (projIcc (0 : ℝ) 1 zero_le_one s) = parallelogramFun c w1 w2 s := by
  by_cases h0 : (0 : ℝ) ≤ s
  · by_cases h1 : s ≤ (1 : ℝ)
    · rw [projIcc_of_mem _ ⟨h0, h1⟩]
    · have h1' : (1 : ℝ) < s := not_le.mp h1
      rw [projIcc_of_right_le zero_le_one h1'.le]
      unfold parallelogramFun
      congr 2
      · congr 1
        · have e1 : (4 : ℝ) * 1 - 0 = 4 := by ring
          have e2 : (4 : ℝ) * 1 - 2 = 2 := by ring
          have e3 : (4 : ℝ) * s - 0 = 4 * s := by ring
          have e4 : (4 : ℝ) * s - 2 = 4 * s - 2 := by ring
          rw [e1, e2, e3, e4, Real.smoothTransition.one_of_one_le (by norm_num),
            Real.smoothTransition.one_of_one_le (by norm_num),
            Real.smoothTransition.one_of_one_le (by linarith),
            Real.smoothTransition.one_of_one_le (by linarith)]
      · congr 1
        · have e1 : (4 : ℝ) * 1 - 1 = 3 := by ring
          have e2 : (4 : ℝ) * 1 - 3 = 1 := by ring
          rw [e1, e2, Real.smoothTransition.one_of_one_le (by norm_num),
            Real.smoothTransition.one_of_one_le (by norm_num),
            Real.smoothTransition.one_of_one_le (by linarith),
            Real.smoothTransition.one_of_one_le (by linarith)]
  · have h0' : s < (0 : ℝ) := not_le.mp h0
    rw [projIcc_of_le_left zero_le_one h0'.le]
    unfold parallelogramFun
    congr 2
    · congr 1
      · rw [Real.smoothTransition.zero_of_nonpos (by norm_num : (4 : ℝ) * 0 - 0 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by norm_num : (4 : ℝ) * 0 - 2 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by linarith : (4 : ℝ) * s - 0 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by linarith : (4 : ℝ) * s - 2 ≤ 0)]
    · congr 1
      · rw [Real.smoothTransition.zero_of_nonpos (by norm_num : (4 : ℝ) * 0 - 1 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by norm_num : (4 : ℝ) * 0 - 3 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by linarith : (4 : ℝ) * s - 1 ≤ 0),
          Real.smoothTransition.zero_of_nonpos (by linarith : (4 : ℝ) * s - 3 ≤ 0)]

/-- The value of `parallelogramFun` at the base vertex. -/
theorem parallelogramFun_zero (c w1 w2 : ℂ) : parallelogramFun c w1 w2 0 = c := by
  unfold parallelogramFun
  norm_num
  rw [Real.smoothTransition.zero_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by norm_num : (-3 : ℝ) ≤ 0)]
  simp

/-- The value of `parallelogramFun` at the second vertex. -/
theorem parallelogramFun_quarter (c w1 w2 : ℂ) : parallelogramFun c w1 w2 (1 / 4) = c + w1 := by
  unfold parallelogramFun
  have e1 : (4 : ℝ) * (1 / 4) - 0 = 1 := by ring
  have e2 : (4 : ℝ) * (1 / 4) - 2 = -1 := by ring
  have e3 : (4 : ℝ) * (1 / 4) - 1 = 0 := by ring
  have e4 : (4 : ℝ) * (1 / 4) - 3 = -2 := by ring
  rw [e1, e2, e3, e4, Real.smoothTransition.one_of_one_le (le_refl 1),
    Real.smoothTransition.zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0),
    Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)),
    Real.smoothTransition.zero_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0)]
  push_cast
  ring

/-- The value of `parallelogramFun` at the third vertex. -/
theorem parallelogramFun_half (c w1 w2 : ℂ) :
    parallelogramFun c w1 w2 (1 / 2) = c + w1 + w2 := by
  unfold parallelogramFun
  have e1 : (4 : ℝ) * (1 / 2) - 0 = 2 := by ring
  have e2 : (4 : ℝ) * (1 / 2) - 2 = 0 := by ring
  have e3 : (4 : ℝ) * (1 / 2) - 1 = 1 := by ring
  have e4 : (4 : ℝ) * (1 / 2) - 3 = -1 := by ring
  rw [e1, e2, e3, e4, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2),
    Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)),
    Real.smoothTransition.one_of_one_le (le_refl 1),
    Real.smoothTransition.zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)]
  push_cast
  ring

/-- The value of `parallelogramFun` at the fourth vertex. -/
theorem parallelogramFun_three_quarter (c w1 w2 : ℂ) :
    parallelogramFun c w1 w2 (3 / 4) = c + w2 := by
  unfold parallelogramFun
  have e1 : (4 : ℝ) * (3 / 4) - 0 = 3 := by ring
  have e2 : (4 : ℝ) * (3 / 4) - 2 = 1 := by ring
  have e3 : (4 : ℝ) * (3 / 4) - 1 = 2 := by ring
  have e4 : (4 : ℝ) * (3 / 4) - 3 = 0 := by ring
  rw [e1, e2, e3, e4, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 3),
    Real.smoothTransition.one_of_one_le (le_refl 1),
    Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2),
    Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))]
  push_cast
  ring

/-- The value of `parallelogramFun` back at the base vertex, closing the loop. -/
theorem parallelogramFun_one (c w1 w2 : ℂ) : parallelogramFun c w1 w2 1 = c := by
  unfold parallelogramFun
  have e1 : (4 : ℝ) * 1 - 0 = 4 := by ring
  have e2 : (4 : ℝ) * 1 - 2 = 2 := by ring
  have e3 : (4 : ℝ) * 1 - 1 = 3 := by ring
  have e4 : (4 : ℝ) * 1 - 3 = 1 := by ring
  rw [e1, e2, e3, e4, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 4),
    Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2),
    Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 3),
    Real.smoothTransition.one_of_one_le (le_refl 1)]
  push_cast
  ring

/-- The parallelogram boundary with vertices `c, c + w1, c + w1 + w2, c + w2`, as a `C^∞`
closed path. -/
def parallelogramLoop (c w1 w2 : ℂ) : Path c c where
  toFun t := parallelogramFun c w1 w2 (t : ℝ)
  continuous_toFun := (contDiff_parallelogramFun c w1 w2).continuous.comp continuous_subtype_val
  source' := parallelogramFun_zero c w1 w2
  target' := parallelogramFun_one c w1 w2

/-- The extension of the parallelogram loop to `ℝ` is `parallelogramFun` itself, since the
latter already takes its boundary values outside `[0, 1]`. -/
theorem parallelogramLoop_extend (c w1 w2 : ℂ) :
    (parallelogramLoop c w1 w2).extend = parallelogramFun c w1 w2 := by
  funext s
  exact parallelogramFun_projIcc c w1 w2 s

/-- The parallelogram loop is `C^1` (indeed `C^∞`) on `[0, 1]`. -/
theorem contDiffOn_parallelogramLoop_extend (c w1 w2 : ℂ) :
    ContDiffOn ℝ 1 (parallelogramLoop c w1 w2).extend I := by
  rw [parallelogramLoop_extend]
  exact ((contDiff_parallelogramFun c w1 w2).of_le (by norm_num)).contDiffOn

/-- The closed (filled) parallelogram with vertices `c, c + w1, c + w1 + w2, c + w2`. -/
def closedParallelogram (c w1 w2 : ℂ) : Set ℂ :=
  (fun p : ℝ × ℝ => c + (p.1 : ℂ) * w1 + (p.2 : ℂ) * w2) '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)

/-- The parallelogram loop stays within the closed parallelogram at every parameter, not only
at the vertices. -/
theorem parallelogramFun_mem_closedParallelogram (c w1 w2 : ℂ) (s : ℝ) :
    parallelogramFun c w1 w2 s ∈ closedParallelogram c w1 w2 := by
  refine ⟨(Real.smoothTransition (4 * s - 0) - Real.smoothTransition (4 * s - 2),
    Real.smoothTransition (4 * s - 1) - Real.smoothTransition (4 * s - 3)), ⟨⟨?_, ?_⟩, ?_, ?_⟩,
    rfl⟩
  · have h1 := Real.smoothTransition.monotone (show 4 * s - 2 ≤ 4 * s - 0 by linarith)
    linarith
  · have h1 := Real.smoothTransition.le_one (4 * s - 0)
    have h2 := Real.smoothTransition.nonneg (4 * s - 2)
    linarith
  · have h1 := Real.smoothTransition.monotone (show 4 * s - 3 ≤ 4 * s - 1 by linarith)
    linarith
  · have h1 := Real.smoothTransition.le_one (4 * s - 1)
    have h2 := Real.smoothTransition.nonneg (4 * s - 3)
    linarith

/-- Coning a point of the closed parallelogram toward the vertex `c` stays inside it. -/
theorem cone_mem_closedParallelogram {c w1 w2 z : ℂ} (hz : z ∈ closedParallelogram c w1 w2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - (t : ℂ)) * z + (t : ℂ) * c ∈ closedParallelogram c w1 w2 := by
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ := hz
  simp only at hxy
  refine ⟨((1 - t) * x, (1 - t) * y), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact mul_nonneg (by linarith) hx.1
  · nlinarith [hx.2, hx.1]
  · exact mul_nonneg (by linarith) hy.1
  · nlinarith [hy.2, hy.1]
  · simp only [← hxy]
    push_cast
    ring

/-- The raw underlying function of the coning homotopy from the parallelogram loop to the
constant loop at `c`. -/
def coningToFun (c w1 w2 : ℂ) : I × I → ℂ :=
  fun p => (1 - (p.1 : ℂ)) * parallelogramFun c w1 w2 (p.2 : ℝ) + (p.1 : ℂ) * c

/-- The coning homotopy's underlying function is continuous. -/
theorem continuous_coningToFun (c w1 w2 : ℂ) : Continuous (coningToFun c w1 w2) := by
  unfold coningToFun
  have h1 : Continuous (fun p : I × I => (1 - (p.1 : ℂ))) := by fun_prop
  have h2 : Continuous (fun p : I × I => parallelogramFun c w1 w2 (p.2 : ℝ)) :=
    (contDiff_parallelogramFun c w1 w2).continuous.comp (by fun_prop)
  have h3 : Continuous (fun p : I × I => (p.1 : ℂ)) := by fun_prop
  exact (h1.mul h2).add (h3.mul continuous_const)

/-- Every point of the coning homotopy lies in the closed parallelogram. -/
theorem coningToFun_mem_closedParallelogram (c w1 w2 : ℂ) (p : I × I) :
    coningToFun c w1 w2 p ∈ closedParallelogram c w1 w2 :=
  cone_mem_closedParallelogram (parallelogramFun_mem_closedParallelogram c w1 w2 (p.2 : ℝ))
    p.1.2.1 p.1.2.2

/-- The coning homotopy from the parallelogram loop to the constant loop at `c`, straight-line
toward the vertex `c`. Since `c` and the loop both lie in the closed convex parallelogram, so
does the whole homotopy. -/
def coningHomotopy (c w1 w2 : ℂ) : (parallelogramLoop c w1 w2).Homotopy (Path.refl c) where
  toFun := coningToFun c w1 w2
  continuous_toFun := continuous_coningToFun c w1 w2
  map_zero_left x := by simp [coningToFun, parallelogramLoop]
  map_one_left x := by simp [coningToFun]
  prop' t x hx := by
    rcases hx with hx | hx
    · simp only [coningToFun, hx, parallelogramLoop]
      norm_num [parallelogramFun_zero]
      ring
    · simp only [Set.mem_singleton_iff] at hx
      simp only [coningToFun, hx, parallelogramLoop]
      norm_num [parallelogramFun_one]
      ring

/-- **The index of the parallelogram boundary vanishes outside the closed parallelogram.** -/
theorem curveIndex_parallelogramLoop_eq_zero {c w1 w2 w : ℂ}
    (hw : w ∉ closedParallelogram c w1 w2) :
    curveIndex (parallelogramLoop c w1 w2) w = 0 :=
  curveIndex_eq_zero_of_continuous_nullhomotopy (coningHomotopy c w1 w2)
    (fun p hp => hw (hp ▸ coningToFun_mem_closedParallelogram c w1 w2 p))
    (contDiffOn_parallelogramLoop_extend c w1 w2)

end Complex

end
