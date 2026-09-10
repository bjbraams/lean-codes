import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Beta
import StdSimplexMeasure.Integral
open Real MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal

lemma lintegral_Icc_rpow_mul_sub_rpow {a c s : ℝ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s) :
    ∫⁻ x in Set.Icc 0 s, ENNReal.ofReal (x ^ (a - 1) * (s - x) ^ (c - 1)) =
      ENNReal.ofReal (s ^ (a + c - 1) * beta a c) := by
  sorry
