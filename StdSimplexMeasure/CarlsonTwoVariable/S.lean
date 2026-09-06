/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonTwoVariable.Basic
import StdSimplexMeasure.CarlsonR.Confluence

/-! # The two-variable Carlson S-function -/

open Complex Filter
open scoped Classical Topology
public noncomputable section CarlsonTwoVariable
namespace DirichletTransform.TwoVariable

/-- The natural-power two-variable R-integrals coalesce to the two-variable S-integral. -/
theorem tendsto_regRIntegral_confluent (b₀ b₁ z₀ z₁ : ℂ)
    (hb : pair b₀ b₁ ∈ mvBetaConvergent) :
    Tendsto (fun n : ℕ ↦ regRIntegral n b₀ b₁ (1 + z₀ / n) (1 + z₁ / n)) atTop
      (𝓝 (regSIntegral b₀ b₁ z₀ z₁)) := by
  convert tendsto_regCarlsonRIntegral_confluent (pair b₀ b₁) (pair z₀ z₁) hb using 1
  funext n
  congr 2

end DirichletTransform.TwoVariable
end CarlsonTwoVariable
