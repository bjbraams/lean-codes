/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.IntegralEvaluation
public import Carlson.R.IntegerParameters
public import Carlson.R.Laplace
public import Carlson.RPolynomial.Coefficients
public import Dirichlet.Transform.Euler

/-!
# The Dirichlet average of `(u·x)^{-a} (u·y)^{-a'}` (Carlson's Exercise 8.1-6)

For `X = u·x`, `Y = u·y` in the right half-plane, `X^{-a} Y^{-a'}` is the two-parameter
average `Γ(a + a') R̃_{-(a+a')}(a, a'; X, Y)`. Exchanging this average with the Dirichlet
average over `u` (Fubini on the product of the two simplices), the inner average is
`R_{-∑b}(b; v₀x + v₁y) = ∏ (v₀xᵢ + v₁yᵢ)^{-bᵢ}`, and the outer one is Formula 8.1-1 on the
segment from `y` to `x`. This gives the identity for `re a, re a' > 0`; both sides are entire in
`a` (with `a' = ∑ bᵢ - a`), which extends it to all complex `a`.

## Main results

* `Carlson.complexDirichletIntegral_cpow_mul_cpow`: the identity for `re a, re a' > 0`.
* `Carlson.complexDirichletIntegral_cpow_mul_cpow_of_sum`: Exercise 8.1-6 for all complex `a`.
* `Carlson.prod_cpow_mul_carlsonR_div_comm`: the second form `∏ xᵢ^{-bᵢ} R_{-a'}(b; y/x)`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.1.
-/

open Dirichlet
open Complex MeasureTheory Set

@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*} [Fintype ι]

/-- The affine form of a convex combination of two node vectors. -/
private theorem carlsonAffineForm_pair_combination (x y : ι → ℂ) (u : ι → ℝ) (v : Fin 2 → ℝ) :
    carlsonAffineForm (fun i => (v 0 : ℂ) * x i + (v 1 : ℂ) * y i) u =
      carlsonAffineForm ![carlsonAffineForm x u, carlsonAffineForm y u] v := by
  simp only [carlsonAffineForm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring

omit [Fintype ι] in
/-- A convex combination of two right-half-plane node vectors lies in the right half-plane. -/
private theorem pair_combination_mem {x y : ι → ℂ} (hx : x ∈ carlsonRVariableDomain)
    (hy : y ∈ carlsonRVariableDomain) {v : Fin 2 → ℝ}
    (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :
    (fun i => (v 0 : ℂ) * x i + (v 1 : ℂ) * y i) ∈ carlsonRVariableDomain := by
  intro i
  have h := carlsonAffineForm_mem_rightHalfPlane (z := ![x i, y i]) (fun j => by
    fin_cases j
    · exact hx i
    · exact hy i) hv
  simpa [carlsonAffineForm, Fin.sum_univ_two] using h

/-- `X^{-a} Y^{-a'}` as a two-parameter Dirichlet average of `(v₀X + v₁Y)^{-(a+a')}`. -/
private theorem cpow_mul_cpow_eq_regDirichletIntegral {a a' X Y : ℂ} (ha : 0 < a.re)
    (ha' : 0 < a'.re) (hX : 0 < X.re) (hY : 0 < Y.re) :
    X ^ (-a) * Y ^ (-a') = Gamma (a + a') *
      regDirichletIntegral ![a, a'] (fun v => carlsonAffineForm ![X, Y] v ^ (-(a + a'))) := by
  have hz : ![X, Y] ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · exact hX
    · exact hY
  have hb : ![a, a'] ∈ mvBetaConvergent := by
    intro i; fin_cases i
    · exact ha
    · exact ha'
  have h1 := regCarlsonR_neg_sum_sub_nat 0 ![a, a'] (carlsonRVariableDomain_subset_slitDomain hz)
  have h2 := regCarlsonR_eq_regCarlsonRIntegral (-(∑ i, ![a, a'] i) - (0 : ℕ)) hb hz
  rw [h1] at h2
  simp only [regCarlsonRPolynomial_zero, Fin.sum_univ_two, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_zero,
    sub_zero] at h2
  rw [regCarlsonRIntegral, regCarlsonDirichletAverage] at h2
  have hG : Gamma (a + a') ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [← h2]
  field_simp

/-- The Dirichlet average of `(u·w)^{-∑ b}` is `∏ wᵢ^{-bᵢ}`, in regularized form. -/
private theorem regDirichletIntegral_cpow_neg_sum {b w : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hw : w ∈ carlsonRVariableDomain) :
    regDirichletIntegral b (fun u => carlsonAffineForm w u ^ (-(∑ i, b i))) =
      (∏ i, w i ^ (-b i)) * (Gamma (∑ i, b i))⁻¹ := by
  have h1 := regCarlsonR_neg_sum_sub_nat 0 b (carlsonRVariableDomain_subset_slitDomain hw)
  have h2 := regCarlsonR_eq_regCarlsonRIntegral (-(∑ i, b i) - (0 : ℕ)) hb hw
  rw [h1] at h2
  simp only [regCarlsonRPolynomial_zero, Nat.cast_zero, sub_zero] at h2
  rw [regCarlsonRIntegral, regCarlsonDirichletAverage] at h2
  exact h2.symm

/-- The two-parameter average of `∏ (v₀ xᵢ + v₁ yᵢ)^{-bᵢ}` is `∏ yᵢ^{-bᵢ} R̃_{-a}(b; x/y)`. -/
private theorem regDirichletIntegral_prod_pair_combination {a a' : ℂ} {b x y : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a + a' = ∑ i, b i)
    (hx : x ∈ carlsonRVariableDomain) (hy : y ∈ carlsonRVariableDomain) :
    regDirichletIntegral ![a, a']
        (fun v => ∏ i, ((v 0 : ℂ) * x i + (v 1 : ℂ) * y i) ^ (-b i)) =
      (∏ i, y i ^ (-b i)) * regCarlsonR (-a) b (fun i => x i / y i) := by
  set f : ℝ → ℂ := fun s => ∏ i, ((s : ℂ) * x i + (1 - s : ℂ) * y i) ^ (-b i)
  have hcongr : regDirichletIntegral ![a, a']
      (fun v => ∏ i, ((v 0 : ℂ) * x i + (v 1 : ℂ) * y i) ^ (-b i)) =
      regDirichletIntegral ![a, a'] (fun v => f (v 0)) := by
    unfold regDirichletIntegral
    refine setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ _).measurableSet
      fun v hv => ?_
    have h1 : v 1 = 1 - v 0 := by
      have := hv.2; simp [Fin.sum_univ_two] at this; linarith
    simp only [f, h1, ofReal_sub, ofReal_one]
  rw [hcongr, regDirichletIntegral_fin_two, regEulerIntegral]
  have hseg : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1,
      y i + (x i - y i) * ((0 : ℂ) + u * (1 - 0)) ∈ slitPlane := by
    intro i u hu
    apply carlsonRightHalfPlane_subset_slitPlane
    have h := pair_combination_mem hx hy (v := ![u, 1 - u])
      ⟨fun j => by fin_cases j <;> simp [hu.1, hu.2], by simp⟩ i
    convert h using 1
    simp; ring
  have H := integral_segment_eq_regCarlsonR (z := y) (w := fun i => x i - y i) ha ha' hsum
    (x := 0) (y := 1) zero_ne_one hseg
  simp only [sub_zero, zero_add, one_mul, mul_one, mul_zero, add_zero, one_cpow] at H
  have hn : (fun i => (y i + (x i - y i)) / y i) = fun i => x i / y i := by
    funext i; ring_nf
  rw [hn] at H
  have hG : Gamma a * Gamma a' ≠ 0 :=
    mul_ne_zero (Gamma_ne_zero_of_re_pos ha) (Gamma_ne_zero_of_re_pos ha')
  rw [show (∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) * f u) =
      Gamma a * Gamma a' * (∏ i, y i ^ (-b i)) * regCarlsonR (-a) b (fun i => x i / y i) by
    rw [← H]
    refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    simp only [f]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    ring_nf]
  rw [inv_mul_eq_div, mul_assoc, mul_comm, mul_div_cancel_right₀ _ hG]

/-- The product kernel: both Dirichlet densities times `(u·(v₀x + v₁y))^{-c}`. -/
private def averageKernel (a a' : ℂ) (b x y : ι → ℂ) (p : (ι → ℝ) × (Fin 2 → ℝ)) : ℂ :=
  regDirichletDensity b p.1 * (regDirichletDensity ![a, a'] p.2 *
    carlsonAffineForm (fun i => (p.2 0 : ℂ) * x i + (p.2 1 : ℂ) * y i) p.1 ^ (-(a + a')))

/-- The product of the two simplex measures. -/
private abbrev averageMeasure (ι : Type*) [Fintype ι] : Measure ((ι → ℝ) × (Fin 2 → ℝ)) :=
  (Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)).prod
    (Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)))

/-- The product kernel is integrable. -/
private theorem integrable_averageKernel {a a' : ℂ} {b x y : ι → ℂ} (ha : 0 < a.re)
    (ha' : 0 < a'.re) (hb : b ∈ mvBetaConvergent) (hx : x ∈ carlsonRVariableDomain)
    (hy : y ∈ carlsonRVariableDomain) :
    Integrable (averageKernel a a' b x y) (averageMeasure ι) := by
  set S := Convexity.StdSimplex.coordinateSet ℝ ι ×ˢ
    Convexity.StdSimplex.coordinateSet ℝ (Fin 2)
  set g : (ι → ℝ) × (Fin 2 → ℝ) → ℂ := fun p =>
    carlsonAffineForm (fun i => (p.2 0 : ℂ) * x i + (p.2 1 : ℂ) * y i) p.1 ^ (-(a + a'))
  have hS : IsCompact S := (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).prod
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 2))
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hg : ContinuousOn g S := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    have hbase : ContinuousAt (fun q : (ι → ℝ) × (Fin 2 → ℝ) =>
        carlsonAffineForm (fun i => (q.2 0 : ℂ) * x i + (q.2 1 : ℂ) * y i) q.1) p := by
      unfold carlsonAffineForm
      fun_prop
    exact (continuousAt_cpow_const (carlsonRightHalfPlane_subset_slitPlane
      (carlsonAffineForm_mem_rightHalfPlane (pair_combination_mem hx hy hp.2) hp.1))).comp_of_eq
      hbase rfl
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hg
  have hab : ![a, a'] ∈ mvBetaConvergent := by
    intro i; fin_cases i
    · exact ha
    · exact ha'
  have hd : Integrable (fun p : (ι → ℝ) × (Fin 2 → ℝ) =>
      regDirichletDensity b p.1 * regDirichletDensity ![a, a'] p.2) (averageMeasure ι) :=
    (integrableOn_regDirichletDensity b hb).mul_prod (integrableOn_regDirichletDensity _ hab)
  have hmeas : ∀ᵐ p ∂(averageMeasure ι), p ∈ S := by
    unfold averageMeasure
    rw [Measure.prod_restrict]
    exact ae_restrict_mem hSm
  have hgm : AEStronglyMeasurable g (averageMeasure ι) := by
    unfold averageMeasure
    rw [Measure.prod_restrict]
    exact hg.aestronglyMeasurable hSm
  have := hd.mul_bdd hgm (hmeas.mono fun p hp => hC p hp)
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [averageKernel, g]
  ring

/-- **Exercise 8.1-6** in the strip `re a, re a' > 0`, for `b`, `x`, `y` with components in the
right half-plane and `a + a' = ∑ bᵢ`: `∫_E (u·x)^{-a} (u·y)^{-a'} dμ_b(u) =
∏ yᵢ^{-bᵢ} R_{-a}(b; x/y)`. -/
theorem complexDirichletIntegral_cpow_mul_cpow {a a' : ℂ} {b x y : ι → ℂ} (ha : 0 < a.re)
    (ha' : 0 < a'.re) (hsum : a + a' = ∑ i, b i) (hb : b ∈ mvBetaConvergent)
    (hx : x ∈ carlsonRVariableDomain) (hy : y ∈ carlsonRVariableDomain) :
    complexDirichletIntegral b
        (fun u => carlsonAffineForm x u ^ (-a) * carlsonAffineForm y u ^ (-a')) =
      (∏ i, y i ^ (-b i)) * carlsonR (-a) b (fun i => x i / y i) := by
  rw [complexDirichletIntegral_eq_Gamma_mul, carlsonR, mul_left_comm]
  congr 1
  have hswap := integral_integral_swap (f := fun u v => averageKernel a a' b x y (u, v))
    (integrable_averageKernel ha ha' hb hx hy)
  have hleft : regDirichletIntegral b
      (fun u => carlsonAffineForm x u ^ (-a) * carlsonAffineForm y u ^ (-a')) =
      Gamma (a + a') * ∫ u, ∫ v, averageKernel a a' b x y (u, v)
        ∂(Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)))
        ∂(Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)) := by
    unfold regDirichletIntegral
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
      fun u hu => ?_
    simp only
    rw [cpow_mul_cpow_eq_regDirichletIntegral ha ha'
      (carlsonAffineForm_mem_rightHalfPlane hx hu) (carlsonAffineForm_mem_rightHalfPlane hy hu)]
    unfold regDirichletIntegral averageKernel
    simp_rw [carlsonAffineForm_pair_combination]
    rw [integral_const_mul]
    ring
  have hright : (∫ v, ∫ u, averageKernel a a' b x y (u, v)
        ∂(Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι))
        ∂(Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)))) =
      (Gamma (∑ i, b i))⁻¹ * regDirichletIntegral ![a, a']
        (fun v => ∏ i, ((v 0 : ℂ) * x i + (v 1 : ℂ) * y i) ^ (-b i)) := by
    unfold regDirichletIntegral
    rw [← integral_const_mul]
    refine setIntegral_congr_fun
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ (Fin 2)).measurableSet fun v hv => ?_
    have h := regDirichletIntegral_cpow_neg_sum hb (pair_combination_mem hx hy hv)
    rw [← hsum] at h
    unfold regDirichletIntegral at h
    simp only [averageKernel]
    have : (fun u => regDirichletDensity b u * (regDirichletDensity ![a, a'] v *
        carlsonAffineForm (fun i => (v 0 : ℂ) * x i + (v 1 : ℂ) * y i) u ^ (-(a + a')))) =
        fun u => regDirichletDensity ![a, a'] v * (regDirichletDensity b u *
          carlsonAffineForm (fun i => (v 0 : ℂ) * x i + (v 1 : ℂ) * y i) u ^ (-(a + a'))) := by
      funext u; ring
    rw [this, integral_const_mul, h, hsum]
    ring
  rw [hleft, hswap, hright, regDirichletIntegral_prod_pair_combination ha ha' hsum hx hy, hsum]
  have hG : Gamma (∑ i, b i) ≠ 0 := Gamma_ne_zero_of_re_pos (by rw [← hsum]; simp; linarith)
  field_simp

omit [Fintype ι] in
/-- The quotient of two right-half-plane numbers lies in the slit plane. -/
private theorem div_mem_slitPlane_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    x / y ∈ slitPlane := by
  rw [mem_slitPlane_iff_not_le_zero]
  intro ⟨hre, him⟩
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have hxy : x = (x / y) * y := by field_simp
  have : (x / y) = ((x / y).re : ℂ) := Complex.ext (by simp) (by simpa using him)
  rw [this] at hxy
  have := congrArg re hxy
  simp at this
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hre hy.le]

/-- **Exercise 8.1-6**: for `a ∈ ℂ` and `b`, `x`, `y` with components in the right half-plane,
`∫_E (u·x)^{-a} (u·y)^{-a'} dμ_b(u) = ∏ yᵢ^{-bᵢ} R_{-a}(b; x/y)`, where `a' = ∑ bᵢ - a`. The
left side is entire in `a`, and the identity extends from the strip
`complexDirichletIntegral_cpow_mul_cpow` by analytic continuation. -/
theorem complexDirichletIntegral_cpow_mul_cpow_of_sum [Nonempty ι] {a a' : ℂ} {b x y : ι → ℂ}
    (hsum : a + a' = ∑ i, b i) (hb : b ∈ mvBetaConvergent)
    (hx : x ∈ carlsonRVariableDomain) (hy : y ∈ carlsonRVariableDomain) :
    complexDirichletIntegral b
        (fun u => carlsonAffineForm x u ^ (-a) * carlsonAffineForm y u ^ (-a')) =
      (∏ i, y i ^ (-b i)) * carlsonR (-a) b (fun i => x i / y i) := by
  set c := ∑ i, b i
  have hc : 0 < c.re := by
    simp only [c, re_sum]
    exact Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  obtain rfl : a' = c - a := by rw [← hsum]; ring
  -- the left side is entire in `a`
  set W : Set ((Fin 1 → ℂ) × (ι → ℂ)) :=
    {p | (∑ i, p.2 i * x i) ∈ slitPlane ∧ (∑ i, p.2 i * y i) ∈ slitPlane}
  set H : (Fin 1 → ℂ) × (ι → ℂ) → ℂ := fun p =>
    (∑ i, p.2 i * x i) ^ (-p.1 0) * (∑ i, p.2 i * y i) ^ (-(c - p.1 0))
  have hH : AnalyticOnNhd ℂ H W := by
    intro p hp
    have hco : ∀ i, AnalyticAt ℂ (fun p : (Fin 1 → ℂ) × (ι → ℂ) => p.2 i) p := fun i =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).comp
        (ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) (ι → ℂ))).analyticAt p
    have hX : AnalyticAt ℂ (fun p : (Fin 1 → ℂ) × (ι → ℂ) => ∑ i, p.2 i * x i) p :=
      Finset.analyticAt_fun_sum _ fun i _ => (hco i).fun_mul analyticAt_const
    have hY : AnalyticAt ℂ (fun p : (Fin 1 → ℂ) × (ι → ℂ) => ∑ i, p.2 i * y i) p :=
      Finset.analyticAt_fun_sum _ fun i _ => (hco i).fun_mul analyticAt_const
    have h0 : AnalyticAt ℂ (fun p : (Fin 1 → ℂ) × (ι → ℂ) => p.1 0) p :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).comp
        (ContinuousLinearMap.fst ℂ (Fin 1 → ℂ) (ι → ℂ))).analyticAt p
    exact (hX.cpow h0.neg hp.1).fun_mul (hY.cpow (analyticAt_const.sub h0).neg hp.2)
  have hW : ∀ z ∈ (univ : Set (Fin 1 → ℂ)), ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ W := fun z _ u hu =>
    ⟨carlsonRightHalfPlane_subset_slitPlane (carlsonAffineForm_mem_rightHalfPlane hx hu),
      carlsonRightHalfPlane_subset_slitPlane (carlsonAffineForm_mem_rightHalfPlane hy hu)⟩
  have hL := analyticOnNhd_regDirichletIntegral_kernel isOpen_univ hH hW hb
  set Φ : ℂ → ℂ := fun s => complexDirichletIntegral b
    (fun u => carlsonAffineForm x u ^ (-s) * carlsonAffineForm y u ^ (-(c - s)))
  have hΦ : AnalyticOnNhd ℂ Φ univ := by
    refine fun s _ => Differentiable.analyticAt (fun s => ?_) s
    have hcomp := ((hL (fun _ => s) (mem_univ _)).comp
      (analyticAt_pi_iff.mpr (fun _ => analyticAt_id) :
        AnalyticAt ℂ (fun s : ℂ => (fun _ : Fin 1 => s)) s)).differentiableAt
    have := hcomp.const_mul (Gamma c)
    simpa [Φ, complexDirichletIntegral_eq_Gamma_mul, H, carlsonAffineForm, Function.comp_def]
      using this
  -- the right side is entire in `a`
  have hslit : (fun i => x i / y i) ∈ carlsonRSlitDomain := fun i =>
    div_mem_slitPlane_of_re_pos (hx i) (hy i)
  set Ψ : ℂ → ℂ := fun s => (∏ i, y i ^ (-b i)) * carlsonR (-s) b (fun i => x i / y i)
  have hΨ : AnalyticOnNhd ℂ Ψ univ := by
    refine fun s _ => Differentiable.analyticAt (fun s => ?_) s
    have h := analyticAt_regCarlsonR_comp (t := fun s : ℂ => -s) (b := fun _ => b)
      (z := fun _ => fun i => x i / y i) (p := s) analyticAt_id.neg analyticAt_const
      analyticAt_const hslit
    simpa [Ψ, carlsonR, mul_assoc] using
      ((h.differentiableAt.const_mul (Gamma c)).const_mul (∏ i, y i ^ (-b i)))
  -- agreement on the strip
  have hstrip : Φ =ᶠ[nhds (c / 2)] Ψ := by
    have hopen : IsOpen {s : ℂ | 0 < s.re ∧ 0 < (c - s).re} :=
      (isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_const (continuous_re.comp (continuous_const.sub continuous_id)))
    filter_upwards [hopen.mem_nhds ⟨by simp; linarith, by simp; linarith⟩] with s hs
    exact complexDirichletIntegral_cpow_mul_cpow hs.1 hs.2 (by ring) hb hx hy
  exact hΦ.eqOn_of_preconnected_of_eventuallyEq hΨ isPreconnected_univ (mem_univ _) hstrip
    (mem_univ a)

/-- **Exercise 8.1-6**, both forms: `∏ yᵢ^{-bᵢ} R_{-a}(b; x/y) = ∏ xᵢ^{-bᵢ} R_{-a'}(b; y/x)` when
`a + a' = ∑ bᵢ`, both being the Dirichlet average of `(u·x)^{-a} (u·y)^{-a'}`. -/
theorem prod_cpow_mul_carlsonR_div_comm [Nonempty ι] {a a' : ℂ} {b x y : ι → ℂ}
    (hsum : a + a' = ∑ i, b i) (hb : b ∈ mvBetaConvergent)
    (hx : x ∈ carlsonRVariableDomain) (hy : y ∈ carlsonRVariableDomain) :
    (∏ i, y i ^ (-b i)) * carlsonR (-a) b (fun i => x i / y i) =
      (∏ i, x i ^ (-b i)) * carlsonR (-a') b (fun i => y i / x i) := by
  rw [← complexDirichletIntegral_cpow_mul_cpow_of_sum hsum hb hx hy,
    ← complexDirichletIntegral_cpow_mul_cpow_of_sum (by rw [add_comm]; exact hsum) hb hy hx]
  simp_rw [mul_comm]

end Carlson
