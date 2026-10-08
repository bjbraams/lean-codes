/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.SimplexFTC
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import ToMathlib.Analysis.Calculus.IteratedDerivOpen

/-!
# Divided differences and Newton–Taylor formulas for real nodes

The real counterpart of `StdSimplexMeasure.Complex`: kernels `f : ℝ → ℂ` integrated over the
simplex spanned by real nodes, for `f` only finitely often continuously differentiable on an open
interval (Carlson's case (i) in Section 5.5). The proofs follow the complex ones, with the
fundamental theorem of calculus along segments in place of holomorphy.

## Main results

* `Real.simplexIntegral_sub`: the simplex fundamental theorem of calculus for `C¹` kernels.
* `Real.dividedDifference_sub`: **Lemma 5.5-1, case (i)**, the divided-difference recurrence,
  including coincident nodes.
* `Real.newtonTaylor_sum_add_remainder`: **Theorem 5.5-2, case (i)**, Newton's expansion with
  its exact divided-difference remainder.
* `Real.taylor_sum_add_dividedDifference_remainder`: **(5.5-8), case (i)**, Taylor's formula
  with Carlson's remainder.

The divided difference of order `n` is `F⁽ⁿ⁾(1, …, 1; z)/n!` in Carlson's notation.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §5.5.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace Real

/-- The integral of a kernel `f : ℝ → ℂ` over the simplex spanned by real nodes. The coordinate
measure has mass `1 / n!`. -/
def simplexIntegral (z : Fin (n + 1) → ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ u in Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)),
    f (∑ k, u k * z k) ∂Measure.stdSimplexMeasure

/-- Compute a simplex kernel integral using its first `n` barycentric coordinates. -/
theorem simplexIntegral_eq_integral (z : Fin (n + 1) → ℝ) (f : ℝ → ℂ) :
    simplexIntegral z f = ∫ v in posSimplexFin n 1, f (∑ k, finSimplexPoint v k * z k) :=
  integral_stdSimplex_fin _

/-- A simplex kernel integral is invariant under permutation of its nodes. -/
theorem simplexIntegral_perm (z : Fin (n + 1) → ℝ) (f : ℝ → ℂ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    simplexIntegral (z ∘ σ) f = simplexIntegral z f := by
  unfold simplexIntegral
  simp only [Function.comp_apply]
  rw [← integral_stdSimplex_comp_perm σ
    (fun u : Fin (n + 1) → ℝ => f (∑ k, u k * z (σ k)))]
  congr 1
  funext u
  congr 1
  exact Equiv.sum_comp σ (fun k => u k * z k)

/-- Coalescing all nodes evaluates the kernel, with the simplex volume factor. -/
theorem simplexIntegral_const (n : ℕ) (f : ℝ → ℂ) (w : ℝ) :
    simplexIntegral (fun _ : Fin (n + 1) => w) f = f w / (n.factorial : ℂ) := by
  unfold simplexIntegral
  have h : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)),
      f (∑ k, u k * w) = f w := by
    intro u hu
    rw [← Finset.sum_mul, hu.2, one_mul]
  rw [integral_stdSimplex_congr h, setIntegral_const]
  simp [Measure.real, Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Barycentric sums of real nodes. -/
private def nodeSum (z : Fin m → ℝ) (u : Fin m → ℝ) : ℝ := ∑ k, u k * z k

/-- Barycentric sums are continuous in their weights. -/
private lemma continuous_nodeSum (z : Fin m → ℝ) : Continuous (nodeSum z) := by
  unfold nodeSum; fun_prop

/-- Barycentric sums of nodes in a convex set stay in it. -/
private lemma nodeSum_mem {Ω : Set ℝ} (hΩ : Convex ℝ Ω) {z : Fin m → ℝ} (hz : ∀ k, z k ∈ Ω)
    {u : Fin m → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin m)) : nodeSum z u ∈ Ω :=
  hΩ.sum_mem (fun i _ => hu.1 i) hu.2 fun i _ => hz i

/-- Separate the last node of a barycentric sum. -/
private lemma nodeSum_finSimplexPoint_snoc (z : Fin n → ℝ) (x : ℝ) (v : Fin n → ℝ) :
    nodeSum (Fin.snoc z x) (finSimplexPoint v) = (∑ k, v k * z k) + (1 - ∑ k, v k) * x := by
  simp [nodeSum, finSimplexPoint, Fin.sum_univ_castSucc]

/-- Changing the last node gives a segment parametrization. -/
private lemma nodeSum_finSimplexPoint_snoc_snoc (z : Fin n → ℝ) (x y : ℝ) (v : Fin n → ℝ)
    (t : ℝ) :
    nodeSum (Fin.snoc (Fin.snoc z x) y) (finSimplexPoint (Fin.snoc v t)) =
      nodeSum (Fin.snoc z y) (finSimplexPoint v) + t * (x - y) := by
  simp [nodeSum_finSimplexPoint_snoc, Fin.sum_univ_castSucc]
  ring

/-- A continuous kernel stays continuous in simplex coordinates. -/
private lemma continuousOn_comp_finSimplex {Ω : Set ℝ} (hΩ : Convex ℝ Ω) {f : ℝ → ℂ}
    (hf : ContinuousOn f Ω) {z : Fin (n + 1) → ℝ} (hz : ∀ k, z k ∈ Ω) :
    ContinuousOn (fun v => f (nodeSum z (finSimplexPoint v))) (posSimplexFin n 1) :=
  hf.comp ((continuous_nodeSum z).comp continuous_finSimplexPoint).continuousOn
    fun _ hv => nodeSum_mem hΩ hz (finSimplexPoint_mem hv)

/-- Appending a node preserves membership in the domain. -/
private lemma snoc_mem {Ω : Set ℝ} {z : Fin n → ℝ} (hz : ∀ k, z k ∈ Ω) {x : ℝ} (hx : x ∈ Ω) :
    ∀ k, (Fin.snoc z x : Fin (n + 1) → ℝ) k ∈ Ω := by
  intro k
  refine Fin.lastCases ?_ (fun l => ?_) k
  · simpa using hx
  · simpa using hz l

/-- **The simplex fundamental theorem of calculus** for a kernel with a continuous derivative on
a real interval (Carlson's Lemma 5.5-1, case (i), in unnormalized form). -/
theorem simplexIntegral_sub {Ω : Set ℝ} (hΩ : Convex ℝ Ω) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ Ω, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' Ω)
    (z : Fin n → ℝ) (hz : ∀ k, z k ∈ Ω) {x y : ℝ} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    simplexIntegral (Fin.snoc z x) f - simplexIntegral (Fin.snoc z y) f =
      (x - y) * simplexIntegral (Fin.snoc (Fin.snoc z x) y) f' := by
  simp only [simplexIntegral_eq_integral]
  change (∫ v in posSimplexFin n 1, f (nodeSum (Fin.snoc z x) (finSimplexPoint v))) -
    (∫ v in posSimplexFin n 1, f (nodeSum (Fin.snoc z y) (finSimplexPoint v))) =
    (x - y) * ∫ v in posSimplexFin (n + 1) 1,
      f' (nodeSum (Fin.snoc (Fin.snoc z x) y) (finSimplexPoint v))
  have hfc : ContinuousOn f Ω := fun w hw => (hf w hw).continuousAt.continuousWithinAt
  have hzx := snoc_mem hz hx
  have hzy := snoc_mem hz hy
  have hzxy := snoc_mem hzx hy
  have hix := (continuousOn_comp_finSimplex hΩ hfc hzx).integrableOn_compact (μ := volume)
    (isCompact_posSimplexFin_one n)
  have hiy := (continuousOn_comp_finSimplex hΩ hfc hzy).integrableOn_compact (μ := volume)
    (isCompact_posSimplexFin_one n)
  have hid : IntegrableOn (fun v => ((x - y : ℝ) : ℂ) *
      f' (nodeSum (Fin.snoc (Fin.snoc z x) y) (finSimplexPoint v)))
      (posSimplexFin (n + 1) 1) :=
    (continuousOn_const.mul (continuousOn_comp_finSimplex hΩ hf' hzxy)).integrableOn_compact
      (isCompact_posSimplexFin_one (n + 1))
  rw [← integral_sub hix hiy, ← integral_const_mul]
  rw [show (fun v => ((x : ℂ) - y) * f' (nodeSum (Fin.snoc (Fin.snoc z x) y)
      (finSimplexPoint v))) = fun v => ((x - y : ℝ) : ℂ) * f' (nodeSum
        (Fin.snoc (Fin.snoc z x) y) (finSimplexPoint v)) by push_cast; rfl,
    integral_posSimplexFin_snoc _ hid]
  apply setIntegral_congr_fun (measurableSet_posSimplexFin _ _)
  intro v hv
  dsimp only
  let r : ℝ := 1 - ∑ k, v k
  have hr : 0 ≤ r := sub_nonneg.mpr hv.2
  let A : ℝ := nodeSum (Fin.snoc z y) (finSimplexPoint v)
  have hmem {t : ℝ} (ht : t ∈ Set.Icc 0 r) : A + t * (x - y) ∈ Ω := by
    rw [← nodeSum_finSimplexPoint_snoc_snoc]
    apply nodeSum_mem hΩ hzxy (finSimplexPoint_mem ?_)
    constructor
    · intro k
      refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [hv.1, ht.1]
    · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      dsimp [r] at ht
      linarith [ht.2]
  have hd (t : ℝ) (ht : t ∈ Set.Icc 0 r) :
      HasDerivAt (fun t : ℝ => f (A + t * (x - y)))
        (((x - y : ℝ) : ℂ) * f' (A + t * (x - y))) t := by
    have hline : HasDerivAt (fun t : ℝ => A + t * (x - y)) (x - y) t := by
      simpa using ((hasDerivAt_id t).mul_const (x - y)).const_add A
    have := (hf _ (hmem ht)).scomp t hline
    simpa [Function.comp_def, Complex.real_smul, mul_comm] using this
  have hint : IntervalIntegrable (fun t : ℝ => ((x - y : ℝ) : ℂ) * f' (A + t * (x - y)))
      volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hr]
    exact continuousOn_const.mul (hf'.comp (by fun_prop) (fun t ht => hmem ht))
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa [Set.uIcc_of_le hr] using ht)) hint
  rw [intervalIntegral.integral_of_le hr, ← integral_Icc_eq_integral_Ioc] at H
  simp only [nodeSum_finSimplexPoint_snoc_snoc]
  change f (nodeSum (Fin.snoc z x) (finSimplexPoint v)) - f A = _
  rw [H]
  simp only [zero_mul, add_zero]
  congr 2
  simp only [A, r, nodeSum_finSimplexPoint_snoc]
  ring

/-- The Hermite–Genocchi divided difference of order `n` of `f : ℝ → ℂ` at real nodes. -/
def dividedDifference (n : ℕ) (f : ℝ → ℂ) (z : Fin (n + 1) → ℝ) : ℂ :=
  simplexIntegral z (iteratedDeriv n f)

/-- Divided differences are invariant under permutations of their nodes. -/
theorem dividedDifference_perm (n : ℕ) (f : ℝ → ℂ) (z : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) : dividedDifference n f (z ∘ σ) = dividedDifference n f z :=
  simplexIntegral_perm _ _ _

/-- Exchanging the final two nodes does not change a divided difference. -/
theorem dividedDifference_snoc_snoc_comm (n : ℕ) (f : ℝ → ℂ) (z : Fin n → ℝ) (x y : ℝ) :
    dividedDifference (n + 1) f (Fin.snoc (Fin.snoc z x) y) =
      dividedDifference (n + 1) f (Fin.snoc (Fin.snoc z y) x) := by
  let i : Fin (n + 2) := Fin.castSucc (Fin.last n)
  let j : Fin (n + 2) := Fin.last (n + 1)
  let σ : Equiv.Perm (Fin (n + 2)) := Equiv.swap i j
  rw [← dividedDifference_perm (n + 1) f (Fin.snoc (Fin.snoc z x) y) σ]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [σ, i, j]
  · by_cases hkj : k = j
    · subst k
      simp [σ, i, j]
    · have hklt : k.val < n := by
        simp only [i, j, Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at hki hkj
        omega
      have hkle : k.val ≤ n := Nat.le_of_lt hklt
      simp [Function.comp_apply, σ, Equiv.swap_apply_of_ne_of_ne hki hkj,
        Fin.snoc, hklt, hkle]

/-- If all nodes coincide, the divided difference is the Taylor coefficient. -/
theorem dividedDifference_const (n : ℕ) (f : ℝ → ℂ) (w : ℝ) :
    dividedDifference n f (fun _ => w) = iteratedDeriv n f w / (n.factorial : ℂ) := by
  simp [dividedDifference, simplexIntegral_const]

/-- **Carlson's Lemma 5.5-1, case (i)**: the divided-difference recurrence
`f[z, x] - f[z, y] = (x - y) f[z, x, y]` for `f ∈ C^(n+1)` on an open interval, including
coincident nodes. -/
theorem dividedDifference_sub {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩ : Convex ℝ Ω) {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f Ω) (z : Fin n → ℝ) (hz : ∀ k, z k ∈ Ω) {x y : ℝ}
    (hx : x ∈ Ω) (hy : y ∈ Ω) :
    dividedDifference n f (Fin.snoc z x) - dividedDifference n f (Fin.snoc z y) =
      (x - y) * dividedDifference (n + 1) f (Fin.snoc (Fin.snoc z x) y) :=
  simplexIntegral_sub hΩ (fun w hw => ContDiffOn.hasDerivAt_iteratedDeriv_of_isOpen (hs := hΩo) hf
    (by norm_cast; omega) hw) (hf.continuousOn_iteratedDeriv_of_isOpen hΩo le_rfl) z hz hx hy

/-- The Newton basis polynomial `∏ᵢ (x - zᵢ)` of real nodes, as a complex number. -/
def newtonBasis (z : Fin n → ℝ) (x : ℝ) : ℂ := ∏ i, ((x - z i : ℝ) : ℂ)

/-- Appending a node adds its linear factor to the Newton basis. -/
@[simp] theorem newtonBasis_snoc (z : Fin n → ℝ) (a x : ℝ) :
    newtonBasis (Fin.snoc z a) x = newtonBasis z x * ((x - a : ℝ) : ℂ) := by
  simp [newtonBasis, Fin.prod_univ_castSucc]

/-- The nodes preceding the coefficient indexed by `n` in a finite Newton expansion. -/
def newtonPrecedingNodes {p : ℕ} (z : Fin p → ℝ) (n : Fin p) : Fin n → ℝ :=
  fun i => z ⟨i, lt_trans i.isLt n.isLt⟩

/-- The nodes through the coefficient indexed by `n` in a finite Newton expansion. -/
def newtonPrefix {p : ℕ} (z : Fin p → ℝ) (n : Fin p) : Fin (n + 1) → ℝ :=
  fun i => z ⟨i, lt_of_lt_of_le i.isLt (Nat.succ_le_iff.mpr n.isLt)⟩

/-- Taking preceding nodes commutes with dropping the final node. -/
@[simp] theorem newtonPrecedingNodes_init_castSucc (z : Fin (p + 1) → ℝ) (n : Fin p) :
    newtonPrecedingNodes z n.castSucc = newtonPrecedingNodes (Fin.init z) n := rfl

/-- Taking a prefix commutes with dropping the final node. -/
@[simp] theorem newtonPrefix_init_castSucc (z : Fin (p + 1) → ℝ) (n : Fin p) :
    newtonPrefix z n.castSucc = newtonPrefix (Fin.init z) n := rfl

/-- The nodes preceding the last coefficient are the initial nodes. -/
@[simp] theorem newtonPrecedingNodes_last (z : Fin (p + 1) → ℝ) :
    newtonPrecedingNodes z (Fin.last p) = Fin.init z := rfl

/-- The final prefix is the complete node vector. -/
@[simp] theorem newtonPrefix_last (z : Fin (p + 1) → ℝ) :
    newtonPrefix z (Fin.last p) = z := by
  funext i; rfl

/-- **Carlson's Theorem 5.5-2, case (i)** (Newton–Taylor series with remainder): for `f` that is
`p` times continuously differentiable on an open interval containing the real nodes,
`f(x) = ∑ₙ f[z₁, …, z_{n+1}] (x - z₁) ⋯ (x - zₙ) + f[z₁, …, z_p, x] (x - z₁) ⋯ (x - z_p)`. -/
theorem newtonTaylor_sum_add_remainder {Ω : Set ℝ} (hΩo : IsOpen Ω) (hΩ : Convex ℝ Ω)
    {p : ℕ} {f : ℝ → ℂ} (hf : ContDiffOn ℝ p f Ω) (z : Fin p → ℝ) (hz : ∀ k, z k ∈ Ω)
    {x : ℝ} (hx : x ∈ Ω) :
    f x = (∑ n : Fin p, dividedDifference n f (newtonPrefix z n) *
        newtonBasis (newtonPrecedingNodes z n) x) +
      dividedDifference p f (Fin.snoc z x) * newtonBasis z x := by
  induction p with
  | zero =>
    have h1 : dividedDifference 0 f (Fin.snoc z x) = f x := by
      have := dividedDifference_const 0 f x
      have hz' : (Fin.snoc z x : Fin 1 → ℝ) = fun _ => x := by
        funext i; rw [Fin.eq_zero i]; simp [Fin.snoc]
      rw [hz', this]; simp
    simp [h1, newtonBasis]
  | succ p ih =>
    let z₀ : Fin p → ℝ := Fin.init z
    let a : ℝ := z (Fin.last p)
    have hza : z = Fin.snoc z₀ a := by simp [z₀, a]
    have hz₀ : ∀ k, z₀ k ∈ Ω := fun k => hz _
    have ha : a ∈ Ω := hz _
    have hih := ih (hf.of_le (by norm_cast; omega)) z₀ hz₀
    rw [hza, hih, Fin.sum_univ_castSucc]
    simp only [newtonPrefix_init_castSucc, newtonPrecedingNodes_init_castSucc,
      newtonPrefix_last, newtonPrecedingNodes_last, Fin.init_snoc,
      Fin.val_castSucc, Fin.val_last, newtonBasis_snoc]
    have hrec := dividedDifference_sub hΩo hΩ (hf.of_le le_rfl) z₀ hz₀ hx ha
    rw [dividedDifference_snoc_snoc_comm] at hrec
    push_cast at hrec ⊢
    linear_combination newtonBasis z₀ x * hrec

/-- **Carlson (5.5-8), case (i)**: Taylor's formula with Carlson's remainder, obtained by
coalescing all nodes at `a`. -/
theorem taylor_sum_add_dividedDifference_remainder {Ω : Set ℝ} (hΩo : IsOpen Ω)
    (hΩ : Convex ℝ Ω) {f : ℝ → ℂ} {p : ℕ} (hf : ContDiffOn ℝ p f Ω) {a x : ℝ} (ha : a ∈ Ω)
    (hx : x ∈ Ω) :
    f x = (∑ n : Fin p, iteratedDeriv n.val f a / (n.val.factorial : ℂ) *
        ((x - a : ℝ) : ℂ) ^ n.val) +
      dividedDifference p f (Fin.snoc (fun _ : Fin p => a) x) * ((x - a : ℝ) : ℂ) ^ p := by
  have h := newtonTaylor_sum_add_remainder hΩo hΩ hf (fun _ : Fin p => a) (fun _ => ha) hx
  have hprefix (n : Fin p) : newtonPrefix (fun _ : Fin p => a) n = fun _ => a := by
    funext i; rfl
  simp_rw [hprefix, dividedDifference_const] at h
  simpa [newtonPrecedingNodes, newtonBasis] using h

end Real
