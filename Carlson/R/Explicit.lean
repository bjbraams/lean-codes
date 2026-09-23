/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Exponent
public import Carlson.R.Relations
public import Carlson.R.SingleIntegralAnalytic

/-!
# Explicit definition of the regularized Carlson R-function

The regularized R-function `R_t(b, z) / Γ(∑ b)` is defined for every complex exponent `t`,
every complex parameter vector `b` and every node vector `z` by a finite recursion that
bottoms out in Carlson's single Euler integral, following the pattern of `Complex.Gamma`.

In the convergence strip `re t < 0 < re (∑ b + t)` the function is the Euler integral
`(Γ(-t) Γ(∑ b + t))⁻¹ ∫₀¹ u^{-t-1} (1-u)^{∑ b + t - 1} ∏ᵢ (1 - u + u zᵢ)^{-bᵢ} du`,
which converges for all parameters and for all nodes in the product slit plane. Outside the
strip the function is reached through the two denominator-free associated relations
`regR_t(b) = ∑ᵢ bᵢ regR_t(b + eᵢ)` and `regR_t(b) = ∑ᵢ bᵢ zᵢ regR_{t-1}(b + eᵢ)`, the first
raising the total parameter and the second lowering the exponent. The recursion depth is
computed from the real parts of `t` and `∑ b + t`, and the value is independent of that
choice by the identity theorem in the joint variables.

## Main definitions

* `Carlson.regCarlsonREuler t b z`: the doubly regularized Euler integral.
* `Carlson.regCarlsonRAux m n t b z`: `m` exponent-lowering and `n` parameter-raising steps
  applied to the Euler integral.
* `Carlson.regCarlsonR t b z`: the regularized R-function, with the recursion depth chosen
  from `t` and `∑ b`.
* `Carlson.carlsonR t b z`: Carlson's function `R_t(b, z) = Γ(∑ b) regCarlsonR t b z`.

## Main results

* `Carlson.regCarlsonR_eq_regCarlsonRAux`: independence of the recursion depth.
* `Carlson.regCarlsonR_eq_regCarlsonREuler`: the Euler integral in the convergence strip.
* `Carlson.analyticOnNhd_regCarlsonR_comp`: joint analyticity under analytic substitutions,
  for all exponents and parameters and slit-plane nodes.
* `Carlson.regCarlsonR_eq_sum_addDirichletUnit`,
  `Carlson.regCarlsonR_add_one_eq_sum_mul_addDirichletUnit`: the associated relations on
  the whole domain.
* `Carlson.regCarlsonR_eq_regCarlsonRIntegral`: agreement with the native Dirichlet integral
  for convergent parameters and right-half-plane nodes, at every exponent.
* `Carlson.isRegCarlsonRContinuation_regCarlsonR`: the R-function is the unique entire
  continuation of the native integral in the parameters.

## Joint variables

For the identity-theorem arguments the three groups of variables are packaged as one
function on `Option (ι ⊕ ι)`: the exponent at `none`, the parameters at `some (Sum.inl i)`
and the nodes at `some (Sum.inr i)`. `Carlson.carlsonRJointStrip m n` is the joint domain on
which `regCarlsonRAux m n` is analytic, and `Carlson.carlsonRJointDomain` is the union of
these strips.
-/

open Dirichlet
open Complex Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Joint variables -/

/-- The joint variable with exponent `t`, parameters `b` and nodes `z`. -/
def carlsonRJointPoint (t : ℂ) (b z : ι → ℂ) : Option (ι ⊕ ι) → ℂ :=
  fun k => k.elim t (Sum.elim b z)

/-- The exponent coordinate of a joint variable. -/
def carlsonRJointExponent (q : Option (ι ⊕ ι) → ℂ) : ℂ := q none

/-- The parameter coordinates of a joint variable. -/
def carlsonRJointParameters (q : Option (ι ⊕ ι) → ℂ) (i : ι) : ℂ := q (some (Sum.inl i))

/-- The node coordinates of a joint variable. -/
def carlsonRJointNodes (q : Option (ι ⊕ ι) → ℂ) (i : ι) : ℂ := q (some (Sum.inr i))

omit [Fintype ι] in
@[simp] theorem carlsonRJointExponent_jointPoint (t : ℂ) (b z : ι → ℂ) :
    carlsonRJointExponent (carlsonRJointPoint t b z) = t := rfl

omit [Fintype ι] in
@[simp] theorem carlsonRJointParameters_jointPoint (t : ℂ) (b z : ι → ℂ) :
    carlsonRJointParameters (carlsonRJointPoint t b z) = b := rfl

omit [Fintype ι] in
@[simp] theorem carlsonRJointNodes_jointPoint (t : ℂ) (b z : ι → ℂ) :
    carlsonRJointNodes (carlsonRJointPoint t b z) = z := rfl

omit [Fintype ι] in
/-- A joint variable is the joint point of its three coordinates. -/
theorem carlsonRJointPoint_coords (q : Option (ι ⊕ ι) → ℂ) :
    carlsonRJointPoint (carlsonRJointExponent q) (carlsonRJointParameters q)
      (carlsonRJointNodes q) = q := by
  funext k
  rcases k with _ | (i | i) <;> rfl

omit [Fintype ι] in
/-- The joint point is continuous in its three arguments. -/
theorem continuous_carlsonRJointPoint :
    Continuous (fun p : (ℂ × (ι → ℂ)) × (ι → ℂ) => carlsonRJointPoint p.1.1 p.1.2 p.2) := by
  apply continuous_pi
  intro k
  rcases k with _ | (i | i)
  · exact continuous_fst.fst
  · exact (continuous_apply i).comp continuous_fst.snd
  · exact (continuous_apply i).comp continuous_snd

omit [Fintype ι] in
theorem continuous_carlsonRJointExponent :
    Continuous (carlsonRJointExponent (ι := ι)) := continuous_apply none

omit [Fintype ι] in
theorem continuous_carlsonRJointParameters :
    Continuous (carlsonRJointParameters (ι := ι)) :=
  continuous_pi fun i => continuous_apply (some (Sum.inl i))

omit [Fintype ι] in
theorem continuous_carlsonRJointNodes :
    Continuous (carlsonRJointNodes (ι := ι)) :=
  continuous_pi fun i => continuous_apply (some (Sum.inr i))

theorem analyticOnNhd_carlsonRJointExponent :
    AnalyticOnNhd ℂ (carlsonRJointExponent (ι := ι)) univ := fun q _ =>
  (ContinuousLinearMap.proj none : (Option (ι ⊕ ι) → ℂ) →L[ℂ] ℂ).analyticAt q

theorem analyticOnNhd_carlsonRJointParameters :
    AnalyticOnNhd ℂ (carlsonRJointParameters (ι := ι)) univ := fun q _ =>
  analyticAt_pi_iff.mpr fun i =>
    (ContinuousLinearMap.proj (some (Sum.inl i)) : (Option (ι ⊕ ι) → ℂ) →L[ℂ] ℂ).analyticAt q

theorem analyticOnNhd_carlsonRJointNodes :
    AnalyticOnNhd ℂ (carlsonRJointNodes (ι := ι)) univ := fun q _ =>
  analyticAt_pi_iff.mpr fun i =>
    (ContinuousLinearMap.proj (some (Sum.inr i)) : (Option (ι ⊕ ι) → ℂ) →L[ℂ] ℂ).analyticAt q

/-- The joint domain: all exponents, all parameters, and slit-plane nodes. -/
def carlsonRJointDomain : Set (Option (ι ⊕ ι) → ℂ) :=
  {q | carlsonRJointNodes q ∈ carlsonRSlitDomain}

/-- The joint strip reached from the convergence strip of the Euler integral by `m`
exponent-lowering and `n` parameter-raising steps. -/
def carlsonRJointStrip (m n : ℕ) : Set (Option (ι ⊕ ι) → ℂ) :=
  {q | (carlsonRJointExponent q).re < m ∧
    -(n : ℝ) < ((∑ i, carlsonRJointParameters q i) + carlsonRJointExponent q).re ∧
    carlsonRJointNodes q ∈ carlsonRSlitDomain}

theorem carlsonRJointStrip_subset_domain (m n : ℕ) :
    carlsonRJointStrip m n ⊆ (carlsonRJointDomain : Set (Option (ι ⊕ ι) → ℂ)) :=
  fun _ hq => hq.2.2

theorem carlsonRJointStrip_mono {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    carlsonRJointStrip m n ⊆ (carlsonRJointStrip m' n' : Set (Option (ι ⊕ ι) → ℂ)) :=
  fun _ hq => ⟨hq.1.trans_le (by exact_mod_cast hm),
    (neg_le_neg (by exact_mod_cast hn)).trans_lt hq.2.1, hq.2.2⟩

theorem isOpen_carlsonRJointDomain : IsOpen (carlsonRJointDomain : Set (Option (ι ⊕ ι) → ℂ)) :=
  isOpen_carlsonRSlitDomain.preimage continuous_carlsonRJointNodes

theorem isOpen_carlsonRJointStrip (m n : ℕ) :
    IsOpen (carlsonRJointStrip m n : Set (Option (ι ⊕ ι) → ℂ)) := by
  simp only [carlsonRJointStrip, Set.ofPred_and]
  refine (isOpen_lt (Complex.continuous_re.comp continuous_carlsonRJointExponent)
    continuous_const).inter ((isOpen_lt continuous_const (Complex.continuous_re.comp
      ((continuous_finsetSum _ fun i _ => continuous_apply (some (Sum.inl i))).add
        continuous_carlsonRJointExponent))).inter isOpen_carlsonRJointDomain)

/-- The exponent-parameter strip is convex. -/
theorem convex_carlsonRExponentParameterStrip (m n : ℕ) :
    Convex ℝ {p : ℂ × (ι → ℂ) | p.1.re < m ∧ -(n : ℝ) < ((∑ i, p.2 i) + p.1).re} := by
  have h1 : IsLinearMap ℝ (fun p : ℂ × (ι → ℂ) => p.1.re) := by
    constructor
    · intro x y
      simp [add_re]
    · intro c x
      simp
  have h2 : IsLinearMap ℝ (fun p : ℂ × (ι → ℂ) => ((∑ i, p.2 i) + p.1).re) := by
    constructor
    · intro x y
      change ((∑ i, (x + y).2 i) + (x + y).1).re =
        ((∑ i, x.2 i) + x.1).re + ((∑ i, y.2 i) + y.1).re
      simp only [Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib, Prod.fst_add, add_re]
      ring
    · intro c x
      change ((∑ i, (c • x).2 i) + (c • x).1).re = c • ((∑ i, x.2 i) + x.1).re
      simp only [Prod.smul_snd, Pi.smul_apply, Prod.smul_fst, Complex.real_smul,
        ← Finset.mul_sum, ← mul_add, Complex.re_ofReal_mul, smul_eq_mul]
  simpa only [Set.ofPred_and] using
    (convex_halfSpace_lt h1 (m : ℝ)).inter (convex_halfSpace_gt h2 (-(n : ℝ)))

/-- The joint strip is the image of a product of a convex set and the slit domain. -/
theorem carlsonRJointStrip_eq_image (m n : ℕ) :
    (carlsonRJointStrip m n : Set (Option (ι ⊕ ι) → ℂ)) =
      (fun p : (ℂ × (ι → ℂ)) × (ι → ℂ) => carlsonRJointPoint p.1.1 p.1.2 p.2) ''
        ({p : ℂ × (ι → ℂ) | p.1.re < m ∧ -(n : ℝ) < ((∑ i, p.2 i) + p.1).re} ×ˢ
          carlsonRSlitDomain) := by
  ext q
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨((carlsonRJointExponent q, carlsonRJointParameters q), carlsonRJointNodes q),
      ⟨⟨h1, h2⟩, h3⟩, carlsonRJointPoint_coords q⟩
  · rintro ⟨⟨⟨t, b⟩, z⟩, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    exact ⟨h1, h2, h3⟩

omit [Fintype ι] in
/-- The joint domain is the image of the product of the whole exponent-parameter space and
the slit domain. -/
theorem carlsonRJointDomain_eq_image :
    (carlsonRJointDomain : Set (Option (ι ⊕ ι) → ℂ)) =
      (fun p : (ℂ × (ι → ℂ)) × (ι → ℂ) => carlsonRJointPoint p.1.1 p.1.2 p.2) ''
        (univ ×ˢ carlsonRSlitDomain) := by
  ext q
  constructor
  · intro h
    exact ⟨((carlsonRJointExponent q, carlsonRJointParameters q), carlsonRJointNodes q),
      ⟨mem_univ _, h⟩, carlsonRJointPoint_coords q⟩
  · rintro ⟨⟨⟨t, b⟩, z⟩, ⟨-, h3⟩, rfl⟩
    exact h3

theorem isPreconnected_carlsonRJointStrip (m n : ℕ) :
    IsPreconnected (carlsonRJointStrip m n : Set (Option (ι ⊕ ι) → ℂ)) := by
  rw [carlsonRJointStrip_eq_image]
  exact ((convex_carlsonRExponentParameterStrip m n).isPreconnected.prod
    isPreconnected_carlsonRSlitDomain).image _ continuous_carlsonRJointPoint.continuousOn

omit [Fintype ι] in
theorem isPreconnected_carlsonRJointDomain :
    IsPreconnected (carlsonRJointDomain : Set (Option (ι ⊕ ι) → ℂ)) := by
  rw [carlsonRJointDomain_eq_image]
  exact (isPreconnected_univ.prod isPreconnected_carlsonRSlitDomain).image _
    continuous_carlsonRJointPoint.continuousOn

/-- The base point `t = -1`, `b = 2`, `z = 1`, which lies in every joint strip when `ι` is
nonempty. -/
def carlsonRJointBase : Option (ι ⊕ ι) → ℂ :=
  carlsonRJointPoint (-1) (fun _ => 2) (fun _ => 1)

theorem carlsonRJointBase_mem_strip [Nonempty ι] (m n : ℕ) :
    (carlsonRJointBase : Option (ι ⊕ ι) → ℂ) ∈ carlsonRJointStrip m n := by
  have hcard : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.mpr Fintype.card_pos
  refine ⟨?_, ?_, one_mem_carlsonRSlitDomain⟩
  · change (-1 : ℂ).re < m
    simp only [neg_re, one_re]
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  · change -(n : ℝ) < ((∑ _i : ι, (2 : ℂ)) + -1).re
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_re, mul_re, natCast_re,
      natCast_im, re_ofNat, im_ofNat, neg_re, one_re]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem carlsonRJointBase_mem_domain [Nonempty ι] :
    (carlsonRJointBase : Option (ι ⊕ ι) → ℂ) ∈ carlsonRJointDomain :=
  carlsonRJointStrip_subset_domain 0 0 (carlsonRJointBase_mem_strip 0 0)

/-- Identity theorem on a joint strip: two functions analytic on the strip that agree near
the base point agree on the whole strip. -/
theorem eqOn_carlsonRJointStrip_of_eventuallyEq [Nonempty ι] {m n : ℕ}
    {F G : (Option (ι ⊕ ι) → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (carlsonRJointStrip m n))
    (hG : AnalyticOnNhd ℂ G (carlsonRJointStrip m n))
    (hFG : F =ᶠ[𝓝 carlsonRJointBase] G) : EqOn F G (carlsonRJointStrip m n) :=
  hF.eqOn_of_preconnected_of_eventuallyEq hG (isPreconnected_carlsonRJointStrip m n)
    (carlsonRJointBase_mem_strip m n) hFG

/-- Identity theorem on the joint domain. -/
theorem eqOn_carlsonRJointDomain_of_eventuallyEq [Nonempty ι]
    {F G : (Option (ι ⊕ ι) → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F carlsonRJointDomain)
    (hG : AnalyticOnNhd ℂ G carlsonRJointDomain)
    (hFG : F =ᶠ[𝓝 carlsonRJointBase] G) : EqOn F G carlsonRJointDomain :=
  hF.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_carlsonRJointDomain
    carlsonRJointBase_mem_domain hFG

/-! ### The recursive definition -/

/-- The Euler integral with both endpoint Gamma regularizations. In the convergence strip
`re t < 0 < re (∑ b + t)` this is `R_t(b, z) / Γ(∑ b)`; elsewhere it is only a totalized
expression. -/
def regCarlsonREuler (t : ℂ) (b z : ι → ℂ) : ℂ :=
  (Gamma (-t))⁻¹ * (Gamma ((∑ i, b i) + t))⁻¹ *
    carlsonRUnitIntervalIntegral (-t) ((∑ i, b i) + t) b z

/-- `n` parameter-raising steps applied to the Euler integral. -/
def regCarlsonRRaise : ℕ → ℂ → (ι → ℂ) → (ι → ℂ) → ℂ
  | 0, t, b, z => regCarlsonREuler t b z
  | n + 1, t, b, z => ∑ i, b i * regCarlsonRRaise n t (addDirichletUnit b i) z

/-- `m` exponent-lowering steps applied after `n` parameter-raising steps. -/
def regCarlsonRAux : ℕ → ℕ → ℂ → (ι → ℂ) → (ι → ℂ) → ℂ
  | 0, n, t, b, z => regCarlsonRRaise n t b z
  | m + 1, n, t, b, z => ∑ i, b i * z i * regCarlsonRAux m n (t - 1) (addDirichletUnit b i) z

/-- The regularized Carlson R-function `R_t(b, z) / Γ(∑ b)`, defined for all complex
exponents and parameters. Values at nodes outside the product slit plane are unspecified.

The definition is irreducible: the recursion depth involves `Nat.floor`, and unfolding it during
unification is never useful. Use `regCarlsonR_eq_regCarlsonRAux` instead. -/
@[irreducible] def regCarlsonR (t : ℂ) (b z : ι → ℂ) : ℂ :=
  regCarlsonRAux (⌊t.re⌋₊ + 1) (⌊-((∑ i, b i) + t).re⌋₊ + 1) t b z

/-- Carlson's R-function `R_t(b, z)`. At poles of `Γ(∑ b)` this is only the totalized
product. -/
def carlsonR (t : ℂ) (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonR t b z

theorem regCarlsonRRaise_zero (t : ℂ) (b z : ι → ℂ) :
    regCarlsonRRaise 0 t b z = regCarlsonREuler t b z := rfl

theorem regCarlsonRRaise_succ (n : ℕ) (t : ℂ) (b z : ι → ℂ) :
    regCarlsonRRaise (n + 1) t b z =
      ∑ i, b i * regCarlsonRRaise n t (addDirichletUnit b i) z := rfl

theorem regCarlsonRAux_zero (n : ℕ) (t : ℂ) (b z : ι → ℂ) :
    regCarlsonRAux 0 n t b z = regCarlsonRRaise n t b z := rfl

theorem regCarlsonRAux_succ (m n : ℕ) (t : ℂ) (b z : ι → ℂ) :
    regCarlsonRAux (m + 1) n t b z =
      ∑ i, b i * z i * regCarlsonRAux m n (t - 1) (addDirichletUnit b i) z := rfl

/-- The parameter-raising step commutes with the exponent-lowering steps. -/
theorem regCarlsonRAux_succ_right (m n : ℕ) (t : ℂ) (b z : ι → ℂ) :
    regCarlsonRAux m (n + 1) t b z =
      ∑ i, b i * regCarlsonRAux m n t (addDirichletUnit b i) z := by
  induction m generalizing t b with
  | zero => rfl
  | succ m ih =>
    rw [regCarlsonRAux_succ]
    simp_rw [ih, regCarlsonRAux_succ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [addDirichletUnit_comm b j i, addDirichletUnit_apply, addDirichletUnit_apply]
    by_cases hij : i = j
    · subst hij
      ring
    · simp only [hij, Ne.symm hij, ite_false, add_zero]
      ring

/-- With an empty index type every recursion step gives zero. -/
theorem regCarlsonRAux_eq_zero_of_isEmpty [IsEmpty ι] {m n : ℕ} (h : m ≠ 0 ∨ n ≠ 0)
    (t : ℂ) (b z : ι → ℂ) : regCarlsonRAux m n t b z = 0 := by
  rcases m with _ | m
  · rcases n with _ | n
    · simp at h
    · rw [regCarlsonRAux_succ_right]
      simp
  · rw [regCarlsonRAux_succ]
    simp

theorem regCarlsonR_eq_zero_of_isEmpty [IsEmpty ι] (t : ℂ) (b z : ι → ℂ) :
    regCarlsonR t b z = 0 := by
  unfold regCarlsonR
  exact regCarlsonRAux_eq_zero_of_isEmpty (Or.inl (Nat.succ_ne_zero _)) t b z

/-! ### Analyticity of the recursion -/

/-- Unit parameter shifts preserve analytic dependence on auxiliary variables. -/
theorem analyticOnNhd_addDirichletUnit_comp {U : Set (κ → ℂ)} {b : (κ → ℂ) → ι → ℂ}
    (hb : AnalyticOnNhd ℂ b U) (i : ι) :
    AnalyticOnNhd ℂ (fun q => addDirichletUnit (b q) i) U := by
  classical
  intro p hp
  apply analyticAt_pi_iff.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [addDirichletUnit, Function.update_self] using!
      ((analyticAt_pi_iff.mp (hb p hp)) i).add analyticAt_const
  · simpa only [addDirichletUnit, Function.update_of_ne hji] using
      (analyticAt_pi_iff.mp (hb p hp)) j

/-- The regularized Euler integral is jointly analytic under analytic substitutions on the
convergence strip. -/
theorem analyticOnNhd_regCarlsonREuler_comp
    {U : Set (κ → ℂ)} {t : (κ → ℂ) → ℂ} {b z : (κ → ℂ) → ι → ℂ}
    (hU : IsOpen U) (ht : AnalyticOnNhd ℂ t U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hslit : ∀ p ∈ U, z p ∈ carlsonRSlitDomain)
    (hstrip : ∀ p ∈ U, (t p).re < 0 ∧ 0 < ((∑ i, b p i) + t p).re) :
    AnalyticOnNhd ℂ (fun p => regCarlsonREuler (t p) (b p) (z p)) U := by
  have hA : AnalyticOnNhd ℂ (fun q => -t q) U := fun q hq => (ht q hq).neg
  have hB : AnalyticOnNhd ℂ (fun q => (∑ i, b q i) + t q) U := fun q hq =>
    (Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp (hb q hq)) i).add (ht q hq)
  have hI := analyticOnNhd_carlsonRUnitIntervalIntegral_comp hU hA hB hb hz
    (fun p hp => ⟨by rw [neg_re]; exact neg_pos.mpr (hstrip p hp).1, (hstrip p hp).2⟩) hslit
  intro p hp
  exact (((differentiable_one_div_Gamma.analyticAt _).comp_of_eq (hA p hp) rfl).mul
    ((differentiable_one_div_Gamma.analyticAt _).comp_of_eq (hB p hp) rfl)).mul (hI p hp)

/-- Joint analyticity of the parameter-raising recursion on its strip. -/
theorem analyticOnNhd_regCarlsonRRaise_comp {n : ℕ}
    {U : Set (κ → ℂ)} {t : (κ → ℂ) → ℂ} {b z : (κ → ℂ) → ι → ℂ}
    (hU : IsOpen U) (ht : AnalyticOnNhd ℂ t U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hslit : ∀ p ∈ U, z p ∈ carlsonRSlitDomain)
    (hstrip : ∀ p ∈ U, (t p).re < 0 ∧ -(n : ℝ) < ((∑ i, b p i) + t p).re) :
    AnalyticOnNhd ℂ (fun p => regCarlsonRRaise n (t p) (b p) (z p)) U := by
  induction n generalizing b with
  | zero =>
    exact analyticOnNhd_regCarlsonREuler_comp hU ht hb hz hslit
      (fun p hp => ⟨(hstrip p hp).1, by simpa using (hstrip p hp).2⟩)
  | succ n ih =>
    intro p hp
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      ((analyticAt_pi_iff.mp (hb p hp)) i).mul
        (ih (b := fun q => addDirichletUnit (b q) i) (analyticOnNhd_addDirichletUnit_comp hb i)
          (fun q hq => ⟨(hstrip q hq).1, by
            have := (hstrip q hq).2
            simp only [sum_addDirichletUnit, add_re, one_re, Nat.cast_add, Nat.cast_one] at this ⊢
            linarith⟩) p hp)

/-- Joint analyticity of the full recursion on its strip. -/
theorem analyticOnNhd_regCarlsonRAux_comp {m n : ℕ}
    {U : Set (κ → ℂ)} {t : (κ → ℂ) → ℂ} {b z : (κ → ℂ) → ι → ℂ}
    (hU : IsOpen U) (ht : AnalyticOnNhd ℂ t U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hslit : ∀ p ∈ U, z p ∈ carlsonRSlitDomain)
    (hstrip : ∀ p ∈ U, (t p).re < m ∧ -(n : ℝ) < ((∑ i, b p i) + t p).re) :
    AnalyticOnNhd ℂ (fun p => regCarlsonRAux m n (t p) (b p) (z p)) U := by
  induction m generalizing t b with
  | zero =>
    exact analyticOnNhd_regCarlsonRRaise_comp hU ht hb hz hslit
      (fun p hp => ⟨by simpa using (hstrip p hp).1, (hstrip p hp).2⟩)
  | succ m ih =>
    intro p hp
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      (((analyticAt_pi_iff.mp (hb p hp)) i).mul ((analyticAt_pi_iff.mp (hz p hp)) i)).mul
        (ih (t := fun q => t q - 1) (b := fun q => addDirichletUnit (b q) i)
          (fun q hq => (ht q hq).sub analyticAt_const)
          (analyticOnNhd_addDirichletUnit_comp hb i)
          (fun q hq => ⟨by
              have := (hstrip q hq).1
              simp only [sub_re, one_re, Nat.cast_add, Nat.cast_one] at this ⊢
              linarith, by
              have := (hstrip q hq).2
              simp only [sum_addDirichletUnit, add_re, sub_re, one_re] at this ⊢
              linarith⟩) p hp)

/-- Analyticity of the recursion on a joint strip. -/
theorem analyticOnNhd_regCarlsonRAux_joint (m n : ℕ) :
    AnalyticOnNhd ℂ (fun q => regCarlsonRAux m n (carlsonRJointExponent q)
      (carlsonRJointParameters q) (carlsonRJointNodes q))
      (carlsonRJointStrip m n : Set (Option (ι ⊕ ι) → ℂ)) :=
  analyticOnNhd_regCarlsonRAux_comp (isOpen_carlsonRJointStrip m n)
    (analyticOnNhd_carlsonRJointExponent.mono (subset_univ _))
    (analyticOnNhd_carlsonRJointParameters.mono (subset_univ _))
    (analyticOnNhd_carlsonRJointNodes.mono (subset_univ _))
    (fun _ hq => hq.2.2) (fun _ hq => ⟨hq.1, hq.2.1⟩)

/-! ### The associated relations for the Euler integral -/

/-- In the convergence strip, for convergent parameters and right-half-plane nodes, the
regularized Euler integral is the regularized Dirichlet integral. -/
theorem regCarlsonREuler_eq_regCarlsonRIntegral {t : ℂ} {b z : ι → ℂ} (ht : t.re < 0)
    (hct : 0 < ((∑ i, b i) + t).re) (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonREuler t b z = regCarlsonRIntegral t b z := by
  have ha : 0 < (-t).re := by rw [neg_re]; exact neg_pos.mpr ht
  have hsum : -t + ((∑ i, b i) + t) = ∑ i, b i := by ring
  have hG := Gamma_ne_zero_of_re_pos ha
  have hG' := Gamma_ne_zero_of_re_pos hct
  have hGc : Gamma (∑ i, b i) ≠ 0 := by
    rw [← hsum]
    exact Gamma_ne_zero_of_re_pos (by rw [add_re]; linarith)
  unfold regCarlsonREuler
  rw [carlsonRUnitIntervalIntegral_eq ha hct hsum hb hz, betaIntegral_eq_Gamma_mul_div _ _ ha hct,
    carlsonRIntegral, hsum, neg_neg]
  field_simp

/-- The open set of joint variables in the convergence strip with convergent parameters
and right-half-plane nodes, on which the Euler integral is the Dirichlet integral. -/
private def nativeJointSet : Set (Option (ι ⊕ ι) → ℂ) :=
  carlsonRJointStrip 0 0 ∩ {q | carlsonRJointParameters q ∈ mvBetaConvergent ∧
    carlsonRJointNodes q ∈ carlsonRVariableDomain}

private theorem isOpen_nativeJointSet :
    IsOpen (nativeJointSet : Set (Option (ι ⊕ ι) → ℂ)) :=
  (isOpen_carlsonRJointStrip 0 0).inter
    ((isOpen_mvBetaConvergent.preimage continuous_carlsonRJointParameters).inter
      (isOpen_carlsonRVariableDomain.preimage continuous_carlsonRJointNodes))

private theorem carlsonRJointBase_mem_nativeJointSet [Nonempty ι] :
    (carlsonRJointBase : Option (ι ⊕ ι) → ℂ) ∈ nativeJointSet :=
  ⟨carlsonRJointBase_mem_strip 0 0, fun _ => by change (0 : ℝ) < (2 : ℂ).re; norm_num,
    fun _ => by change (0 : ℝ) < (1 : ℂ).re; norm_num⟩

private theorem mem_nativeJointSet_iff {q : Option (ι ⊕ ι) → ℂ} :
    q ∈ nativeJointSet ↔ (carlsonRJointExponent q).re < 0 ∧
      0 < ((∑ i, carlsonRJointParameters q i) + carlsonRJointExponent q).re ∧
      carlsonRJointNodes q ∈ carlsonRSlitDomain ∧
      carlsonRJointParameters q ∈ mvBetaConvergent ∧
      carlsonRJointNodes q ∈ carlsonRVariableDomain := by
  simp only [nativeJointSet, carlsonRJointStrip, mem_inter_iff, mem_ofPred_eq, Nat.cast_zero,
    neg_zero, and_assoc]

/-- The first associated relation for the regularized Euler integral in its convergence
strip: raising the total parameter by one. -/
theorem regCarlsonREuler_eq_sum_addDirichletUnit {t : ℂ} {b z : ι → ℂ} (ht : t.re < 0)
    (hct : 0 < ((∑ i, b i) + t).re) (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonREuler t b z = ∑ i, b i * regCarlsonREuler t (addDirichletUnit b i) z := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    exfalso
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hct
    linarith
  | inr h =>
    have hF : AnalyticOnNhd ℂ (fun q => regCarlsonREuler (carlsonRJointExponent q)
        (carlsonRJointParameters q) (carlsonRJointNodes q)) (carlsonRJointStrip 0 0) :=
      analyticOnNhd_regCarlsonREuler_comp (isOpen_carlsonRJointStrip (ι := ι) 0 0)
        (analyticOnNhd_carlsonRJointExponent.mono (subset_univ _))
        (analyticOnNhd_carlsonRJointParameters.mono (subset_univ _))
        (analyticOnNhd_carlsonRJointNodes.mono (subset_univ _))
        (fun _ hq => hq.2.2) (fun _ hq => ⟨by simpa using hq.1, by simpa using hq.2.1⟩)
    have hG : AnalyticOnNhd ℂ (fun q : Option (ι ⊕ ι) → ℂ =>
        ∑ i, carlsonRJointParameters q i * regCarlsonREuler (carlsonRJointExponent q)
          (addDirichletUnit (carlsonRJointParameters q) i) (carlsonRJointNodes q))
        (carlsonRJointStrip 0 0) := by
      intro q hq
      exact Finset.analyticAt_fun_sum _ fun i _ =>
        ((analyticAt_pi_iff.mp
          (analyticOnNhd_carlsonRJointParameters (ι := ι) q (mem_univ _))) i).mul
          (analyticOnNhd_regCarlsonREuler_comp (isOpen_carlsonRJointStrip (ι := ι) 0 0)
            (analyticOnNhd_carlsonRJointExponent.mono (subset_univ _))
            (analyticOnNhd_addDirichletUnit_comp
              (analyticOnNhd_carlsonRJointParameters.mono (subset_univ _)) i)
            (analyticOnNhd_carlsonRJointNodes.mono (subset_univ _))
            (fun _ hq => hq.2.2) (fun q hq => ⟨by simpa using hq.1, by
              have := hq.2.1
              simp only [sum_addDirichletUnit, add_re, one_re, Nat.cast_zero, neg_zero] at this ⊢
              linarith⟩) q hq)
    have key := eqOn_carlsonRJointStrip_of_eventuallyEq hF hG (by
      filter_upwards [isOpen_nativeJointSet.mem_nhds carlsonRJointBase_mem_nativeJointSet] with q hq
      obtain ⟨h1, h2, -, h4, h5⟩ := mem_nativeJointSet_iff.mp hq
      show regCarlsonREuler _ _ _ = ∑ i, _ * regCarlsonREuler _ _ _
      rw [regCarlsonREuler_eq_regCarlsonRIntegral h1 h2 h4 h5,
        regCarlsonRIntegral_eq_sum_update_add_one _ h4 h5]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [regCarlsonREuler_eq_regCarlsonRIntegral h1 (by
        simp only [sum_addDirichletUnit, add_re, one_re] at h2 ⊢; linarith)
        (addDirichletUnit_mem_mvBetaConvergent h4 i) h5]
      rfl)
    exact key (show carlsonRJointPoint t b z ∈ carlsonRJointStrip 0 0 from
      ⟨by simpa using ht, by simpa using hct, hz⟩)

/-- The second associated relation for the regularized Euler integral in its convergence
strip: lowering the exponent by one. -/
theorem regCarlsonREuler_eq_sum_mul_addDirichletUnit {t : ℂ} {b z : ι → ℂ} (ht : t.re < 0)
    (hct : 0 < ((∑ i, b i) + t).re) (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonREuler t b z =
      ∑ i, b i * z i * regCarlsonREuler (t - 1) (addDirichletUnit b i) z := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    exfalso
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hct
    linarith
  | inr h =>
    have hF : AnalyticOnNhd ℂ (fun q => regCarlsonREuler (carlsonRJointExponent q)
        (carlsonRJointParameters q) (carlsonRJointNodes q)) (carlsonRJointStrip 0 0) :=
      analyticOnNhd_regCarlsonREuler_comp (isOpen_carlsonRJointStrip (ι := ι) 0 0)
        (analyticOnNhd_carlsonRJointExponent.mono (subset_univ _))
        (analyticOnNhd_carlsonRJointParameters.mono (subset_univ _))
        (analyticOnNhd_carlsonRJointNodes.mono (subset_univ _))
        (fun _ hq => hq.2.2) (fun _ hq => ⟨by simpa using hq.1, by simpa using hq.2.1⟩)
    have hG : AnalyticOnNhd ℂ (fun q : Option (ι ⊕ ι) → ℂ =>
        ∑ i, carlsonRJointParameters q i * carlsonRJointNodes q i *
          regCarlsonREuler (carlsonRJointExponent q - 1)
            (addDirichletUnit (carlsonRJointParameters q) i) (carlsonRJointNodes q))
        (carlsonRJointStrip 0 0) := by
      intro q hq
      exact Finset.analyticAt_fun_sum _ fun i _ =>
        (((analyticAt_pi_iff.mp
          (analyticOnNhd_carlsonRJointParameters (ι := ι) q (mem_univ _))) i).mul
          ((analyticAt_pi_iff.mp
            (analyticOnNhd_carlsonRJointNodes (ι := ι) q (mem_univ _))) i)).mul
          (analyticOnNhd_regCarlsonREuler_comp (isOpen_carlsonRJointStrip (ι := ι) 0 0)
            (t := fun q => carlsonRJointExponent q - 1)
            (fun q _ => (analyticOnNhd_carlsonRJointExponent (ι := ι) q (mem_univ _)).sub
              analyticAt_const)
            (analyticOnNhd_addDirichletUnit_comp
              (analyticOnNhd_carlsonRJointParameters.mono (subset_univ _)) i)
            (analyticOnNhd_carlsonRJointNodes.mono (subset_univ _))
            (fun _ hq => hq.2.2) (fun q hq => ⟨by
              have := hq.1
              simp only [sub_re, one_re, Nat.cast_zero] at this ⊢
              linarith, by
              have := hq.2.1
              simp only [sum_addDirichletUnit, add_re, sub_re, one_re, Nat.cast_zero,
                neg_zero] at this ⊢
              linarith⟩) q hq)
    have key := eqOn_carlsonRJointStrip_of_eventuallyEq hF hG (by
      filter_upwards [isOpen_nativeJointSet.mem_nhds carlsonRJointBase_mem_nativeJointSet] with q hq
      obtain ⟨h1, h2, -, h4, h5⟩ := mem_nativeJointSet_iff.mp hq
      show regCarlsonREuler _ _ _ = ∑ i, _ * _ * regCarlsonREuler _ _ _
      have hrel := regCarlsonRIntegral_add_one_eq_sum_mul_update
        (carlsonRJointExponent q - 1) h4 h5
      rw [sub_add_cancel] at hrel
      rw [regCarlsonREuler_eq_regCarlsonRIntegral h1 h2 h4 h5, hrel]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [regCarlsonREuler_eq_regCarlsonRIntegral (by
        simp only [sub_re, one_re]; linarith) (by
        simp only [sum_addDirichletUnit, add_re, sub_re, one_re] at h2 ⊢; linarith)
        (addDirichletUnit_mem_mvBetaConvergent h4 i) h5]
      rfl)
    exact key (show carlsonRJointPoint t b z ∈ carlsonRJointStrip 0 0 from
      ⟨by simpa using ht, by simpa using hct, hz⟩)

/-! ### Independence of the recursion depth -/

/-- In the convergence strip every parameter-raising recursion returns the Euler integral. -/
theorem regCarlsonRRaise_eq_regCarlsonREuler {t : ℂ} {b z : ι → ℂ} (ht : t.re < 0)
    (hct : 0 < ((∑ i, b i) + t).re) (hz : z ∈ carlsonRSlitDomain) (n : ℕ) :
    regCarlsonRRaise n t b z = regCarlsonREuler t b z := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [regCarlsonRRaise_succ, regCarlsonREuler_eq_sum_addDirichletUnit ht hct hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ih (by simp only [sum_addDirichletUnit, add_re, one_re] at hct ⊢; linarith)]

/-- In the convergence strip every recursion returns the Euler integral. -/
theorem regCarlsonRAux_eq_regCarlsonREuler {t : ℂ} {b z : ι → ℂ} (ht : t.re < 0)
    (hct : 0 < ((∑ i, b i) + t).re) (hz : z ∈ carlsonRSlitDomain) (m n : ℕ) :
    regCarlsonRAux m n t b z = regCarlsonREuler t b z := by
  induction m generalizing t b with
  | zero => exact regCarlsonRRaise_eq_regCarlsonREuler ht hct hz n
  | succ m ih =>
    rw [regCarlsonRAux_succ, regCarlsonREuler_eq_sum_mul_addDirichletUnit ht hct hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ih (by simp only [sub_re, one_re]; linarith)
      (by simp only [sum_addDirichletUnit, add_re, sub_re, one_re] at hct ⊢; linarith)]

/-- The Euler integral seed as a function of the joint variable is analytic on the
convergence strip and agrees there with every recursion. -/
private theorem regCarlsonRAux_joint_eventuallyEq [Nonempty ι] (m n m' n' : ℕ) :
    (fun q : Option (ι ⊕ ι) → ℂ => regCarlsonRAux m n (carlsonRJointExponent q)
      (carlsonRJointParameters q) (carlsonRJointNodes q)) =ᶠ[𝓝 carlsonRJointBase]
    (fun q => regCarlsonRAux m' n' (carlsonRJointExponent q)
      (carlsonRJointParameters q) (carlsonRJointNodes q)) := by
  filter_upwards [(isOpen_carlsonRJointStrip 0 0).mem_nhds (carlsonRJointBase_mem_strip 0 0)]
    with q hq
  have h1 : (carlsonRJointExponent q).re < 0 := by simpa using hq.1
  have h2 : 0 < ((∑ i, carlsonRJointParameters q i) + carlsonRJointExponent q).re := by
    simpa using hq.2.1
  change regCarlsonRAux m n _ _ _ = regCarlsonRAux m' n' _ _ _
  rw [regCarlsonRAux_eq_regCarlsonREuler h1 h2 hq.2.2,
    regCarlsonRAux_eq_regCarlsonREuler h1 h2 hq.2.2]

/-- One more exponent-lowering step does not change the value on the current strip. -/
theorem regCarlsonRAux_succ_left_eq {m n : ℕ} {t : ℂ} {b z : ι → ℂ} (ht : t.re < m)
    (hct : -(n : ℝ) < ((∑ i, b i) + t).re) (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonRAux (m + 1) n t b z = regCarlsonRAux m n t b z := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    rw [regCarlsonRAux_eq_zero_of_isEmpty (Or.inl (Nat.succ_ne_zero m))]
    rcases m with _ | m
    · rcases n with _ | n
      · exfalso
        simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, Nat.cast_zero,
          neg_zero] at ht hct
        linarith
      · rw [regCarlsonRAux_eq_zero_of_isEmpty (Or.inr (Nat.succ_ne_zero n))]
    · rw [regCarlsonRAux_eq_zero_of_isEmpty (Or.inl (Nat.succ_ne_zero m))]
  | inr h =>
    have key := eqOn_carlsonRJointStrip_of_eventuallyEq
      ((analyticOnNhd_regCarlsonRAux_joint (ι := ι) (m + 1) n).mono
        (carlsonRJointStrip_mono (Nat.le_succ m) le_rfl))
      (analyticOnNhd_regCarlsonRAux_joint m n)
      (regCarlsonRAux_joint_eventuallyEq (m + 1) n m n)
    exact key (show carlsonRJointPoint t b z ∈ carlsonRJointStrip m n from ⟨ht, hct, hz⟩)

/-- One more parameter-raising step does not change the value on the current strip. -/
theorem regCarlsonRAux_succ_right_eq {m n : ℕ} {t : ℂ} {b z : ι → ℂ} (ht : t.re < m)
    (hct : -(n : ℝ) < ((∑ i, b i) + t).re) (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonRAux m (n + 1) t b z = regCarlsonRAux m n t b z := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    rw [regCarlsonRAux_eq_zero_of_isEmpty (Or.inr (Nat.succ_ne_zero n))]
    rcases m with _ | m
    · rcases n with _ | n
      · exfalso
        simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, Nat.cast_zero,
          neg_zero] at ht hct
        linarith
      · rw [regCarlsonRAux_eq_zero_of_isEmpty (Or.inr (Nat.succ_ne_zero n))]
    · rw [regCarlsonRAux_eq_zero_of_isEmpty (Or.inl (Nat.succ_ne_zero m))]
  | inr h =>
    have key := eqOn_carlsonRJointStrip_of_eventuallyEq
      ((analyticOnNhd_regCarlsonRAux_joint (ι := ι) m (n + 1)).mono
        (carlsonRJointStrip_mono le_rfl (Nat.le_succ n)))
      (analyticOnNhd_regCarlsonRAux_joint m n)
      (regCarlsonRAux_joint_eventuallyEq m (n + 1) m n)
    exact key (show carlsonRJointPoint t b z ∈ carlsonRJointStrip m n from ⟨ht, hct, hz⟩)

/-- Increasing the recursion depth does not change the value on the current strip. -/
theorem regCarlsonRAux_eq_of_le {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n')
    {t : ℂ} {b z : ι → ℂ} (ht : t.re < m)
    (hct : -(n : ℝ) < ((∑ i, b i) + t).re) (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonRAux m n t b z = regCarlsonRAux m' n' t b z := by
  have h1 : ∀ k, m ≤ k → regCarlsonRAux k n t b z = regCarlsonRAux m n t b z := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [regCarlsonRAux_succ_left_eq (ht.trans_le (by exact_mod_cast hk)) hct hz, ih]
  have h2 : ∀ l, n ≤ l → regCarlsonRAux m' l t b z = regCarlsonRAux m' n t b z := by
    intro l hl
    induction l, hl using Nat.le_induction with
    | base => rfl
    | succ l hl ih =>
      rw [regCarlsonRAux_succ_right_eq (ht.trans_le (by exact_mod_cast hm))
        ((neg_le_neg (by exact_mod_cast hl)).trans_lt hct) hz, ih]
  rw [h2 n' hn, h1 m' hm]

/-- The regularized R-function equals every sufficiently deep recursion. -/
theorem regCarlsonR_eq_regCarlsonRAux {m n : ℕ} {t : ℂ} {b z : ι → ℂ} (ht : t.re < m)
    (hct : -(n : ℝ) < ((∑ i, b i) + t).re) (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR t b z = regCarlsonRAux m n t b z := by
  unfold regCarlsonR
  have hM : t.re < ((⌊t.re⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  have hN : -((⌊-((∑ i, b i) + t).re⌋₊ + 1 : ℕ) : ℝ) < ((∑ i, b i) + t).re := by
    push_cast
    linarith [Nat.lt_floor_add_one (-((∑ i, b i) + t).re)]
  rw [regCarlsonRAux_eq_of_le (le_max_left _ m) (le_max_left _ n) hM hN hz,
    regCarlsonRAux_eq_of_le (le_max_right _ m) (le_max_right _ n) ht hct hz]

/-- In the convergence strip the regularized R-function is the regularized Euler
integral. -/
theorem regCarlsonR_eq_regCarlsonREuler {t : ℂ} {b z : ι → ℂ} (ht : t.re < 0)
    (hct : 0 < ((∑ i, b i) + t).re) (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR t b z = regCarlsonREuler t b z :=
  regCarlsonR_eq_regCarlsonRAux (m := 0) (n := 0) (by simpa using ht) (by simpa using hct) hz

/-- Carlson's single-integral representation 6.8-6 in its convergence strip, for all
complex parameters and slit-plane nodes. -/
theorem regCarlsonR_eq_unitIntervalIntegral {t : ℂ} {b z : ι → ℂ} (ht : t.re < 0)
    (hct : 0 < ((∑ i, b i) + t).re) (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR t b z = (Gamma (-t))⁻¹ * (Gamma ((∑ i, b i) + t))⁻¹ *
      carlsonRUnitIntervalIntegral (-t) ((∑ i, b i) + t) b z :=
  regCarlsonR_eq_regCarlsonREuler ht hct hz

/-- In the convergence strip, for convergent parameters and right-half-plane nodes, the
regularized R-function is the regularized Dirichlet integral. -/
theorem regCarlsonR_eq_regCarlsonRIntegral_of_strip {t : ℂ} {b z : ι → ℂ} (ht : t.re < 0)
    (hct : 0 < ((∑ i, b i) + t).re) (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonR t b z = regCarlsonRIntegral t b z := by
  rw [regCarlsonR_eq_regCarlsonREuler ht hct (carlsonRVariableDomain_subset_slitDomain hz),
    regCarlsonREuler_eq_regCarlsonRIntegral ht hct hb hz]

/-! ### Joint analyticity -/

/-- Joint analyticity of the regularized R-function under analytic substitutions, for all
exponents and parameters and slit-plane nodes (Carlson's Theorem 6.8-2). -/
theorem analyticOnNhd_regCarlsonR_comp
    {U : Set (κ → ℂ)} {t : (κ → ℂ) → ℂ} {b z : (κ → ℂ) → ι → ℂ}
    (hU : IsOpen U) (ht : AnalyticOnNhd ℂ t U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hslit : ∀ p ∈ U, z p ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun p => regCarlsonR (t p) (b p) (z p)) U := by
  intro p hp
  obtain ⟨m, hm⟩ := exists_nat_gt (t p).re
  obtain ⟨n, hn⟩ := exists_nat_gt (-((∑ i, b p i) + t p).re)
  have hB : AnalyticOnNhd ℂ (fun q => (∑ i, b q i) + t q) U := fun q hq =>
    (Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp (hb q hq)) i).add (ht q hq)
  have hevent : ∀ᶠ q in 𝓝 p, q ∈ U ∧ (t q).re < m ∧ -(n : ℝ) < ((∑ i, b q i) + t q).re := by
    filter_upwards [hU.mem_nhds hp,
      (Complex.continuous_re.continuousAt.comp (ht p hp).continuousAt).eventually_lt_const hm,
      (Complex.continuous_re.continuousAt.comp (hB p hp).continuousAt).eventually_const_lt
        (show -(n : ℝ) < ((∑ i, b p i) + t p).re by linarith)] with q hq h1 h2
    exact ⟨hq, h1, h2⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hsub : Metric.ball p r ⊆ U := fun q hq => (hball hq).1
  have hA := analyticOnNhd_regCarlsonRAux_comp (m := m) (n := n) Metric.isOpen_ball
    (ht.mono hsub) (hb.mono hsub) (hz.mono hsub) (fun q hq => hslit q (hsub hq))
    (fun q hq => (hball hq).2)
  apply (hA p (Metric.mem_ball_self hr)).congr
  filter_upwards [Metric.ball_mem_nhds p hr] with q hq
  exact (regCarlsonR_eq_regCarlsonRAux (hball hq).2.1 (hball hq).2.2 (hslit q (hsub hq))).symm

/-- Joint analyticity in the packaged variables on the joint domain. -/
theorem analyticOnNhd_regCarlsonR_jointCoordinates :
    AnalyticOnNhd ℂ (fun q => regCarlsonR (carlsonRJointExponent q)
      (carlsonRJointParameters q) (carlsonRJointNodes q))
      (carlsonRJointDomain : Set (Option (ι ⊕ ι) → ℂ)) :=
  analyticOnNhd_regCarlsonR_comp isOpen_carlsonRJointDomain
    (analyticOnNhd_carlsonRJointExponent.mono (subset_univ _))
    (analyticOnNhd_carlsonRJointParameters.mono (subset_univ _))
    (analyticOnNhd_carlsonRJointNodes.mono (subset_univ _)) (fun _ hq => hq)

/-- At fixed slit-plane nodes the regularized R-function is entire in the exponent and the
parameters jointly. -/
theorem analyticOnNhd_regCarlsonR_exponent_parameters {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun p : Option ι → ℂ =>
      regCarlsonR (p none) (fun i => p (some i)) z) univ := by
  apply analyticOnNhd_regCarlsonR_comp isOpen_univ
  · exact fun p _ => (ContinuousLinearMap.proj none : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p
  · intro p _
    exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p
  · exact analyticOnNhd_const
  · exact fun _ _ => hz

/-- At fixed exponent and parameters the regularized R-function is analytic on the product
slit plane. -/
theorem analyticOnNhd_regCarlsonR (t : ℂ) (b : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonR t b) carlsonRSlitDomain :=
  analyticOnNhd_regCarlsonR_comp isOpen_carlsonRSlitDomain analyticOnNhd_const
    analyticOnNhd_const analyticOnNhd_id (fun _ hz => hz)

/-! ### The associated relations on the whole domain -/

/-- Carlson's first associated relation for all exponents and parameters and slit-plane
nodes. -/
theorem regCarlsonR_eq_sum_addDirichletUnit (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR t b z = ∑ i, b i * regCarlsonR t (addDirichletUnit b i) z := by
  obtain ⟨m, hm⟩ := exists_nat_gt t.re
  obtain ⟨n, hn⟩ := exists_nat_gt (-((∑ i, b i) + t).re)
  rw [regCarlsonR_eq_regCarlsonRAux (m := m) (n := n + 1) hm (by push_cast; linarith) hz,
    regCarlsonRAux_succ_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [regCarlsonR_eq_regCarlsonRAux (m := m) (n := n) hm
    (by simp only [sum_addDirichletUnit, add_re, one_re] at hn ⊢; linarith) hz]

/-- Carlson's second associated relation for all exponents and parameters and slit-plane
nodes. -/
theorem regCarlsonR_add_one_eq_sum_mul_addDirichletUnit (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR (t + 1) b z = ∑ i, b i * z i * regCarlsonR t (addDirichletUnit b i) z := by
  obtain ⟨m, hm⟩ := exists_nat_gt t.re
  obtain ⟨n, hn⟩ := exists_nat_gt (-((∑ i, b i) + t).re)
  rw [regCarlsonR_eq_regCarlsonRAux (m := m + 1) (n := n)
    (by simp only [add_re, one_re]; push_cast; linarith)
    (by simp only [add_re, one_re] at hn ⊢; linarith) hz, regCarlsonRAux_succ,
    add_sub_cancel_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [regCarlsonR_eq_regCarlsonRAux (m := m) (n := n) hm
    (by simp only [sum_addDirichletUnit, add_re, one_re] at hn ⊢; linarith) hz]

/-! ### Composition interfaces -/

/-- Joint analyticity with the exponent at `none`, the parameters at `some (Sum.inl i)` and
the nodes at `some (Sum.inr i)`. This is the full joint holomorphy assertion of Carlson's
Theorem 6.8-2. -/
theorem analyticOnNhd_regCarlsonR_joint :
    AnalyticOnNhd ℂ (fun p : Option (ι ⊕ ι) → ℂ =>
      regCarlsonR (p none) (fun i => p (some (.inl i))) (fun i => p (some (.inr i))))
      {p | (fun i => p (some (.inr i))) ∈ carlsonRSlitDomain} :=
  analyticOnNhd_regCarlsonR_jointCoordinates

/-- A pointwise composition interface for arbitrary complex normed parameter spaces. -/
theorem analyticAt_regCarlsonR_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : E → ℂ} {b z : E → ι → ℂ} {p : E}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) :
    AnalyticAt ℂ (fun q => regCarlsonR (t q) (b q) (z q)) p := by
  have hf : AnalyticAt ℂ (fun q => carlsonRJointPoint (t q) (b q) (z q)) p := by
    apply analyticAt_pi_iff.mpr
    intro k
    rcases k with _ | (i | i)
    · exact ht
    · exact (analyticAt_pi_iff.mp hb) i
    · exact (analyticAt_pi_iff.mp hz) i
  exact (analyticOnNhd_regCarlsonR_jointCoordinates (carlsonRJointPoint (t p) (b p) (z p))
    hslit).comp_of_eq hf rfl

/-- The ordinary, unregularized function is jointly analytic wherever the total parameter
avoids the Gamma poles. The regularized theorem above has no such exclusion. -/
theorem analyticAt_carlsonR_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : E → ℂ} {b z : E → ι → ℂ} {p : E}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) (hc : ∀ n : ℕ, (∑ i, b p i) ≠ -n) :
    AnalyticAt ℂ (fun q => carlsonR (t q) (b q) (z q)) p := by
  have hsum : AnalyticAt ℂ (fun q => ∑ i, b q i) p :=
    Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i
  have hrecip := (differentiable_one_div_Gamma.analyticAt (∑ i, b p i)).comp_of_eq hsum rfl
  have hgamma : AnalyticAt ℂ (fun q => Gamma (∑ i, b q i)) p := by
    have h := hrecip.inv (inv_ne_zero (Gamma_ne_zero hc))
    change AnalyticAt ℂ (fun q => ((Gamma (∑ i, b q i))⁻¹)⁻¹) p at h
    simpa only [inv_inv] using h
  exact hgamma.mul (analyticAt_regCarlsonR_comp ht hb hz hslit)

/-- At fixed slit-plane nodes the regularized R-function is entire in the parameters. -/
theorem analyticOnNhd_regCarlsonR_parameters (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun b => regCarlsonR t b z) univ :=
  analyticOnNhd_regCarlsonR_comp isOpen_univ analyticOnNhd_const analyticOnNhd_id
    analyticOnNhd_const (fun _ _ => hz)

/-- At fixed parameters and slit-plane nodes the regularized R-function is entire in the
exponent. -/
theorem analyticOnNhd_regCarlsonR_exponent (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun t => regCarlsonR t b z) univ :=
  fun _ _ => analyticAt_regCarlsonR_comp analyticAt_id analyticAt_const analyticAt_const hz

/-- The unregularized R-function is analytic on the product slit plane at fixed exponent and
parameters. -/
theorem analyticOnNhd_carlsonR (t : ℂ) (b : ι → ℂ) :
    AnalyticOnNhd ℂ (carlsonR t b) carlsonRSlitDomain := by
  change AnalyticOnNhd ℂ (fun z => Gamma (∑ i, b i) * regCarlsonR t b z) carlsonRSlitDomain
  exact analyticOnNhd_const.mul (analyticOnNhd_regCarlsonR t b)

/-- Carlson's single-integral representation with the Gamma factors on the right, on the
whole product slit plane. -/
theorem carlsonRUnitIntervalIntegral_eq_gamma_mul_regCarlsonR {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a + a' = ∑ i, b i)
    (hz : z ∈ carlsonRSlitDomain) :
    carlsonRUnitIntervalIntegral a a' b z = (Gamma a * Gamma a') * regCarlsonR (-a) b z := by
  have hsum' : (∑ i, b i) + -a = a' := by rw [← hsum]; ring
  have hct : 0 < ((∑ i, b i) + -a).re := by rw [hsum']; exact ha'
  rw [regCarlsonR_eq_unitIntervalIntegral (by rw [neg_re]; linarith) hct hz, neg_neg, hsum']
  have hG := Gamma_ne_zero_of_re_pos ha
  have hG' := Gamma_ne_zero_of_re_pos ha'
  field_simp

/-! ### Agreement with the native integral at every exponent -/

open scoped Classical in
/-- The native regularized integral vanishes for the empty index type. -/
theorem regCarlsonRIntegral_eq_zero_of_isEmpty [IsEmpty ι] (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral t b z = 0 := by
  rw [regCarlsonRIntegral_eq_sum_update_add_one t hb hz]
  simp

/-- For convergent parameters and right-half-plane nodes the regularized R-function is the
native regularized Dirichlet integral, at every exponent. -/
theorem regCarlsonR_eq_regCarlsonRIntegral (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) : regCarlsonR t b z = regCarlsonRIntegral t b z := by
  cases isEmpty_or_nonempty ι with
  | inl h => rw [regCarlsonR_eq_zero_of_isEmpty, regCarlsonRIntegral_eq_zero_of_isEmpty t hb hz]
  | inr h =>
    have hc : 0 < (∑ i, b i).re := by
      rw [re_sum]
      exact Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
    have hslit := carlsonRVariableDomain_subset_slitDomain hz
    let S : Set ℂ := {s | s.re < 0} ∩ {s | 0 < ((∑ i, b i) + s).re}
    have hS : IsOpen S :=
      (isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.add
          continuous_id)))
    have ht₀ : (-((∑ i, b i).re / 2 : ℝ) : ℂ) ∈ S := by
      constructor
      · change (-((∑ i, b i).re / 2 : ℝ) : ℂ).re < 0
        simp only [neg_re, ofReal_re]
        linarith
      · change 0 < ((∑ i, b i) + (-((∑ i, b i).re / 2 : ℝ) : ℂ)).re
        simp only [add_re, neg_re, ofReal_re]
        linarith
    exact (analyticOnNhd_regCarlsonR_exponent b hslit).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_regCarlsonRIntegral_exponent hb hz) isPreconnected_univ (mem_univ _)
      (by
        filter_upwards [hS.mem_nhds ht₀] with s hs
        exact regCarlsonR_eq_regCarlsonRIntegral_of_strip hs.1 hs.2 hb hz) (mem_univ t)

/-- The regularized R-function is an entire regularized continuation of the native integral
in the parameters, for right-half-plane nodes. -/
theorem isRegCarlsonRContinuation_regCarlsonR (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    IsRegCarlsonRContinuation t z (regCarlsonR t · z) :=
  ⟨analyticOnNhd_regCarlsonR_parameters t (carlsonRVariableDomain_subset_slitDomain hz),
    fun _ hb => regCarlsonR_eq_regCarlsonRIntegral _ hb hz⟩

/-- Any entire regularized continuation of the native integral in the parameters is the
regularized R-function. -/
theorem IsRegCarlsonRContinuation.eq_regCarlsonR {t : ℂ} {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonRContinuation t z G) (hz : z ∈ carlsonRVariableDomain) :
    G = (regCarlsonR t · z) :=
  hG.eq (isRegCarlsonRContinuation_regCarlsonR t hz)

/-- At natural exponents the regularized R-function is the regularized R-polynomial. -/
theorem regCarlsonR_natCast (n : ℕ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonR (n : ℂ) b z = regCarlsonRPolynomial n b z :=
  congrFun (isRegCarlsonRContinuation_regCarlsonR (n : ℂ) hz).eq_regCarlsonR_natCast b

/-! ### The third associated relation -/

/-- Carlson's third associated relation on right-half-plane nodes, by continuation in the
parameters from the native integral. -/
private theorem regCarlsonR_eq_addDirichletUnit_of_mem_variableDomain (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    regCarlsonR t b z =
      ((∑ j, b j) + t) * regCarlsonR t (addDirichletUnit b i) z -
        t * z i * regCarlsonR (t - 1) (addDirichletUnit b i) z := by
  have hslit := carlsonRVariableDomain_subset_slitDomain hz
  have hshift (s : ℂ) (c : ι → ℂ) :
      AnalyticAt ℂ (fun c : ι → ℂ ↦ regCarlsonR s (addDirichletUnit c i) z) c :=
    analyticAt_regCarlsonR_comp analyticAt_const
      (analyticOnNhd_addDirichletUnit_comp (b := id) analyticOnNhd_id i c (Set.mem_univ _))
      analyticAt_const hslit
  have hright : AnalyticOnNhd ℂ (fun b : ι → ℂ ↦
      ((∑ j, b j) + t) * regCarlsonR t (addDirichletUnit b i) z -
        t * z i * regCarlsonR (t - 1) (addDirichletUnit b i) z) Set.univ := by
    intro b _
    have hsum : AnalyticAt ℂ (fun c : ι → ℂ ↦ ∑ j, c j) b :=
      Finset.analyticAt_fun_sum _ fun j _ ↦
        (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).analyticAt b
    exact ((hsum.add analyticAt_const).mul (hshift t b)).sub
      (analyticAt_const.mul (hshift (t - 1) b))
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_regCarlsonR_parameters t hslit) hright ?_) b
  intro c hc
  simp_rw [regCarlsonR_eq_regCarlsonRIntegral t hc hz,
    regCarlsonR_eq_regCarlsonRIntegral t (addDirichletUnit_mem_mvBetaConvergent hc i) hz,
    regCarlsonR_eq_regCarlsonRIntegral (t - 1) (addDirichletUnit_mem_mvBetaConvergent hc i) hz]
  exact regCarlsonRIntegral_eq_update_add_one t hc hz i

/-- The parameter-raising identity on the full slit domain, without dividing by
the exponent or total parameter. -/
theorem regCarlsonR_eq_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    regCarlsonR t b z =
      ((∑ j, b j) + t) * regCarlsonR t (addDirichletUnit b i) z -
        t * z i * regCarlsonR (t - 1) (addDirichletUnit b i) z := by
  have hright : AnalyticOnNhd ℂ (fun w =>
      ((∑ j, b j) + t) * regCarlsonR t (addDirichletUnit b i) w -
        t * w i * regCarlsonR (t - 1) (addDirichletUnit b i) w) carlsonRSlitDomain := by
    intro w hw
    exact (analyticAt_const.mul (analyticOnNhd_regCarlsonR t _ w hw)).sub
      ((analyticAt_const.mul ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w)).mul
        (analyticOnNhd_regCarlsonR (t - 1) _ w hw))
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
    (analyticOnNhd_regCarlsonR t b) hright ?_ hz
  intro w hw
  exact regCarlsonR_eq_addDirichletUnit_of_mem_variableDomain t b hw i

end Carlson
