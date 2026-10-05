/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.AssociatedExercises
public import Carlson.R.IntegerParameters
public import Carlson.R.ZeroParameter
public import Carlson.R.SmallVariableContinuation
public import Carlson.Aggregation
public import Carlson.RPolynomial.Coefficients

/-!
# Removal of integral parameters (Carlson's Theorem 8.5-1)

Carlson's Theorem 8.5-1: if the exponent and all Dirichlet parameters of `R` are integers, then
`R_{-a}(b; z)` can be expressed with rational functions and logarithms. We make this precise
with a predicate. A function `f` of the nodes is *log-rational* on a set `S` if some nonzero
polynomial `Q` satisfies
`Q(z) f(z) = P₀(z) + ∑ᵢ Pᵢ(z) log zᵢ` on `S`,
where `P₀` and the `Pᵢ` are polynomials. The theorem is proved on the whole slit domain, for
the regularized function `R_t(b; z)/Γ(c)` and so also for `R_t(b; z)`. There is no
restriction on the parameters: some or all of the `bᵢ` may be zero or negative.

The proof follows Carlson's. A negative parameter is raised to `0` by (5.9-7). A zero parameter
is deleted. With all `bᵢ ≥ 0`, the function is a polynomial when `t ≥ 0`, and a polynomial in
the `1/zᵢ` times powers when `c + t ≤ 0`. Otherwise, relation (1) of Section 8.5 (the first
relation of Exercise 5.9-6) lowers two parameters and raises `t`, and Zill's relation lowers one
parameter. The process ends in `R_t(β eᵢ; z) = zᵢ^t/Γ(β)` or in
`(zᵢ - zⱼ) R_{-1}(eᵢ + eⱼ; z) = log zᵢ - log zⱼ` (Exercise 5.9-13).

## Main definitions

* `Carlson.IsRationalOn S f`: `f` is a rational function of the nodes on `S`.
* `Carlson.IsLogRationalOn S f`: `f` is a rational function plus a rational combination of the
  logarithms of the nodes on `S`.

## Main results

* `Carlson.regCarlsonR_erase_zero`: deletion of a zero parameter on the slit domain.
* `Carlson.regCarlsonR_single`: `R_t(β eᵢ; z)/Γ(β) = zᵢ^t/Γ(β)`.
* `Carlson.regCarlsonR_single_add_single_log`:
  `(zᵢ - zⱼ) R_{-1}(eᵢ + eⱼ; z) = log zᵢ - log zⱼ` (Exercise 5.9-13 and (8.5-2)).
* `Carlson.isLogRationalOn_regCarlsonR`, `Carlson.isLogRationalOn_carlsonR`: Theorem 8.5-1.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §8.5.
-/

open Complex Set Filter Dirichlet MvPolynomial
open scoped Topology
@[expose] public noncomputable section

namespace Carlson

variable {ι : Type*}

/-! ### Rational and log-rational functions of the nodes -/

/-- A function `f` of the nodes is *rational* on `S` if `Q(z) f(z) = P(z)` on `S` for
polynomials `Q ≠ 0` and `P`. -/
def IsRationalOn (S : Set (ι → ℂ)) (f : (ι → ℂ) → ℂ) : Prop :=
  ∃ Q P : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ z ∈ S, eval z Q * f z = eval z P

variable [Fintype ι] in
/-- A function `f` of the nodes is *log-rational* on `S` if
`Q(z) f(z) = P₀(z) + ∑ᵢ Pᵢ(z) log zᵢ` on `S` for polynomials `Q ≠ 0`, `P₀` and `Pᵢ`. -/
def IsLogRationalOn (S : Set (ι → ℂ)) (f : (ι → ℂ) → ℂ) : Prop :=
  ∃ Q P₀ : MvPolynomial ι ℂ, ∃ P : ι → MvPolynomial ι ℂ, Q ≠ 0 ∧
    ∀ z ∈ S, eval z Q * f z = eval z P₀ + ∑ i, eval z (P i) * log (z i)

namespace IsRationalOn

variable {S : Set (ι → ℂ)} {f g : (ι → ℂ) → ℂ}

/-- Rationality depends only on the values on `S`. -/
theorem congr (hf : IsRationalOn S f) (hfg : EqOn f g S) : IsRationalOn S g := by
  obtain ⟨Q, P, hQ, h⟩ := hf
  exact ⟨Q, P, hQ, fun z hz => by rw [← hfg hz, h z hz]⟩

/-- Rationality passes to subsets. -/
theorem mono {T : Set (ι → ℂ)} (hf : IsRationalOn S f) (hTS : T ⊆ S) : IsRationalOn T f := by
  obtain ⟨Q, P, hQ, h⟩ := hf
  exact ⟨Q, P, hQ, fun z hz => h z (hTS hz)⟩

/-- A polynomial is rational. -/
theorem polynomial (P : MvPolynomial ι ℂ) : IsRationalOn S (fun z => eval z P) :=
  ⟨1, P, one_ne_zero, fun z _ => by simp⟩

/-- A constant is rational. -/
theorem const (c : ℂ) : IsRationalOn S (fun _ => c) := by
  simpa using polynomial (S := S) (C c)

/-- A node is rational. -/
theorem coord (i : ι) : IsRationalOn S (fun z => z i) := by
  simpa using polynomial (S := S) (X i)

/-- Division by a nonzero polynomial preserves rationality. -/
theorem of_mul_eq {R : MvPolynomial ι ℂ} (hR : R ≠ 0) (hf : IsRationalOn S f)
    (h : ∀ z ∈ S, eval z R * g z = f z) : IsRationalOn S g := by
  obtain ⟨Q, P, hQ, hf⟩ := hf
  refine ⟨Q * R, P, mul_ne_zero hQ hR, fun z hz => ?_⟩
  rw [map_mul, mul_assoc, h z hz, hf z hz]

/-- Sums of rational functions are rational. -/
theorem add (hf : IsRationalOn S f) (hg : IsRationalOn S g) :
    IsRationalOn S (fun z => f z + g z) := by
  obtain ⟨Q₁, P₁, hQ₁, h₁⟩ := hf
  obtain ⟨Q₂, P₂, hQ₂, h₂⟩ := hg
  refine ⟨Q₁ * Q₂, Q₂ * P₁ + Q₁ * P₂, mul_ne_zero hQ₁ hQ₂, fun z hz => ?_⟩
  simp only [map_mul, map_add]
  linear_combination eval z Q₂ * h₁ z hz + eval z Q₁ * h₂ z hz

/-- Products of rational functions are rational. -/
theorem mul (hf : IsRationalOn S f) (hg : IsRationalOn S g) :
    IsRationalOn S (fun z => f z * g z) := by
  obtain ⟨Q₁, P₁, hQ₁, h₁⟩ := hf
  obtain ⟨Q₂, P₂, hQ₂, h₂⟩ := hg
  refine ⟨Q₁ * Q₂, P₁ * P₂, mul_ne_zero hQ₁ hQ₂, fun z hz => ?_⟩
  simp only [map_mul]
  rw [← h₁ z hz, ← h₂ z hz]
  ring

/-- Powers of rational functions are rational. -/
theorem pow (hf : IsRationalOn S f) (n : ℕ) : IsRationalOn S (fun z => f z ^ n) := by
  induction n with
  | zero => simpa using const (S := S) 1
  | succ n ih => simpa [pow_succ] using ih.mul hf

/-- Finite sums of rational functions are rational. -/
theorem sum {α : Type*} (s : Finset α) {F : α → (ι → ℂ) → ℂ}
    (hF : ∀ a ∈ s, IsRationalOn S (F a)) : IsRationalOn S (fun z => ∑ a ∈ s, F a z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (S := S) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

/-- Finite products of rational functions are rational. -/
theorem prod {α : Type*} (s : Finset α) {F : α → (ι → ℂ) → ℂ}
    (hF : ∀ a ∈ s, IsRationalOn S (F a)) : IsRationalOn S (fun z => ∏ a ∈ s, F a z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (S := S) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).mul
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

/-- The reciprocal of a node is rational where the node does not vanish. -/
theorem inv_coord (i : ι) (hS : ∀ z ∈ S, z i ≠ 0) : IsRationalOn S (fun z => (z i)⁻¹) :=
  of_mul_eq (R := X i) (X_ne_zero i) (const 1) fun z hz => by
    rw [eval_X, mul_inv_cancel₀ (hS z hz)]

/-- An integer power of a node is rational where the node does not vanish. -/
theorem zpow_coord (i : ι) (hS : ∀ z ∈ S, z i ≠ 0) (n : ℤ) :
    IsRationalOn S (fun z => z i ^ n) := by
  cases n with
  | ofNat n => simpa using (coord (S := S) i).pow n
  | negSucc n => simpa [zpow_negSucc, inv_pow] using (inv_coord i hS).pow (n + 1)

end IsRationalOn

namespace IsLogRationalOn

variable [Fintype ι]

variable {S : Set (ι → ℂ)} {f g : (ι → ℂ) → ℂ}

/-- Log-rationality depends only on the values on `S`. -/
theorem congr (hf : IsLogRationalOn S f) (hfg : EqOn f g S) : IsLogRationalOn S g := by
  obtain ⟨Q, P₀, P, hQ, h⟩ := hf
  exact ⟨Q, P₀, P, hQ, fun z hz => by rw [← hfg hz, h z hz]⟩

/-- A rational function is log-rational. -/
theorem of_rational (hf : IsRationalOn S f) : IsLogRationalOn S f := by
  obtain ⟨Q, P, hQ, h⟩ := hf
  exact ⟨Q, P, 0, hQ, fun z hz => by simp [h z hz]⟩

/-- The logarithm of a node is log-rational. -/
theorem log_coord (i : ι) : IsLogRationalOn S (fun z => log (z i)) := by
  classical
  refine ⟨1, 0, Pi.single i 1, one_ne_zero, fun z _ => ?_⟩
  simp [Pi.single_apply]

/-- A rational multiple of a log-rational function is log-rational. -/
theorem rational_mul (hf : IsRationalOn S f) (hg : IsLogRationalOn S g) :
    IsLogRationalOn S (fun z => f z * g z) := by
  obtain ⟨Q₁, P₁, hQ₁, h₁⟩ := hf
  obtain ⟨Q₂, P₀, P, hQ₂, h₂⟩ := hg
  refine ⟨Q₁ * Q₂, P₁ * P₀, fun i => P₁ * P i, mul_ne_zero hQ₁ hQ₂, fun z hz => ?_⟩
  simp only [map_mul, mul_assoc, ← Finset.mul_sum, ← mul_add]
  rw [← h₂ z hz, ← h₁ z hz]
  ring

/-- A constant multiple of a log-rational function is log-rational. -/
theorem const_mul (c : ℂ) (hg : IsLogRationalOn S g) : IsLogRationalOn S (fun z => c * g z) :=
  rational_mul (IsRationalOn.const c) hg

/-- Sums of log-rational functions are log-rational. -/
theorem add (hf : IsLogRationalOn S f) (hg : IsLogRationalOn S g) :
    IsLogRationalOn S (fun z => f z + g z) := by
  obtain ⟨Q₁, P₀, P, hQ₁, h₁⟩ := hf
  obtain ⟨Q₂, P₀', P', hQ₂, h₂⟩ := hg
  refine ⟨Q₁ * Q₂, Q₂ * P₀ + Q₁ * P₀', fun i => Q₂ * P i + Q₁ * P' i, mul_ne_zero hQ₁ hQ₂,
    fun z hz => ?_⟩
  simp only [map_mul, map_add, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  linear_combination eval z Q₂ * h₁ z hz + eval z Q₁ * h₂ z hz

/-- Differences of log-rational functions are log-rational. -/
theorem sub (hf : IsLogRationalOn S f) (hg : IsLogRationalOn S g) :
    IsLogRationalOn S (fun z => f z - g z) := by
  simpa [sub_eq_add_neg] using hf.add (hg.const_mul (-1))

/-- Division by a nonzero polynomial preserves log-rationality. -/
theorem of_mul_eq {R : MvPolynomial ι ℂ} (hR : R ≠ 0) (hf : IsLogRationalOn S f)
    (h : ∀ z ∈ S, eval z R * g z = f z) : IsLogRationalOn S g := by
  obtain ⟨Q, P₀, P, hQ, hf⟩ := hf
  refine ⟨Q * R, P₀, P, mul_ne_zero hQ hR, fun z hz => ?_⟩
  rw [map_mul, mul_assoc, h z hz, hf z hz]

/-- A log-rational representation on the right half-plane extends to the slit domain for a
function holomorphic there. -/
theorem of_rightHalfPlane (hf : AnalyticOnNhd ℂ f carlsonRSlitDomain)
    (h : IsLogRationalOn carlsonRVariableDomain f) : IsLogRationalOn carlsonRSlitDomain f := by
  obtain ⟨Q, P₀, P, hQ, h⟩ := h
  have hpoly (R : MvPolynomial ι ℂ) : AnalyticOnNhd ℂ (fun z : ι → ℂ => eval z R) univ :=
    AnalyticOnNhd.eval_mvPolynomial R
  refine ⟨Q, P₀, P, hQ, fun z hz => ?_⟩
  refine eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane (fun w hw => ?_) (fun w hw => ?_)
    (fun w hw => h w hw) hz
  · exact (hpoly Q w (mem_univ w)).mul (hf w hw)
  · refine (hpoly P₀ w (mem_univ w)).add (Finset.analyticAt_fun_sum _ fun i _ => ?_)
    exact (hpoly (P i) w (mem_univ w)).mul
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt w).clog (hw i))

end IsLogRationalOn

/-! ### Deleting a zero parameter; the one-node and two-node base cases -/

section Base

variable [Fintype ι]

/-- Deletion of a zero parameter on the right half-plane. -/
private theorem regCarlsonR_erase_zero_right [DecidableEq ι] (t : ℂ) {b : ι → ℂ} (k : ι)
    (hb : b k = 0) (hne : ∃ i, i ≠ k) {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonR t b z = regCarlsonR t (eraseCarlsonParameter k b) (eraseCarlsonVariable k z) := by
  obtain ⟨i, hi⟩ := hne
  have : Nonempty {j // j ≠ k} := ⟨⟨i, hi⟩⟩
  set e := Equiv.optionSubtypeNe k
  have hagg : stdSimplexAggregate e (b ∘ e) = b := by
    funext j
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    have : (Finset.univ.filter fun x => e x = j) = {e.symm j} := by
      ext x; simp [Equiv.eq_symm_apply]
    rw [this, Finset.sum_singleton]
    simp
  have h := regCarlsonR_aggregate e.surjective t hz (b ∘ e)
  rw [hagg] at h
  rw [← h, regCarlsonR_option_zero t (b := b ∘ e) (z := z ∘ e) hb
    (carlsonRVariableDomain_subset_slitDomain fun o => hz (e o))]
  rfl

/-- **Deletion of a zero parameter** on the slit domain:
`R_t(b; z) = R_t(b'; z')` when `b_k = 0`, where `b'` and `z'` omit the coordinate `k`. -/
theorem regCarlsonR_erase_zero [DecidableEq ι] (t : ℂ) {b : ι → ℂ} (k : ι) (hb : b k = 0)
    (hne : ∃ i, i ≠ k) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR t b z = regCarlsonR t (eraseCarlsonParameter k b) (eraseCarlsonVariable k z) := by
  have hcomp : AnalyticOnNhd ℂ (fun w : ι → ℂ =>
      regCarlsonR t (eraseCarlsonParameter k b) (eraseCarlsonVariable k w)) carlsonRSlitDomain :=
    fun w hw => analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
      (analyticAt_pi_iff.mpr fun j => (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : ι => ℂ) j.1).analyticAt w) (fun j => hw j.1)
  exact eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane (analyticOnNhd_regCarlsonR t _) hcomp
    (fun w hw => regCarlsonR_erase_zero_right t k hb hne hw) hz

/-- One nonzero parameter on the right half-plane, by deleting the zero parameters. -/
private theorem regCarlsonR_single_right (t β : ℂ) (κ : Type*) [Fintype κ] :
    ∀ [DecidableEq κ] (i : κ) {z : κ → ℂ}, z ∈ carlsonRVariableDomain →
      regCarlsonR t (Pi.single i β) z = z i ^ t * (Gamma β)⁻¹ := by
  refine Fintype.induction_subsingleton_or_nontrivial (P := fun α _ => ∀ [DecidableEq α] (i : α)
    {z : α → ℂ}, z ∈ carlsonRVariableDomain →
      regCarlsonR t (Pi.single i β) z = z i ^ t * (Gamma β)⁻¹) κ ?_ ?_
  · intro α _ _ _ i z hz
    have hzc : z = fun _ => z i := funext fun j => by rw [Subsingleton.elim j i]
    rw [show regCarlsonR t (Pi.single i β) z = regCarlsonR t (Pi.single i β) (fun _ => z i) by
      rw [← hzc], regCarlsonR_const_node t _ (carlsonRightHalfPlane_subset_slitPlane (hz i))]
    simp
  · intro α _ _ ih _ i z hz
    obtain ⟨k, hk⟩ := exists_ne i
    rw [regCarlsonR_erase_zero_right t k (by simp [hk]) ⟨i, hk.symm⟩ hz]
    have hcard : Fintype.card {j // j ≠ k} < Fintype.card α :=
      Fintype.card_subtype_lt (p := fun j => j ≠ k) (x := k) (by simp)
    have herase : eraseCarlsonParameter k (Pi.single i β) =
        Pi.single (⟨i, hk.symm⟩ : {j // j ≠ k}) β := by
      funext j
      simp [eraseCarlsonParameter, Pi.single_apply, Subtype.ext_iff]
    rw [herase]
    exact ih _ hcard ⟨i, hk.symm⟩ (z := eraseCarlsonVariable k z) (fun j => hz j)

/-- **One nonzero parameter**: `R_t(β eᵢ; z)/Γ(β) = zᵢ^t/Γ(β)` on the slit domain. -/
theorem regCarlsonR_single [DecidableEq ι] (t β : ℂ) (i : ι) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR t (Pi.single i β) z = z i ^ t * (Gamma β)⁻¹ := by
  have hG : AnalyticOnNhd ℂ (fun w : ι → ℂ => w i ^ t * (Gamma β)⁻¹) carlsonRSlitDomain :=
    fun w hw => (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt w).cpow
      analyticAt_const (hw i)).mul analyticAt_const
  exact eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane (analyticOnNhd_regCarlsonR t _) hG
    (fun w hw => regCarlsonR_single_right t β ι i hw) hz

open scoped Classical in
/-- **Carlson's (8.5-2)** (Exercise 5.9-13) for any number of variables:
`(zᵢ - zⱼ) R_{-1}(eᵢ + eⱼ; z) = log zᵢ - log zⱼ` on the slit domain. -/
theorem regCarlsonR_single_add_single_log (i j : ι) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    (z i - z j) * regCarlsonR (-1) (Pi.single i 1 + Pi.single j 1) z =
      log (z i) - log (z j) := by
  set b : ι → ℂ := Pi.single i 1 + Pi.single j 1
  have hpow : ∀ t : ℂ, t * ((z i - z j) * regCarlsonR (t - 1) b z) = z i ^ t - z j ^ t := by
    intro t
    have h := regCarlsonR_tangent_sub t b hz i j
    have hbj : b - Pi.single j 1 = Pi.single i 1 := by simp [b]
    have hbi : b - Pi.single i 1 = Pi.single j 1 := by
      simp only [b]; abel
    rw [hbj, hbi, regCarlsonR_single t 1 i hz, regCarlsonR_single t 1 j hz] at h
    simp only [Gamma_one, inv_one, mul_one] at h
    linear_combination h
  set F : ℂ → ℂ := fun t => (z i - z j) * regCarlsonR (t - 1) b z
  have hF : ContinuousAt F 0 := by
    have h := analyticAt_regCarlsonR_comp (t := fun s : ℂ => s - 1)
      (b := fun _ => b) (z := fun _ => z) (p := (0 : ℂ))
      (analyticAt_id.sub analyticAt_const) analyticAt_const analyticAt_const hz
    exact continuousAt_const.mul h.continuousAt
  have hslope : ∀ w : ℂ, w ≠ 0 → Tendsto (fun t : ℂ => t⁻¹ * (w ^ t - 1)) (𝓝[≠] 0)
      (𝓝 (log w)) := by
    intro w hw
    have hd : HasDerivAt (fun t : ℂ => w ^ t) (w ^ (0 : ℂ) * log w * 1) 0 :=
      (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl hw)
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    simpa using hd
  have hlim : Tendsto F (𝓝[≠] 0) (𝓝 (log (z i) - log (z j))) := by
    have := (hslope (z i) (slitPlane_ne_zero (hz i))).sub
      (hslope (z j) (slitPlane_ne_zero (hz j)))
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    have h := hpow t
    simp only [F]
    field_simp
    linear_combination -h
  have := tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds) hlim
  simpa [F] using this

end Base

/-! ### Theorem 8.5-1 -/

section Main

variable [Fintype ι]

/-- At a natural exponent the regularized `R` function is a polynomial in the nodes. -/
theorem isLogRationalOn_regCarlsonR_natCast (n : ℕ) (b : ι → ℂ) :
    IsLogRationalOn carlsonRSlitDomain (regCarlsonR n b) := by
  classical
  refine IsLogRationalOn.of_rightHalfPlane (analyticOnNhd_regCarlsonR _ b)
    (IsLogRationalOn.of_rational (IsRationalOn.congr (f := fun z =>
      (∑ m ∈ Finset.piAntidiag Finset.univ n, (Nat.multinomial Finset.univ m : ℂ) *
        (∏ i, z i ^ m i) * ∏ i, (ascPochhammer ℂ (m i)).eval (b i)) *
          (Gamma ((∑ i, b i) + n))⁻¹) ?_ fun z hz => ?_))
  · exact (IsRationalOn.sum _ fun m _ => ((IsRationalOn.const _).mul
      (IsRationalOn.prod _ fun i _ => (IsRationalOn.coord i).pow _)).mul
        (IsRationalOn.const _)).mul (IsRationalOn.const _)
  · beta_reduce
    rw [regCarlsonR_natCast n b (carlsonRVariableDomain_subset_slitDomain hz),
      regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
      carlsonRPolynomialNumerator_eq_multinomial_sum]

/-- When the parameters are integers and `c + t` is a nonpositive integer, the regularized `R`
function is rational in the nodes. -/
theorem isLogRationalOn_regCarlsonR_neg_sum_sub_nat (N : ℕ) (m : ι → ℤ) :
    IsLogRationalOn carlsonRSlitDomain (regCarlsonR (-(∑ i, (m i : ℂ)) - N) (fun i => m i)) := by
  classical
  have hS : ∀ z ∈ (carlsonRVariableDomain : Set (ι → ℂ)), ∀ i, z i ≠ 0 := fun z hz i =>
    slitPlane_ne_zero (carlsonRVariableDomain_subset_slitDomain hz i)
  refine IsLogRationalOn.of_rightHalfPlane (analyticOnNhd_regCarlsonR _ _)
    (IsLogRationalOn.of_rational (IsRationalOn.congr (f := fun z =>
      (∏ i, z i ^ (-m i)) * ((∑ k ∈ Finset.piAntidiag Finset.univ N,
        (Nat.multinomial Finset.univ k : ℂ) * (∏ i, (z i)⁻¹ ^ k i) *
          ∏ i, (ascPochhammer ℂ (k i)).eval (m i : ℂ)) *
            (Gamma ((∑ i, (m i : ℂ)) + N))⁻¹)) ?_ fun z hz => ?_))
  · exact (IsRationalOn.prod _ fun i _ => IsRationalOn.zpow_coord i (fun z hz => hS z hz i) _).mul
      ((IsRationalOn.sum _ fun k _ => ((IsRationalOn.const _).mul
        (IsRationalOn.prod _ fun i _ =>
          (IsRationalOn.inv_coord i (fun z hz => hS z hz i)).pow _)).mul
            (IsRationalOn.const _)).mul (IsRationalOn.const _))
  · beta_reduce
    rw [regCarlsonR_neg_sum_sub_nat_int N m (carlsonRVariableDomain_subset_slitDomain hz),
      regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
      carlsonRPolynomialNumerator_eq_multinomial_sum]

omit [Fintype ι] in
/-- Lowering a positive natural parameter by one, cast to `ℂ`. -/
private theorem cast_sub_single [DecidableEq ι] {b : ι → ℕ} {j : ι} (hj : 1 ≤ b j) :
    (fun l => ((b - Pi.single j 1 : ι → ℕ) l : ℂ)) = (fun l => (b l : ℂ)) - Pi.single j 1 := by
  funext l
  by_cases h : l = j
  · subst h; simp [Nat.cast_sub hj]
  · simp [h]

/-- Lowering a positive natural parameter by one lowers the sum by one. -/
private theorem sum_sub_single [DecidableEq ι] {b : ι → ℕ} {j : ι} (hj : 1 ≤ b j) :
    ∑ l, (b - Pi.single j 1 : ι → ℕ) l + 1 = ∑ l, b l := by
  have h : ∀ l, (b - Pi.single j 1 : ι → ℕ) l + (if l = j then 1 else 0) = b l := by
    intro l
    by_cases h : l = j
    · subst h; simp; omega
    · simp [h]
  rw [← Finset.sum_congr rfl fun l _ => h l, Finset.sum_add_distrib]
  simp

/-- A natural parameter vector with positive sum has two positive entries or is supported on one
node. -/
private theorem exists_pair_or_single [DecidableEq ι] (b : ι → ℕ) {n : ℕ} (hb : ∑ l, b l = n)
    (hn : 1 ≤ n) : (∃ i j, i ≠ j ∧ 1 ≤ b i ∧ 1 ≤ b j) ∨ ∃ i, b = Pi.single i n := by
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, b i ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by omega)
  by_cases h : ∃ j, j ≠ i ∧ 1 ≤ b j
  · obtain ⟨j, hji, hj⟩ := h
    exact Or.inl ⟨i, j, hji.symm, by omega, hj⟩
  · push Not at h
    refine Or.inr ⟨i, ?_⟩
    have hz : ∀ j, j ≠ i → b j = 0 := fun j hj => by have := h j hj; omega
    have hbi : b i = n := by
      rw [← hb, Finset.sum_eq_single i (fun j _ hj => hz j hj) (by simp)]
    funext j
    by_cases hj : j = i
    · subst hj; simp [hbi]
    · simp [hj, hz j hj]

open scoped Classical in
/-- Theorem 8.5-1 for natural parameters, by induction on their sum. -/
private theorem isLogRationalOn_regCarlsonR_nat (n : ℕ) : ∀ (b : ι → ℕ), ∑ l, b l = n →
    ∀ t : ℤ, IsLogRationalOn carlsonRSlitDomain (regCarlsonR t (fun l => (b l : ℂ))) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b hb t
  have hc : ∑ l, (b l : ℂ) = n := by rw [← hb]; push_cast; rfl
  -- a natural exponent: a polynomial
  rcases le_or_gt 0 t with ht | ht
  · lift t to ℕ using ht
    simpa using isLogRationalOn_regCarlsonR_natCast t (fun l => (b l : ℂ))
  -- `c + t ≤ 0`: a rational function
  rcases le_or_gt ((n : ℤ) + t) 0 with hnt | hnt
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = -((n : ℤ) + t) :=
      ⟨(-((n : ℤ) + t)).toNat, Int.toNat_of_nonneg (by omega)⟩
    have htN : (t : ℂ) = -(∑ l, (((b l : ℤ)) : ℂ)) - N := by
      have : ((N : ℤ) : ℂ) = ((-((n : ℤ) + t) : ℤ) : ℂ) := by rw [hN]
      push_cast at this ⊢
      rw [hc, this]
      ring
    rw [htN]
    simpa using isLogRationalOn_regCarlsonR_neg_sum_sub_nat N (fun l => (b l : ℤ))
  obtain ⟨i, j, hij, hi, hj⟩ | ⟨i, hbi⟩ := exists_pair_or_single b hb (by omega)
  · -- two positive parameters
    have hXij : (X i - X j : MvPolynomial ι ℂ) ≠ 0 := sub_ne_zero.mpr (X_injective.ne hij)
    have hbi := cast_sub_single hi
    have hbj := cast_sub_single hj
    have hsi := sum_sub_single hi
    have hsj := sum_sub_single hj
    by_cases ht1 : t = -1
    · subst ht1
      by_cases hn2 : n = 2
      · -- `b = eᵢ + eⱼ`: the logarithmic base case
        have hj' : 1 ≤ (b - Pi.single i 1 : ι → ℕ) j := by simp [hij.symm]; exact hj
        have hsij := sum_sub_single hj'
        have h0 : (b - Pi.single i 1 - Pi.single j 1 : ι → ℕ) = 0 := by
          have : ∑ l, (b - Pi.single i 1 - Pi.single j 1 : ι → ℕ) l = 0 := by omega
          funext l
          exact (Finset.sum_eq_zero_iff.mp this) l (Finset.mem_univ l)
        have hcast : (fun l => (b l : ℂ)) = Pi.single i 1 + Pi.single j 1 := by
          have h1 := cast_sub_single hj'
          rw [hbi, h0] at h1
          funext l
          have := congrFun h1 l
          simp only [Pi.zero_apply, Nat.cast_zero, Pi.sub_apply] at this
          simp only [Pi.add_apply]
          linear_combination -this
        rw [hcast]
        refine IsLogRationalOn.of_mul_eq hXij
          ((IsLogRationalOn.log_coord i).sub (IsLogRationalOn.log_coord j)) fun z hz => ?_
        simpa using regCarlsonR_single_add_single_log i j hz
      · -- Zill's relation lowers one parameter
        have hn3 : (n : ℂ) - 2 ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast (by omega : n ≠ 2)
        refine IsLogRationalOn.of_mul_eq (R := C ((n : ℂ) - 2) * (X i - X j))
          (mul_ne_zero (by rwa [Ne, C_eq_zero]) hXij)
          ((IsLogRationalOn.rational_mul (IsRationalOn.coord i)
            (ih _ (by omega) (b - Pi.single j 1) rfl (-1))).sub
            (IsLogRationalOn.rational_mul (IsRationalOn.coord j)
            (ih _ (by omega) (b - Pi.single i 1) rfl (-1))))
          fun z hz => ?_
        have h := regCarlsonR_zill ((-1 : ℤ) : ℂ) (fun l => (b l : ℂ)) hz i j
        rw [← hbi, ← hbj, hc] at h
        simp only [map_mul, eval_C, map_sub, eval_X]
        push_cast at h ⊢
        linear_combination h
    · -- relation (8.5-1) lowers two parameters and raises the exponent
      have ht1' : (t : ℂ) + 1 ≠ 0 := by
        intro h; apply ht1; exact_mod_cast (eq_neg_of_add_eq_zero_left h)
      refine IsLogRationalOn.of_mul_eq (R := C ((t : ℂ) + 1) * (X i - X j))
        (mul_ne_zero (by rwa [Ne, C_eq_zero]) hXij)
        ((ih _ (by omega) (b - Pi.single j 1) rfl (t + 1)).sub
          (ih _ (by omega) (b - Pi.single i 1) rfl (t + 1))) fun z hz => ?_
      have h := regCarlsonR_tangent_sub ((t : ℂ) + 1) (fun l => (b l : ℂ)) hz i j
      rw [← hbi, ← hbj, show (t : ℂ) + 1 - 1 = t by ring] at h
      simp only [map_mul, eval_C, map_sub, eval_X]
      push_cast
      linear_combination h
  · -- one node: a power
    have hcast : (fun l => (b l : ℂ)) = Pi.single i (n : ℂ) := by
      rw [hbi]; funext l; by_cases h : l = i
      · subst h; simp
      · simp [h]
    rw [hcast]
    refine IsLogRationalOn.of_rational (IsRationalOn.congr
      ((IsRationalOn.zpow_coord (S := carlsonRSlitDomain) i
        (fun z hz => slitPlane_ne_zero (hz i)) t).mul (IsRationalOn.const (Gamma n)⁻¹))
          fun z hz => ?_)
    rw [regCarlsonR_single _ _ i hz, cpow_intCast]

open scoped Classical in
/-- **Carlson's Theorem 8.5-1**, regularized: if the exponent `t = -a` and all the parameters
`bᵢ` are integers, then `R_t(b; z)/Γ(c)` is log-rational on the slit domain. There is some
nonzero polynomial `Q` with `Q(z) R_t(b; z)/Γ(c) = P₀(z) + ∑ᵢ Pᵢ(z) log zᵢ` for polynomials
`P₀` and `Pᵢ`. -/
theorem isLogRationalOn_regCarlsonR (t : ℤ) (b : ι → ℤ) :
    IsLogRationalOn carlsonRSlitDomain (regCarlsonR t (fun l => (b l : ℂ))) := by
  obtain ⟨M, hM⟩ : ∃ M, ∑ l, (-b l).toNat = M := ⟨_, rfl⟩
  induction M generalizing b t with
  | zero =>
    have hb : ∀ l, 0 ≤ b l := fun l => by
      have := (Finset.sum_eq_zero_iff.mp hM) l (Finset.mem_univ _); omega
    have hcast : (fun l => (b l : ℂ)) = fun l => ((b l).toNat : ℂ) := funext fun l => by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hb l)]
    rw [hcast]
    exact isLogRationalOn_regCarlsonR_nat _ (fun l => (b l).toNat) rfl t
  | succ M ih =>
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, (-b i).toNat ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by omega)
    set b' : ι → ℤ := b + Pi.single i 1
    have hM' : ∑ l, (-b' l).toNat = M := by
      have h : ∀ l, (-b' l).toNat + (if l = i then 1 else 0) = (-b l).toNat := by
        intro l
        by_cases h : l = i
        · subst h; simp [b']; omega
        · simp [b', h]
      rw [← Finset.sum_congr rfl fun l _ => h l, Finset.sum_add_distrib] at hM
      simp at hM
      omega
    have hcast : (fun l => (b l : ℂ)) = (fun l => (b' l : ℂ)) - Pi.single i 1 := by
      funext l
      by_cases h : l = i
      · subst h; simp [b']
      · simp [b', Pi.single_apply, h]
    refine IsLogRationalOn.congr ((IsLogRationalOn.const_mul ((∑ l, (b' l : ℂ)) + t - 1)
      (ih t b' hM')).sub (IsLogRationalOn.rational_mul ((IsRationalOn.const (t : ℂ)).mul
        (IsRationalOn.coord i)) (ih (t - 1) b' hM'))) fun z hz => ?_
    rw [hcast, regCarlsonR_sub_dirichletUnit _ _ hz i]
    push_cast
    ring

/-- **Carlson's Theorem 8.5-1**: if the exponent `t = -a` and all the parameters `bᵢ` are
integers, then `R_t(b; z)` is log-rational on the slit domain. -/
theorem isLogRationalOn_carlsonR (t : ℤ) (b : ι → ℤ) :
    IsLogRationalOn carlsonRSlitDomain (carlsonR t (fun l => (b l : ℂ))) :=
  IsLogRationalOn.const_mul _ (isLogRationalOn_regCarlsonR t b)

end Main

end Carlson
