/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The next-to-highest elementary symmetric mean

The sum of products omitting one variable is maximized, at fixed nonnegative
sum, when all variables are equal. This is the case of Maclaurin's inequality
used in Carlson's 1966 capacity bound. The proof averages a pair of coordinates
at a maximum on the compact simplex.
-/

open Set
open scoped Topology
@[expose] public noncomputable section
namespace Finset
variable {ι : Type*} [DecidableEq ι]

/-- The elementary symmetric sum of degree one less than the size of a finite set. -/
def prodEraseSum (s : Finset ι) (y : ι → ℝ) : ℝ := ∑ i ∈ s, ∏ j ∈ s.erase i, y j

/-- Adjoining a variable gives the usual elementary-symmetric recurrence. -/
theorem prodEraseSum_insert (s : Finset ι) {i : ι} (hi : i ∉ s) (y : ι → ℝ) :
    prodEraseSum (insert i s) y = (∏ j ∈ s, y j) + y i * prodEraseSum s y := by
  unfold prodEraseSum
  rw [sum_insert hi, erase_insert hi]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  have hji : j ≠ i := ne_of_mem_of_not_mem hj hi
  rw [erase_insert_of_ne hji.symm, prod_insert (by simp [hi])]

/-- Separating two coordinates in the next-to-highest elementary symmetric sum. -/
theorem prodEraseSum_pair (s : Finset ι) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) (y : ι → ℝ) :
    prodEraseSum s y = (y i + y j) * (∏ k ∈ (s.erase i).erase j, y k) +
      y i * y j * prodEraseSum ((s.erase i).erase j) y := by
  let T := (s.erase i).erase j
  have hTi : i ∉ T := by simp [T]
  have hTj : j ∉ T := by simp [T]
  have hs : s = insert i (insert j T) := by ext k; simp [T]; grind
  conv_lhs =>
    rw [hs, prodEraseSum_insert _ (by simp [hij, hTi]), prodEraseSum_insert _ hTj,
      prod_insert hTj]
  ring

/-- Changing only two coordinates leaves products on the complementary set unchanged. -/
theorem prodEraseSum_update_pair (s : Finset ι) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) (y : ι → ℝ) (a b : ℝ) :
    prodEraseSum s (Function.update (Function.update y i a) j b) =
      (a + b) * (∏ k ∈ (s.erase i).erase j, y k) +
        a * b * prodEraseSum ((s.erase i).erase j) y := by
  rw [prodEraseSum_pair s hi hj hij]
  have he (k : ι) (hk : k ∈ (s.erase i).erase j) :
      Function.update (Function.update y i a) j b k = y k := by
    simp only [mem_erase] at hk
    simp [hk.1, hk.2.1]
  have hp : (∏ k ∈ (s.erase i).erase j,
      Function.update (Function.update y i a) j b k) = ∏ k ∈ (s.erase i).erase j, y k :=
    prod_congr rfl he
  have hE : prodEraseSum ((s.erase i).erase j)
      (Function.update (Function.update y i a) j b) = prodEraseSum ((s.erase i).erase j) y := by
    unfold prodEraseSum
    apply sum_congr rfl
    intro k hk
    exact prod_congr rfl (fun l hl => he l (mem_of_mem_erase hl))
  simp only [Function.update_self, Function.update_of_ne hij, hp, hE]

end Finset

namespace Finset
variable {ι : Type*} [DecidableEq ι]

/-- The complementary elementary symmetric coefficient is positive if at most one
coordinate vanishes and the complementary set is nonempty. -/
theorem prodEraseSum_pos_of_except_one {s : Finset ι} (hs : s.Nonempty) {y : ι → ℝ}
    (hy : ∀ i ∈ s, 0 ≤ y i) (hgood : ∃ r : ι, ∀ i ∈ s, i ≠ r → 0 < y i) :
    0 < prodEraseSum s y := by
  obtain ⟨r, hr⟩ := hgood
  obtain ⟨k, hk, hkr⟩ : ∃ k ∈ s, ∀ i ∈ s.erase k, i ≠ r := by
    by_cases hrs : r ∈ s
    · exact ⟨r, hrs, fun i hi => (mem_erase.mp hi).1⟩
    · obtain ⟨k, hk⟩ := hs
      exact ⟨k, hk, fun i hi hir => hrs (hir ▸ mem_of_mem_erase hi)⟩
  have hp : 0 < ∏ i ∈ s.erase k, y i :=
    prod_pos (fun i hi => hr i (mem_of_mem_erase hi) (hkr i hi))
  apply hp.trans_le
  exact single_le_sum (f := fun i => ∏ j ∈ s.erase i, y j)
    (fun i _ => prod_nonneg fun j hj => hy j (mem_of_mem_erase hj)) hk

/-- Averaging an unequal pair strictly increases the symmetric sum if at most
one of the original coordinates vanishes. -/
theorem prodEraseSum_lt_update_average {s : Finset ι} (hn : 3 ≤ s.card) {y : ι → ℝ}
    (hy : ∀ i ∈ s, 0 ≤ y i) (hgood : ∃ r : ι, ∀ i ∈ s, i ≠ r → 0 < y i)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hne : y i ≠ y j) :
    prodEraseSum s y < prodEraseSum s
      (Function.update (Function.update y i ((y i + y j) / 2)) j ((y i + y j) / 2)) := by
  have hij : i ≠ j := fun h => hne (congrArg y h)
  have hT : ((s.erase i).erase j).Nonempty := by
    apply card_pos.mp
    have h1 := card_erase_add_one hi
    have h2 := card_erase_add_one (mem_erase.mpr ⟨hij.symm, hj⟩ : j ∈ s.erase i)
    omega
  have hpos := prodEraseSum_pos_of_except_one hT
    (fun k hk => hy k (mem_of_mem_erase (mem_of_mem_erase hk)))
    (by obtain ⟨r, hr⟩ := hgood
        exact ⟨r, fun k hk hkr => hr k (mem_of_mem_erase (mem_of_mem_erase hk)) hkr⟩)
  rw [prodEraseSum_update_pair s hi hj hij, prodEraseSum_pair s hi hj hij]
  have hp := mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) hpos
  nlinarith

end Finset

namespace Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A maximum on the positive-mass simplex has positive symmetric sum. -/
private theorem prodEraseSum_pos_of_max {S : ℝ} (hS : 0 < S) {z : ι → ℝ}
    (hmax : ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) → (∑ i, y i) = S →
      Finset.prodEraseSum Finset.univ y ≤ Finset.prodEraseSum Finset.univ z) :
    0 < Finset.prodEraseSum Finset.univ z := by
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := by
    change (0 : ℝ) < Fintype.card ι
    exact_mod_cast (Fintype.card_pos (α := ι))
  have hconst : Finset.prodEraseSum Finset.univ (fun _ : ι => S / N) =
      N * (S / N) ^ (Fintype.card ι - 1) := by simp [Finset.prodEraseSum, N, div_pow]
  apply (show 0 < N * (S / N) ^ (Fintype.card ι - 1) by positivity).trans_le
  rw [← hconst]
  apply hmax _ (fun _ => (div_pos hS hN).le)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change N * (S / N) = S
  field_simp

/-- A maximizer of the next-to-highest symmetric sum on a positive-mass simplex
has all its coordinates equal. -/
private theorem prodEraseSum_max_constant {S : ℝ} (hS : 0 < S)
    (hn : 3 ≤ Fintype.card ι) {z : ι → ℝ}
    (hz : (∀ i, 0 ≤ z i) ∧ ∑ i, z i = S)
    (hmax : ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) → (∑ i, y i) = S →
      Finset.prodEraseSum Finset.univ y ≤ Finset.prodEraseSum Finset.univ z) :
    ∀ i j, z i = z j := by
  have hpos := prodEraseSum_pos_of_max hS hmax
  obtain ⟨r, hr⟩ : ∃ r : ι, 0 < ∏ k ∈ Finset.univ.erase r, z k := by
    by_contra h
    push Not at h
    have hh : Finset.prodEraseSum Finset.univ z ≤ 0 :=
      Finset.sum_nonpos (fun i _ => h i)
    exact (not_le_of_gt hpos) hh
  have hgood : ∀ k : ι, k ≠ r → 0 < z k := by
    intro k hkr
    by_contra hk
    have hzero : z k = 0 := le_antisymm (not_lt.mp hk) (hz.1 k)
    have he := Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkr, Finset.mem_univ k⟩) hzero
    rw [he] at hr
    exact lt_irrefl 0 hr
  intro i j
  by_contra hij
  let m := (z i + z j) / 2
  let y := Function.update (Function.update z i m) j m
  have hne : i ≠ j := fun h => hij (congrArg z h)
  have hy : ∀ k, 0 ≤ y k := by
    intro k
    have hm : 0 ≤ m := div_nonneg (add_nonneg (hz.1 i) (hz.1 j)) (by norm_num)
    by_cases hkj : k = j
    · subst k; simpa [y] using hm
    · by_cases hki : k = i
      · subst k; simpa [y, hkj] using hm
      · simpa [y, hkj, hki] using hz.1 k
  have hup (v : ι → ℝ) (k : ι) (a : ℝ) :
      (∑ l, Function.update v k a l) = (∑ l, v l) - v k + a := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase,
      Finset.sum_erase_eq_sub (Finset.mem_univ k)]
    ring
  have hys : ∑ k, y k = S := by
    dsimp only [y]
    rw [hup, hup, Function.update_of_ne hne.symm]
    dsimp [m]
    linarith [hz.2]
  have hlt := Finset.prodEraseSum_lt_update_average (by simpa using hn)
    (fun k _ => hz.1 k) ⟨r, fun k _ hkr => hgood k hkr⟩
    (Finset.mem_univ i) (Finset.mem_univ j) hij
  exact (not_lt_of_ge (hmax y hy hys)) hlt

/-- **Maclaurin's inequality at degree `n-1`.** The elementary symmetric sum
is bounded by `n` times the arithmetic mean to degree `n-1`. -/
theorem prodEraseSum_le_arithmetic_pow {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i)
    (hS : 0 < ∑ i, y i) (hn : 3 ≤ Fintype.card ι) :
    Finset.prodEraseSum Finset.univ y ≤
      Fintype.card ι * ((∑ i, y i) / Fintype.card ι) ^ (Fintype.card ι - 1) := by
  let S := ∑ i, y i
  let K : Set (ι → ℝ) := {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = S}
  have hclosed : IsClosed K := by
    change IsClosed ({z : ι → ℝ | ∀ i, 0 ≤ z i} ∩ {z | ∑ i, z i = S})
    apply IsClosed.inter
    · simpa only [ofPred_forall] using
        isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
    · exact isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const
  have hcompact : IsCompact K :=
    (isCompact_Icc (a := (fun _ : ι => (0 : ℝ))) (b := fun _ => S)).of_isClosed_subset hclosed (by
    intro z hz
    exact ⟨fun i => hz.1 i, fun i => by
      rw [← hz.2]
      exact Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ i)⟩)
  have hcont : Continuous (fun z : ι → ℝ => Finset.prodEraseSum Finset.univ z) := by
    unfold Finset.prodEraseSum
    fun_prop
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn ⟨y, hy, rfl⟩ hcont.continuousOn
  have hc := prodEraseSum_max_constant hS hn hz
    (fun v hv hvs => hmax ⟨hv, hvs⟩)
  let i : ι := Classical.arbitrary ι
  have hzi : z i = S / Fintype.card ι := by
    have hs := hz.2
    have hsum : (∑ k, z k) = Fintype.card ι * z i := by
      calc
        _ = ∑ _k : ι, z i := Finset.sum_congr rfl (fun k _ => hc k i)
        _ = _ := by simp
    rw [hsum] at hs
    exact (eq_div_iff (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card ι : ℝ) ≠ 0)).mpr
      (by linarith)
  have he : Finset.prodEraseSum Finset.univ z =
      Fintype.card ι * (S / Fintype.card ι) ^ (Fintype.card ι - 1) := by
    have hz' : z = fun _ => S / Fintype.card ι := funext (fun j => (hc j i).trans hzi)
    simp [hz', Finset.prodEraseSum, div_pow]
  exact (hmax ⟨hy, rfl⟩).trans_eq he

/-- The next-to-highest Maclaurin inequality is strict for positive nonconstant inputs. -/
theorem prodEraseSum_lt_arithmetic_pow {y : ι → ℝ} (hy : ∀ i, 0 < y i)
    (hn : 3 ≤ Fintype.card ι) (hne : ∃ i j, y i ≠ y j) :
    Finset.prodEraseSum Finset.univ y <
      Fintype.card ι * ((∑ i, y i) / Fintype.card ι) ^ (Fintype.card ι - 1) := by
  have hS : 0 < ∑ i, y i := Finset.sum_pos (fun i _ => hy i) Finset.univ_nonempty
  apply lt_of_le_of_ne (prodEraseSum_le_arithmetic_pow (fun i => (hy i).le) hS hn)
  intro he
  have hc := prodEraseSum_max_constant hS hn ⟨fun i => (hy i).le, rfl⟩
    (fun v hv hvs => by
      have hh := prodEraseSum_le_arithmetic_pow hv (by rw [hvs]; exact hS) hn
      rw [hvs, ← he] at hh
      exact hh)
  obtain ⟨i, j, hij⟩ := hne
  exact hij (hc i j)

/-- The product-times-reciprocal-sum formulation of Maclaurin's inequality. -/
theorem prod_mul_sum_inv_lt_arithmetic_pow {y : ι → ℝ} (hy : ∀ i, 0 < y i)
    (hn : 3 ≤ Fintype.card ι) (hne : ∃ i j, y i ≠ y j) :
    (∏ i, y i) * (∑ i, (y i)⁻¹) <
      Fintype.card ι * ((∑ i, y i) / Fintype.card ι) ^ (Fintype.card ι - 1) := by
  have he : Finset.prodEraseSum Finset.univ y = (∏ i, y i) * (∑ i, (y i)⁻¹) := by
    unfold Finset.prodEraseSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← div_eq_mul_inv, eq_div_iff (hy i).ne']
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  rw [← he]
  exact prodEraseSum_lt_arithmetic_pow hy hn hne

end Real
