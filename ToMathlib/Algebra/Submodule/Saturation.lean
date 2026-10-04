/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Order.Closure

/-!
# Saturation of submodules

`P.IsSaturated S` means that `r • x ∈ P` implies `x ∈ P` for every `r ∈ S`.
The predicate makes sense over any semiring. Over a commutative ring, `P.saturation S`
is the inverse image of the existing `S`-torsion submodule of `M ⧸ P`.
Thus membership means `∃ r ∈ S, r • x ∈ P`, without a second construction of a
torsion submodule. No regularity assumption on the denominators is needed.

The specialization `S = R⁰` uses non-zero-divisors; over a domain these are exactly
the nonzero scalars. A submodule is saturated with respect to `R⁰` precisely when
its quotient is torsion-free.

## Proposed Mathlib home

`Mathlib/Algebra/Module/Submodule/Saturation.lean`. Dimension results belong in a
separate file, so the basic saturation API does not import dimension theory.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace Submodule

section Semiring

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  {P Q : Submodule R M} {S T : Submonoid R}

/-- A submodule is `S`-saturated if scalar multiplication by an element of `S`
can be cancelled from membership. -/
def IsSaturated (P : Submodule R M) (S : Submonoid R) : Prop :=
  ∀ ⦃r : R⦄, r ∈ S → ∀ ⦃x : M⦄, r • x ∈ P → x ∈ P

/-- Membership in a saturated submodule is unchanged by a denominator. -/
theorem IsSaturated.smul_mem_iff (hP : P.IsSaturated S) {r : R} (hr : r ∈ S) {x : M} :
    r • x ∈ P ↔ x ∈ P :=
  ⟨fun hx => hP hr hx, P.smul_mem r⟩

/-- Saturation with respect to more denominators implies saturation with respect to fewer. -/
theorem IsSaturated.of_le (hP : P.IsSaturated T) (hST : S ≤ T) : P.IsSaturated S :=
  fun _ hr _ hx => hP (hST hr) hx

/-- The whole module is saturated with respect to every submonoid. -/
@[simp] theorem isSaturated_top (S : Submonoid R) : (⊤ : Submodule R M).IsSaturated S :=
  fun _ _ _ _ => trivial

/-- Intersections of saturated submodules are saturated. -/
theorem IsSaturated.inf (hP : P.IsSaturated S) (hQ : Q.IsSaturated S) :
    (P ⊓ Q).IsSaturated S :=
  fun _ hr _ hx => ⟨hP hr hx.1, hQ hr hx.2⟩

/-- Arbitrary intersections of saturated submodules are saturated. -/
theorem IsSaturated.iInf {ι : Sort*} {P : ι → Submodule R M}
    (hP : ∀ i, (P i).IsSaturated S) : (⨅ i, P i).IsSaturated S := by
  intro r hr x hx
  simp only [mem_iInf] at hx ⊢
  exact fun i => hP i hr (hx i)

/-- Inverse images of saturated submodules under linear maps are saturated. -/
theorem IsSaturated.comap {Q : Submodule R N} (hQ : Q.IsSaturated S) (f : M →ₗ[R] N) :
    (Q.comap f).IsSaturated S := by
  intro r hr x hx
  exact hQ hr (by simpa only [mem_comap, map_smul] using hx)

end Semiring

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {S : Submonoid R}

/-- A vanishing finite relation in a saturated submodule determines the remaining vector
whenever its coefficient is an allowed denominator. -/
theorem IsSaturated.mem_of_sum_smul_eq_zero {P : Submodule R M} (hP : P.IsSaturated S)
    {ι : Type*} {s : Finset ι} {c : ι → R} {v : ι → M}
    (hsum : ∑ j ∈ s, c j • v j = 0) {i : ι} (hi : i ∈ s) (hci : c i ∈ S)
    (hrest : ∀ j ∈ s, j ≠ i → v j ∈ P) : v i ∈ P := by
  classical
  have hmem : ∑ j ∈ s.erase i, c j • v j ∈ P :=
    P.sum_mem fun j hj => P.smul_mem _
      (hrest j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1)
  have heq := Finset.sum_erase_add s (fun j => c j • v j) hi
  rw [hsum] at heq
  exact hP hci ((eq_neg_of_add_eq_zero_right heq) ▸ P.neg_mem hmem)

end Ring

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  (P Q : Submodule R M) (S T : Submonoid R)

/-- The saturation of `P` at `S`, obtained by pulling back the `S`-torsion of `M ⧸ P`. -/
def saturation : Submodule R M :=
  (torsion' R (M ⧸ P) S).comap P.mkQ

/-- An element is in the saturation exactly when a denominator sends it into `P`. -/
theorem mem_saturation_iff {x : M} :
    x ∈ P.saturation S ↔ ∃ r ∈ S, r • x ∈ P := by
  simp only [saturation, mem_comap, mem_torsion'_iff, Submonoid.smul_def,
    mkQ_apply, ← Quotient.mk_smul, Quotient.mk_eq_zero, Subtype.exists, exists_prop]

/-- Every submodule is contained in its saturation. -/
theorem le_saturation : P ≤ P.saturation S :=
  fun _ hx => (mem_saturation_iff P S).mpr ⟨1, S.one_mem, by simpa using hx⟩

/-- Saturation is monotone in the submodule. -/
theorem saturation_mono {P Q : Submodule R M} (hPQ : P ≤ Q) :
    P.saturation S ≤ Q.saturation S := by
  intro x hx
  obtain ⟨r, hr, hx⟩ := (mem_saturation_iff P S).mp hx
  exact (mem_saturation_iff Q S).mpr ⟨r, hr, hPQ hx⟩

/-- Enlarging the denominator submonoid enlarges the saturation. -/
theorem saturation_mono_right {S T : Submonoid R} (hST : S ≤ T) :
    P.saturation S ≤ P.saturation T := by
  intro x hx
  obtain ⟨r, hr, hx⟩ := (mem_saturation_iff P S).mp hx
  exact (mem_saturation_iff P T).mpr ⟨r, hST hr, hx⟩

/-- The saturation is saturated. -/
theorem isSaturated_saturation : (P.saturation S).IsSaturated S := by
  intro r hr x hx
  obtain ⟨s, hs, hx⟩ := (mem_saturation_iff P S).mp hx
  exact (mem_saturation_iff P S).mpr ⟨s * r, S.mul_mem hs hr, by simpa [mul_smul] using hx⟩

variable {S} in
/-- Saturation is the least saturated submodule containing the original submodule. -/
theorem IsSaturated.saturation_le {Q : Submodule R M} (hQ : Q.IsSaturated S)
    (hPQ : P ≤ Q) : P.saturation S ≤ Q := by
  intro x hx
  obtain ⟨r, hr, hx⟩ := (mem_saturation_iff P S).mp hx
  exact hQ hr (hPQ hx)

/-- A submodule is saturated precisely when saturation fixes it. -/
theorem isSaturated_iff_saturation_eq : P.IsSaturated S ↔ P.saturation S = P := by
  refine ⟨fun h => le_antisymm (h.saturation_le P le_rfl) (le_saturation P S), ?_⟩
  intro h
  rw [← h]
  exact isSaturated_saturation P S

/-- Saturating twice has the same effect as saturating once. -/
@[simp] theorem saturation_idem : (P.saturation S).saturation S = P.saturation S :=
  (isSaturated_iff_saturation_eq _ _).mp (isSaturated_saturation P S)

/-- Saturation as a closure operator, with saturated submodules as its closed elements. -/
def saturationClosureOperator : ClosureOperator (Submodule R M) where
  toFun P := P.saturation S
  monotone' _ _ h := saturation_mono S h
  le_closure' P := le_saturation P S
  idempotent' P := saturation_idem P S
  IsClosed P := P.IsSaturated S
  isClosed_iff := isSaturated_iff_saturation_eq _ _

/-- Saturation commutes with inverse images of linear maps. -/
@[simp] theorem saturation_comap (Q : Submodule R N) (f : M →ₗ[R] N) :
    (Q.comap f).saturation S = (Q.saturation S).comap f := by
  ext x
  simp only [mem_saturation_iff, mem_comap, map_smul]

/-- Saturation preserves binary intersections; multiply the two denominators. -/
@[simp] theorem saturation_inf : (P ⊓ Q).saturation S = P.saturation S ⊓ Q.saturation S := by
  apply le_antisymm
  · exact le_inf (saturation_mono S inf_le_left) (saturation_mono S inf_le_right)
  · intro x hx
    obtain ⟨r, hr, hPx⟩ := (mem_saturation_iff P S).mp hx.1
    obtain ⟨s, hs, hQx⟩ := (mem_saturation_iff Q S).mp hx.2
    refine (mem_saturation_iff _ S).mpr ⟨r * s, S.mul_mem hr hs, ?_, ?_⟩
    · simpa [mul_smul, smul_comm r s] using P.smul_mem s hPx
    · simpa [mul_smul] using Q.smul_mem r hQx

/-- The whole module is fixed by saturation. -/
@[simp] theorem saturation_top : (⊤ : Submodule R M).saturation S = ⊤ :=
  (isSaturated_iff_saturation_eq _ _).mp (isSaturated_top S)

/-- Saturating at the trivial submonoid does nothing. -/
@[simp] theorem saturation_bot : P.saturation ⊥ = P := by
  ext x
  simp [mem_saturation_iff]

/-- Saturation of the zero submodule is the existing `S`-torsion submodule. -/
@[simp] theorem bot_saturation : (⊥ : Submodule R M).saturation S = torsion' R M S := by
  ext x
  simp only [mem_saturation_iff, mem_bot, mem_torsion'_iff, Submonoid.smul_def,
    Subtype.exists, exists_prop]

/-- Allowing zero as a denominator makes every element belong to the saturation. -/
theorem saturation_eq_top_of_zero_mem (hS : (0 : R) ∈ S) : P.saturation S = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  exact (mem_saturation_iff P S).mpr ⟨0, hS, by simp⟩

/-- Saturation at non-zero-divisors is exactly torsion-freeness of the quotient. -/
theorem isSaturated_nonZeroDivisors_iff : P.IsSaturated R⁰ ↔ Module.IsTorsionFree R (M ⧸ P) := by
  constructor
  · intro hP
    constructor
    intro r hr
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro x hx
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    apply (Quotient.mk_eq_zero _).mpr
    exact hP hr.mem_nonZeroDivisors ((Quotient.mk_eq_zero _).mp hx)
  · intro hP r hr x hx
    have : r • P.mkQ x = 0 := by simpa using (Quotient.mk_eq_zero P).mpr hx
    have hr' := (isRegular_iff_mem_nonZeroDivisors.mpr hr).isSMulRegular (M := M ⧸ P)
    exact (Quotient.mk_eq_zero P).mp (hr' (this.trans (smul_zero r).symm))

/-- Over a domain, saturation at non-zero-divisors clears an arbitrary nonzero scalar. -/
theorem mem_saturation_nonZeroDivisors_iff [IsDomain R] {x : M} :
    x ∈ P.saturation R⁰ ↔ ∃ r : R, r ≠ 0 ∧ r • x ∈ P := by
  simp only [mem_saturation_iff, mem_nonZeroDivisors_iff_ne_zero]
end CommRing

end Submodule
