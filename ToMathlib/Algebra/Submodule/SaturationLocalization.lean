/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Algebra.Submodule.Saturation
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Saturation and localization of submodules

Saturation is the inverse image of the localized submodule under the localization map.
This identifies the torsion-based construction with Mathlib's existing localization API,
without requiring injectivity of the localization map or regularity of the denominators.

## Proposed Mathlib home

Add these results to `Mathlib/Algebra/Module/LocalizedModule/Submodule.lean`, importing
`Mathlib/Algebra/Module/Submodule/Saturation.lean` there. Keeping the bridge separate here
avoids adding localization imports to the basic saturation API.
-/

public section

namespace Submodule

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (P : Submodule R M) (S : Submonoid R) (f : M →ₗ[R] N) [IsLocalizedModule S f]

/-- Saturation is the inverse image of the localized submodule. -/
theorem saturation_eq_comap_localized₀ : P.saturation S = (P.localized₀ S f).comap f := by
  ext x
  rw [mem_saturation_iff, mem_comap, mem_localized₀]
  constructor
  · rintro ⟨r, hr, hx⟩
    exact ⟨r • x, hx, ⟨r, hr⟩, IsLocalizedModule.mk'_eq_iff.mpr (f.map_smul r x)⟩
  · rintro ⟨m, hm, s, hs⟩
    rw [← IsLocalizedModule.mk'_one S f x, IsLocalizedModule.mk'_eq_mk'_iff] at hs
    obtain ⟨t, ht⟩ := hs
    refine ⟨(t * s : S), (t * s).property, ?_⟩
    have ht' : ((t * s : S) : R) • x = (t : R) • m := by
      simpa only [Submonoid.coe_mul, mul_smul, Submonoid.smul_def, one_smul] using ht
    rw [ht']
    exact P.smul_mem _ hm

/-- A submodule is saturated exactly when localization followed by inverse image fixes it. -/
theorem isSaturated_iff_comap_localized₀_eq :
    P.IsSaturated S ↔ (P.localized₀ S f).comap f = P := by
  rw [isSaturated_iff_saturation_eq, saturation_eq_comap_localized₀ P S f]

end Submodule
