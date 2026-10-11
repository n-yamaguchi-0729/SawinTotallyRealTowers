/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.SubmoduleAdjoinLocalization
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Generated algebras under an actual localized submodule restriction

The lower submodule is given by the actual restriction map, as with
sections of a quasicoherent subsheaf. Its identification with the native
localized submodule follows from denominators of its own sections. The
previous generated-algebra localization theorem then applies to the
literal algebra restriction. No submodule-comparison premise is added.
-/

noncomputable section

universe u v w z

namespace Submodule

variable {R : Type u} [CommRing R]
variable (R' : Type v) [CommRing R'] [Algebra R R']
variable {B : Type w} [CommRing B] [Algebra R B]
variable {B' : Type z} [CommRing B'] [Algebra R B'] [Algebra R' B']
variable [IsScalarTower R R' B']
variable (S : Submonoid R) [IsLocalization S R']
variable (f : B →ₐ[R] B') [IsLocalizedModule S f.toLinearMap]
variable (N : Submodule R B) (N' : Submodule R' B')

/-- If the actual restriction between the two submodules is a localization,
the target is precisely the native localized submodule of the ambient ring. -/
theorem localized'_eq_of_isLocalizedModule_restrict (hf : ∀ x ∈ N, f x ∈ N')
    [IsLocalizedModule S
      (f.toLinearMap.restrict (p := N) (q := N'.restrictScalars R) hf)] :
    N.localized' R' S f.toLinearMap = N' := by
  rw [localized'_eq_span]
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact hf x hx
  · intro x hx
    let g : N →ₗ[R] N'.restrictScalars R :=
      f.toLinearMap.restrict (p := N) (q := N'.restrictScalars R) hf
    obtain ⟨⟨y, s⟩, hy⟩ := IsLocalizedModule.surj S g ⟨x, hx⟩
    have hy' : (s : R) • x = f y.val := congrArg Subtype.val hy
    have hmem : f y.val ∈ span R' (f.toLinearMap '' (N : Set B)) :=
      subset_span ⟨y.val, y.property, rfl⟩
    apply (Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units R' s)).mp
    rw [algebraMap_smul, hy']
    exact hmem

private theorem adjoinRestrictionTo_mapsTo (hf : ∀ x ∈ N, f x ∈ N') :
    ∀ x ∈ Algebra.adjoin R (N : Set B), f x ∈ Algebra.adjoin R' (N' : Set B') := by
  change Algebra.adjoin R (N : Set B) ≤
    ((Algebra.adjoin R' (N' : Set B')).restrictScalars R).comap f
  apply Algebra.adjoin_le
  intro x hx
  exact Algebra.subset_adjoin (hf x hx)

/-- The literal ambient algebra restriction on the generated algebras. -/
def adjoinRestrictionTo (hf : ∀ x ∈ N, f x ∈ N') :
    Algebra.adjoin R (N : Set B) →ₐ[R] Algebra.adjoin R' (N' : Set B') :=
  (f.comp (Algebra.adjoin R (N : Set B)).val).codRestrict
    ((Algebra.adjoin R' (N' : Set B')).restrictScalars R)
    (fun x => adjoinRestrictionTo_mapsTo R' f N N' hf x.val x.property)

/-- The actual restriction on generated algebras localizes their modules
when the ambient restriction and the original submodule restriction do. -/
theorem isLocalizedModule_adjoinRestrictionTo (hf : ∀ x ∈ N, f x ∈ N')
    [IsLocalizedModule S
      (f.toLinearMap.restrict (p := N) (q := N'.restrictScalars R) hf)] :
    IsLocalizedModule S (adjoinRestrictionTo R' f N N' hf).toLinearMap := by
  have h : N.localized' R' S f.toLinearMap = N' :=
    localized'_eq_of_isLocalizedModule_restrict R' S f N N' hf
  subst N'
  exact isLocalizedModule_adjoinRestriction R' S f N

/-- Over a principal localization, the actual generated-algebra ring map
is a principal localization at the same structure coefficient. -/
theorem isLocalizationAway_adjoinRestrictionTo (hf : ∀ x ∈ N, f x ∈ N') (r : R)
    [IsLocalization.Away r R'] [IsLocalizedModule.Away r f.toLinearMap]
    [IsLocalizedModule.Away r
      (f.toLinearMap.restrict (p := N) (q := N'.restrictScalars R) hf)] :
    let g := adjoinRestrictionTo R' f N N' hf
    let : Algebra (Algebra.adjoin R (N : Set B)) (Algebra.adjoin R' (N' : Set B')) :=
      g.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (Algebra.adjoin R (N : Set B)) r)
      (Algebra.adjoin R' (N' : Set B')) := by
  intro g algebra
  have hloc : IsLocalizedModule.Away r g.toLinearMap :=
    isLocalizedModule_adjoinRestrictionTo R' (Submonoid.powers r) f N N' hf
  have htower : IsScalarTower R (Algebra.adjoin R (N : Set B))
      (Algebra.adjoin R' (N' : Set B')) := IsScalarTower.of_algHom g
  have h : IsLocalization
      (Algebra.algebraMapSubmonoid (Algebra.adjoin R (N : Set B)) (Submonoid.powers r))
      (Algebra.adjoin R' (N' : Set B')) :=
    isLocalizedModule_iff_isLocalization.mp hloc
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using h

end Submodule
