/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteTypeAffineSections
import Nyll.SchemeTheory.Modules.FiniteTypeSchemeRestriction
import Nyll.SchemeTheory.Modules.AffineSectionLocalizationFinite
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Affine-section finiteness from finite type only on the given open

The finite-type hypothesis concerns the original module restricted to the
given open. The proved site-equivalence transport puts it on that actual
open subscheme. Its affine-section finiteness is transported back with the
existing section and coefficient isomorphisms, then supplied to canonical
localization. Global finite type of the ambient module is never required.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem finite_sections_of_finite_restriction
    {X Y : Scheme.{u}} (M : X.Modules) (j : Y ⟶ X) [IsOpenImmersion j]
    (V : Y.Opens) (hFinite : Module.Finite Γ(Y, V) Γ(M.restrict j, V)) :
    Module.Finite Γ(X, j ''ᵁ V) Γ(M, j ''ᵁ V) := by
  let σ : Γ(Y, V) →+* Γ(X, j ''ᵁ V) := (j.appIso V).inv.hom
  let e : Γ(M.restrict j, V) ≅ Γ(M, j ''ᵁ V) := M.restrictAppIso j V
  let l : Γ(M.restrict j, V) →ₛₗ[σ] Γ(M, j ''ᵁ V) :=
    { toAddHom := e.hom.hom.toAddHom
      map_smul' := fun r x =>
        congrArg (fun k : Γ(M.restrict j, V) ⟶ Γ(M, j ''ᵁ V) => k x)
          (M.smul_restrictAppIso_hom j V r) }
  have : Module.Finite Γ(Y, V) Γ(M.restrict j, V) := hFinite
  apply Module.Finite.of_surjective l
  intro y
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso e.hom).surjective y
  exact ⟨x, hx⟩

/-- Finite type of the actual module over an affine open suffices for its
native module of sections there to be finite. -/
theorem moduleFinite_sections_of_isFiniteType_over
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (hFinite : (M.over U).IsFiniteType) :
    Module.Finite Γ(X, U) Γ(M, U) := by
  have : IsAffine U.toScheme := hU
  have : (M.restrict U.ι).IsFiniteType := isFiniteType_restrict_of_over M U hFinite
  have hΓ : Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) :=
    moduleFinite_sections_of_isFiniteType (M.restrict U.ι) ⊤ (isAffineOpen_top U.toScheme)
  have hImage : U.ι ''ᵁ ⊤ = U := U.ι.image_top_eq_opensRange.trans U.opensRange_ι
  have h : Module.Finite Γ(X, U.ι ''ᵁ ⊤) Γ(M, U.ι ''ᵁ ⊤) :=
    finite_sections_of_finite_restriction M U.ι ⊤ hΓ
  exact Eq.mp (congrArg (fun W : X.Opens => Module.Finite Γ(X, W) Γ(M, W)) hImage) h

/-- Finite type only over the given principal open supplies the canonical
localized-top FG condition used in affine finite-submodule extraction. -/
theorem fg_localized_top_of_isFiniteType_over_basicOpen
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent] (r : R) :
    let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
    (M.over U).IsFiniteType →
      ((⊤ : Submodule R ((moduleSpecΓFunctor (R := R)).obj M)).localized
        (Submonoid.powers r)).FG := by
  intro U hFinite
  have hΓ : Module.Finite ((Spec R).ringCatSheaf.obj.obj (op U)) (M.val.obj (op U)) :=
    moduleFinite_sections_of_isFiniteType_over M U (IsAffineOpen.Spec_basicOpen r) hFinite
  exact fg_localized_top_of_finite_basicOpen M r hΓ

end AlgebraicGeometry.Scheme.Modules
