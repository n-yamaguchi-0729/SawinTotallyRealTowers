/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Topology.Sheaves.Module
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Quasicoherence from actual affine restrictions

The affine tilde presentation is transported to the open subscheme and then
through the native equivalence with the slice site. These genuine local
presentations form quasicoherent data on the canonical affine open cover.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The identity action on modules and morphisms, with the scheme-module
and native sheaf-module category structures made explicit. -/
def sheafOfModulesEquivalence (X : Scheme.{u}) :
    X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf where
  functor :=
    { obj := fun M => M
      map := fun φ => φ
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  inverse :=
    { obj := fun M => M
      map := fun φ => φ
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  unitIso := NatIso.ofComponents (fun M => Iso.refl M) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun M => Iso.refl M) (by intros; rfl)
  functor_unitIso_comp := fun _ => by rfl

private def presentationOfQuasicoherentSpec
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent] :
    M.Presentation := by
  let G : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj M
  let A : SheafOfModules.{u} (Spec R).ringCatSheaf := tilde (R := R) G
  let B : SheafOfModules.{u} (Spec R).ringCatSheaf := M
  let P : A.Presentation :=
    presentationTilde (R := R) G Set.univ (Submodule.span_univ) _ (Submodule.span_eq _)
  let f : (tilde (R := R) G : (Spec R).Modules) ⟶ M :=
    Scheme.Modules.fromTildeΓ (R := R) M
  have hf : IsIso (C := (Spec R).Modules) f :=
    isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  let eScheme : (tilde (R := R) G : (Spec R).Modules) ≅ M :=
    asIso (C := (Spec R).Modules) f
  let e : A ≅ B := (sheafOfModulesEquivalence (Spec R)).functor.mapIso eScheme
  have : IsIso e.hom := inferInstance
  exact SheafOfModules.Presentation.ofIsIso
    (R := (Spec R).ringCatSheaf) (M := A) (N := B) e.hom P

private def presentationOverOfRestrict
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  let e : (overEquiv U).inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
      ((overEquiv U).unitIso.app (M.over U)).symm
  let F := (sheafOfModulesEquivalence U.toScheme).inverse ⋙ (overEquiv U).inverse
  have : PreservesColimitsOfSize.{u, u} (sheafOfModulesEquivalence U.toScheme).inverse :=
    (sheafOfModulesEquivalence U.toScheme).symm.toAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} (overEquiv U).inverse :=
    (overEquiv U).symm.toAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} F := comp_preservesColimits _ _
  let Q : ((overEquiv U).inverse.obj (M.restrict U.ι)).Presentation :=
    P.map F (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  exact Q.ofIsIso e.hom

private def presentationOfAffineSpecRestriction
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    (P : (M.restrict hU.fromSpec).Presentation) : (M.over U).Presentation := by
  let e : restrictFunctor hU.fromSpec ⋙ restrictFunctor hU.isoSpec.hom ≅
      restrictFunctor U.ι :=
    (restrictFunctorComp hU.isoSpec.hom hU.fromSpec).symm ≪≫
      restrictFunctorCongr hU.isoSpec_hom_fromSpec
  let A : SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    (M.restrict hU.fromSpec).restrict hU.isoSpec.hom
  let B : SheafOfModules.{u} U.toScheme.ringCatSheaf := M.restrict U.ι
  let eM : A ≅ B := (sheafOfModulesEquivalence U.toScheme).functor.mapIso (e.app M)
  have : IsIso eM.hom := inferInstance
  let P' : A.Presentation := presentationRestrict hU.isoSpec.hom P
  let Q : (M.restrict U.ι).Presentation :=
    SheafOfModules.Presentation.ofIsIso
      (R := U.toScheme.ringCatSheaf) (M := A) (N := B) eM.hom P'
  exact presentationOverOfRestrict M U Q

/-- Quasicoherence can be checked on the actual restrictions to the
canonical spectra of the rings of affine-open sections. -/
theorem isQuasicoherent_of_affineSpecRestrictions
    {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      (M.restrict hU.fromSpec).IsQuasicoherent) : M.IsQuasicoherent := by
  let q : M.QuasicoherentData :=
    { I := X.affineOpens
      X := fun U => U.1
      coversTop := by
        rw [Opens.coversTop_iff]
        exact iSup_affineOpens_eq_top X
      presentation := fun U => by
        have hU : IsAffineOpen U.1 := U.2
        have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
        have : (M.restrict hU.fromSpec).IsQuasicoherent := h U.1 hU
        exact presentationOfAffineSpecRestriction M U.1 hU
          (presentationOfQuasicoherentSpec (M.restrict hU.fromSpec)) }
  exact q.isQuasicoherent

end AlgebraicGeometry.Scheme.Modules
