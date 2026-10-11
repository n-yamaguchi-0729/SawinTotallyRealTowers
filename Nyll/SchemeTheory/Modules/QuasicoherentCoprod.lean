/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.QuasicoherentLocal
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# Quasicoherence of actual binary coproducts

On each affine chart the tilde adjunction carries the coproduct of the
two section modules to the actual sheaf coproduct. Restriction preserves
this coproduct, so the affine criterion gives global quasicoherence.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

private def tildeSectionsIso {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (tilde.functor R).obj ((moduleSpecΓFunctor (R := R)).obj M) ≅ M := by
  let f : (tilde.functor R).obj ((moduleSpecΓFunctor (R := R)).obj M) ⟶ M :=
    fromTildeΓ (R := R) M
  have : IsIso (C := (Spec R).Modules) f :=
    isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  exact asIso (C := (Spec R).Modules) f

/-- Actual binary coproducts of quasicoherent modules are quasicoherent on an affine scheme. -/
theorem isQuasicoherent_coprod_toSpec {R : CommRingCat.{u}}
    (M N : (Spec R).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⨿ N).IsQuasicoherent := by
  let GM : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj M
  let GN : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj N
  have : PreservesColimitsOfSize.{u, u} (tilde.functor R) :=
    (tilde.adjunction (R := R)).leftAdjoint_preservesColimits
  let e : (tilde.functor R).obj (GM ⨿ GN) ≅ M ⨿ N :=
    (PreservesColimitPair.iso (tilde.functor R) GM GN).symm ≪≫
      coprod.mapIso (tildeSectionsIso M) (tildeSectionsIso N)
  have h : ((tilde.functor R).obj (GM ⨿ GN)).IsQuasicoherent :=
    inferInstanceAs (tilde (R := R) (GM ⨿ GN)).IsQuasicoherent
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((sheafOfModulesEquivalence (Spec R)).functor.mapIso e) h

/-- The actual binary coproduct of quasicoherent scheme modules is quasicoherent. -/
theorem isQuasicoherent_coprod {X : Scheme.{u}}
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⨿ N).IsQuasicoherent := by
  apply isQuasicoherent_of_affineSpecRestrictions (M ⨿ N)
  intro U hU
  let F : X.Modules ⥤ (Spec Γ(X, U)).Modules := restrictFunctor hU.fromSpec
  have : (F.obj M).IsQuasicoherent := isQuasicoherent_restrictFunctor hU.fromSpec M
  have : (F.obj N).IsQuasicoherent := isQuasicoherent_restrictFunctor hU.fromSpec N
  have : PreservesColimitsOfSize.{u, u} F :=
    (restrictAdjunction hU.fromSpec).leftAdjoint_preservesColimits
  have h : (F.obj M ⨿ F.obj N).IsQuasicoherent :=
    isQuasicoherent_coprod_toSpec (F.obj M) (F.obj N)
  let e := (sheafOfModulesEquivalence (Spec Γ(X, U))).functor.mapIso
    (PreservesColimitPair.iso F M N)
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso e h

end AlgebraicGeometry.Scheme.Modules

namespace SheafOfModules

/-- The actual native binary coproduct of quasicoherent sheaves on a scheme is quasicoherent. -/
theorem isQuasicoherent_coprod_native {X : AlgebraicGeometry.Scheme.{u}}
    (M N : SheafOfModules.{u} X.ringCatSheaf) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⨿ N).IsQuasicoherent := by
  let E : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf :=
    AlgebraicGeometry.Scheme.Modules.sheafOfModulesEquivalence X
  have : (E.inverse.obj M).IsQuasicoherent := inferInstanceAs M.IsQuasicoherent
  have : (E.inverse.obj N).IsQuasicoherent := inferInstanceAs N.IsQuasicoherent
  have h : (E.inverse.obj M ⨿ E.inverse.obj N).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_coprod
      (E.inverse.obj M) (E.inverse.obj N)
  let e : E.functor.obj (E.inverse.obj M ⨿ E.inverse.obj N) ≅ M ⨿ N :=
    (PreservesColimitPair.iso E.functor (E.inverse.obj M) (E.inverse.obj N)).symm
  exact (isQuasicoherent X.ringCatSheaf).prop_of_iso e h

end SheafOfModules
