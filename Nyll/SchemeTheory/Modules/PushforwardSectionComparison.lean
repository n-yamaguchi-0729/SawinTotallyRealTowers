/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.PushforwardCoefficients
import Nyll.SchemeTheory.Modules.NativeSectionObjects
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.NatIso
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Comparison of pushforward sections

Compares the existing section modules through the prescribed coefficient and restriction maps.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual target coefficient route at the already computed native section ring. -/
def targetSectionCoefficient {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (V : (Spec R).Opens) : R →+* j.sectionComparisonRing V :=
  j.pushforwardSectionCoefficient V

/-- The actual source coefficient route at the same native section ring. -/
def sourceSectionCoefficient {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (V : (Spec R).Opens) : R →+* j.sectionComparisonRing V :=
  (X.presheaf.map (j.sectionComparisonOpen V).leTop.op).hom.comp
    j.pushforwardGlobalCoefficient

/-- The existing coefficient naturality at these computed native values. -/
theorem sectionCoefficient_eq {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (V : (Spec R).Opens) :
    j.targetSectionCoefficient V = j.sourceSectionCoefficient V :=
  j.pushforwardSectionCoefficient_eq_restrict V

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual underlying base-module presheaf of the existing module pushforward. -/
def pushforwardModulePresheaf {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) : (Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  (modulesSpecToSheaf.obj ((pushforward j).obj M)).obj

/-- The existing source global-module presheaf with its prescribed base coefficients. -/
def sourceModulePresheaf {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) : X.Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  (show X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(X, ⊤) from
    PresheafOfModules.forgetToPresheafModuleCatObj (op (⊤ : X.Opens))
      (Limits.initialOpOfTerminal Limits.isTerminalTop) M.val) ⋙
        ModuleCat.restrictScalars j.pushforwardGlobalCoefficient

private def restrictedModule {R A : CommRingCat.{u}} (σ : R →+* A)
    (N : ModuleCat.{u} A) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars σ).obj N

private def coefficientCongr {R A : CommRingCat.{u}} (σ τ : R →+* A)
    (h : σ = τ) (N : ModuleCat.{u} A) :
    restrictedModule σ N ≅ restrictedModule τ N :=
  eqToIso (congrArg (fun ρ : R →+* A => restrictedModule ρ N) h)

private lemma coefficientCongr_hom_apply {R A : CommRingCat.{u}} (σ τ : R →+* A)
    (h : σ = τ) (N : ModuleCat.{u} A) (x : N) :
    (coefficientCongr σ τ h N).hom x = x := by
  subst τ
  rfl

private def targetSectionComponent {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) (V : (Spec R).Opens) :
    (pushforwardModulePresheaf j M).obj (op V) ≅
      restrictedModule (j.targetSectionCoefficient V) (j.sectionComparisonModule M V) :=
  Iso.refl (show ModuleCat.{u} R from
    restrictedModule (j.targetSectionCoefficient V) (j.sectionComparisonModule M V))

private def sourceSectionComponent {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) (V : (Spec R).Opens) :
    (sourceModulePresheaf j M).obj (op (j.sectionComparisonOpen V)) ≅
      restrictedModule (j.sourceSectionCoefficient V) (j.sectionComparisonModule M V) :=
  Iso.refl (show ModuleCat.{u} R from
    restrictedModule (j.sourceSectionCoefficient V) (j.sectionComparisonModule M V))

/-- Actual section comparison, using native values and the proved coefficient equality. -/
def pushforwardSectionIso {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) (V : (Spec R).Opens) :
    (pushforwardModulePresheaf j M).obj (op V) ≅
      (sourceModulePresheaf j M).obj (op (j.sectionComparisonOpen V)) :=
  targetSectionComponent j M V ≪≫
    coefficientCongr (j.targetSectionCoefficient V) (j.sourceSectionCoefficient V)
      (j.sectionCoefficient_eq V) (j.sectionComparisonModule M V) ≪≫
    (sourceSectionComponent j M V).symm

/-- The actual source module presheaf precomposed with the native preimage functor. -/
def sourceModuleOnTarget {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) : (Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  (Opens.map j.base).op ⋙ sourceModulePresheaf j M

private def sectionIsoOnTarget {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) (V : (Spec R).Opens) :
    (pushforwardModulePresheaf j M).obj (op V) ≅ (sourceModuleOnTarget j M).obj (op V) :=
  pushforwardSectionIso j M V

private lemma coefficientCongr_hom_toAddMonoidHom {R A : CommRingCat.{u}}
    (σ τ : R →+* A) (h : σ = τ) (N : ModuleCat.{u} A) :
    (coefficientCongr σ τ h N).hom.hom.toAddMonoidHom = AddMonoidHom.id N := by
  subst τ
  rfl

private def componentAddHom {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) (V : (Spec R).Opens) :
    j.sectionComparisonGroup M V →+ j.sectionComparisonGroup M V :=
  (sectionIsoOnTarget j M V).hom.hom.toAddMonoidHom

private lemma componentAddHom_eq_id {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) (V : (Spec R).Opens) :
    componentAddHom j M V = AddMonoidHom.id (j.sectionComparisonGroup M V) :=
  coefficientCongr_hom_toAddMonoidHom (j.targetSectionCoefficient V)
    (j.sourceSectionCoefficient V) (j.sectionCoefficient_eq V) (j.sectionComparisonModule M V)

private def targetRestrictionAddHom {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) {U V : (Spec R).Opens} (i : U ⟶ V) :
    j.sectionComparisonGroup M V →+ j.sectionComparisonGroup M U :=
  ((pushforwardModulePresheaf j M).map i.op).hom.toAddMonoidHom

private def sourceRestrictionAddHom {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) {U V : (Spec R).Opens} (i : U ⟶ V) :
    j.sectionComparisonGroup M V →+ j.sectionComparisonGroup M U :=
  ((sourceModuleOnTarget j M).map i.op).hom.toAddMonoidHom

private lemma restrictionAddHom_eq {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) {U V : (Spec R).Opens} (i : U ⟶ V) :
    targetRestrictionAddHom j M i = sourceRestrictionAddHom j M i := rfl

private lemma additive_naturality {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) {U V : (Spec R).Opens} (i : U ⟶ V) :
    (componentAddHom j M U).comp (targetRestrictionAddHom j M i) =
      (sourceRestrictionAddHom j M i).comp (componentAddHom j M V) := by
  rw [componentAddHom_eq_id, AddMonoidHom.id_comp,
    componentAddHom_eq_id, AddMonoidHom.comp_id]
  exact restrictionAddHom_eq j M i

private lemma sectionIsoOnTarget_naturality {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) {U V : (Spec R).Opens} (i : U ⟶ V) :
    (pushforwardModulePresheaf j M).map i.op ≫ (sectionIsoOnTarget j M U).hom =
      (sectionIsoOnTarget j M V).hom ≫ (sourceModuleOnTarget j M).map i.op := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  exact additive_naturality j M i

/-- The actual underlying module presheaves agree naturally over the target-open site. -/
def pushforwardModulePresheafIso {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) :
    pushforwardModulePresheaf j M ≅ sourceModuleOnTarget j M :=
  NatIso.ofComponents (fun V => sectionIsoOnTarget j M V.unop)
    (fun {_U _V} i => sectionIsoOnTarget_naturality j M i.unop)

end AlgebraicGeometry.Scheme.Modules
