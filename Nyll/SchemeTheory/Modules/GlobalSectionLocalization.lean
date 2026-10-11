/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.SectionLocalization
import Nyll.SchemeTheory.Modules.LocalizationRestrictionOfScalars
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.QuasiSeparated

/-!
# Localization from global sections

Transports the section-localization results through the existing global coefficient modules.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The existing native global-section module presheaf, evaluated once at its ringed-site owner. -/
def globalModulePresheaf {X : Scheme.{u}} (M : X.Modules) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  PresheafOfModules.forgetToPresheafModuleCatObj (op (⊤ : X.Opens))
    (Limits.initialOpOfTerminal Limits.isTerminalTop) M.val

private lemma topMap_id {X : Scheme.{u}} :
    (X.presheaf.map (⊤ : X.Opens).leTop.op).hom = RingHom.id Γ(X, ⊤) := by
  have h : X.presheaf.map (⊤ : X.Opens).leTop.op = 𝟙 Γ(X, ⊤) := by
    rw [Subsingleton.elim (⊤ : X.Opens).leTop (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  exact congrArg CommRingCat.Hom.hom h

private def nativeTopIso {X : Scheme.{u}} (M : X.Modules) :
    (globalModulePresheaf M).obj (op ⊤) ≅ ModuleCat.of Γ(X, ⊤) Γ(M, ⊤) :=
  ModuleCat.restrictScalarsId'App (X.presheaf.map (⊤ : X.Opens).leTop.op).hom
    topMap_id (ModuleCat.of Γ(X, ⊤) Γ(M, ⊤))

private abbrev nativeRestriction {X : Scheme.{u}} (M : X.Modules) (W : X.Opens) :
    ModuleCat.of Γ(X, ⊤) Γ(M, ⊤) ⟶ (globalModulePresheaf M).obj (op W) :=
  ModuleCat.ofHom (X := ModuleCat.of Γ(X, ⊤) Γ(M, ⊤))
    (Y := (globalModulePresheaf M).obj (op W))
    (show Γ(M, ⊤) →ₗ[Γ(X, ⊤)] (globalModulePresheaf M).obj (op W) from
      (M.val.map W.leTop.op).hom)

private theorem restriction_comparison {X : Scheme.{u}} (M : X.Modules) (W : X.Opens) :
    (globalModulePresheaf M).map W.leTop.op = (nativeTopIso M).hom ≫ nativeRestriction M W := by
  apply ModuleCat.hom_ext
  ext x
  rfl

private lemma nativeRestriction_isLocalized {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] [CompactSpace X] [QuasiSeparatedSpace X] (g : Γ(X, ⊤)) :
    IsLocalizedModule (Submonoid.powers g) (nativeRestriction M (X.basicOpen g)).hom :=
  isLocalizedModule_basicOpen_of_isQuasicoherent_of_qcqs M isCompact_univ
    isQuasiSeparated_univ g

/-- The native global-section module presheaf sends a basic-open restriction
of a quasicoherent module on a qcqs scheme to actual localization. -/
theorem isLocalizedModule_forgetToModuleCat_of_qcqs {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] [CompactSpace X] [QuasiSeparatedSpace X] (g : Γ(X, ⊤)) :
    IsLocalizedModule (Submonoid.powers g)
      ((globalModulePresheaf M).map (X.basicOpen g).leTop.op).hom := by
  have : IsLocalizedModule (Submonoid.powers g) (nativeRestriction M (X.basicOpen g)).hom :=
    nativeRestriction_isLocalized M g
  rw [restriction_comparison]
  exact IsLocalizedModule.of_linearEquiv_right (S := Submonoid.powers g)
    (f := (nativeRestriction M (X.basicOpen g)).hom) (nativeTopIso M).toLinearEquiv

/-- The same genuine localization persists under the native restriction of
coefficients along a prescribed ring homomorphism. -/
theorem isLocalizedModule_restrictGlobalScalars_of_qcqs {R : CommRingCat.{u}}
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    [CompactSpace X] [QuasiSeparatedSpace X] (σ : R →+* Γ(X, ⊤)) (r : R) :
    IsLocalizedModule (Submonoid.powers r)
      ((globalModulePresheaf M ⋙
            ModuleCat.restrictScalars σ).map (X.basicOpen (σ r)).leTop.op).hom := by
  have : IsLocalizedModule (Submonoid.powers (σ r))
      ((globalModulePresheaf M).map (X.basicOpen (σ r)).leTop.op).hom :=
    isLocalizedModule_forgetToModuleCat_of_qcqs M (σ r)
  exact ModuleCat.isLocalizedModuleAway_restrictScalars R Γ(X, ⊤) σ
    ((globalModulePresheaf M).obj (op ⊤)) ((globalModulePresheaf M).obj (op (X.basicOpen (σ r))))
    ((globalModulePresheaf M).map (X.basicOpen (σ r)).leTop.op) r

end AlgebraicGeometry.Scheme.Modules
