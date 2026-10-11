/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.AffineFiniteSubmodule
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The actual localized range of the affine submodule morphism

Naturality and the tilde--Gamma unit identify the concrete section map
with localization of the original submodule inclusion. The existing
localization-of-ranges theorem then computes its actual range on every
principal open, without an assumed comparison map.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (F : (Spec R).Modules)

/-- The actual affine submodule morphism commutes with restriction of its
generators to every open. -/
theorem affineSubmoduleMap_toOpen
    (K : Submodule R ((moduleSpecΓFunctor (R := R)).obj F)) (U : (Spec R).Opens) :
    tilde.toOpen (ModuleCat.of R K) U ≫
        (modulesSpecToSheaf.map (affineSubmoduleMap F K)).hom.app (op U) =
      affineSubmoduleInclusion F K ≫ (modulesSpecToSheaf.obj F).obj.map U.leTop.op := by
  let A : ModuleCat.{u} R := ModuleCat.of R K
  let ψ := (modulesSpecToSheaf.map (affineSubmoduleMap F K)).hom
  have htop : tilde.toOpen A ⊤ ≫ ψ.app (op ⊤) = affineSubmoduleInclusion F K :=
    affineSubmoduleMap_globalSections F K
  calc
    tilde.toOpen A U ≫ ψ.app (op U) =
        (tilde.toOpen A ⊤ ≫ (modulesSpecToSheaf.obj (tilde A)).obj.map U.leTop.op) ≫
          ψ.app (op U) :=
      congrArg (fun g => g ≫ ψ.app (op U)) (tilde.toOpen_res A ⊤ U U.leTop).symm
    _ = tilde.toOpen A ⊤ ≫
        ((modulesSpecToSheaf.obj (tilde A)).obj.map U.leTop.op ≫ ψ.app (op U)) :=
      Category.assoc _ _ _
    _ = tilde.toOpen A ⊤ ≫ (ψ.app (op ⊤) ≫ (modulesSpecToSheaf.obj F).obj.map U.leTop.op) :=
      congrArg (fun g => tilde.toOpen A ⊤ ≫ g) (ψ.naturality U.leTop.op)
    _ = (tilde.toOpen A ⊤ ≫ ψ.app (op ⊤)) ≫ (modulesSpecToSheaf.obj F).obj.map U.leTop.op :=
      (Category.assoc _ _ _).symm
    _ = affineSubmoduleInclusion F K ≫ (modulesSpecToSheaf.obj F).obj.map U.leTop.op :=
      congrArg (fun g => g ≫ (modulesSpecToSheaf.obj F).obj.map U.leTop.op) htop

/-- The section map on a principal open has exactly the localization of
the original submodule as its range. -/
theorem affineSubmoduleMap_basicOpen_range [F.IsQuasicoherent]
    (K : Submodule R ((moduleSpecΓFunctor (R := R)).obj F)) (r : R) :
    let P : (Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R := (modulesSpecToSheaf.obj F).obj
    let U : (Spec R).Opens := PrimeSpectrum.basicOpen (R := R) r
    let b : ((moduleSpecΓFunctor (R := R)).obj F) →ₗ[R] P.obj (op U) :=
      (P.map U.leTop.op).hom
    let : IsLocalizedModule (Submonoid.powers r) b :=
      ((isIso_fromTildeΓ_iff_isLocalizing F).mp inferInstance) r
    ((modulesSpecToSheaf.map (affineSubmoduleMap F K)).hom.app (op U)).hom.range =
      K.localized₀ (Submonoid.powers r) b := by
  intro P U b hb
  let A : ModuleCat.{u} R := ModuleCat.of R K
  let A' : ModuleCat.{u} R := (modulesSpecToSheaf.obj (tilde A)).obj.obj (op U)
  let a : A →ₗ[R] A' := (tilde.toOpen A U).hom
  let c : A' →ₗ[R] P.obj (op U) :=
    ((modulesSpecToSheaf.map (affineSubmoduleMap F K)).hom.app (op U)).hom
  have : IsLocalizedModule (Submonoid.powers r) a := by
    let Q : (Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R := (modulesSpecToSheaf.obj (tilde A)).obj
    let a₀ : Q.obj (op ⊤) →ₗ[R] A' := (Q.map U.leTop.op).hom
    let e : A ≅ Q.obj (op ⊤) := tilde.isoTop A
    have ha₀ : IsLocalizedModule (Submonoid.powers r) a₀ := isLocalizing_tilde A r
    have he : a₀.comp e.hom.hom = a :=
      congrArg ModuleCat.Hom.hom (tilde.toOpen_res A ⊤ U U.leTop)
    have hComp : IsLocalizedModule (Submonoid.powers r) (a₀.comp e.hom.hom) :=
      (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers r)
        e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)).mpr ha₀
    exact Eq.mp (congrArg (fun l : A →ₗ[R] A' =>
      IsLocalizedModule (Submonoid.powers r) l) he) hComp
  let i : A →ₗ[R] (moduleSpecΓFunctor (R := R)).obj F :=
    (affineSubmoduleInclusion F K).hom
  have hc : c = IsLocalizedModule.map (Submonoid.powers r) a b i := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r) a b
    exact (congrArg ModuleCat.Hom.hom (affineSubmoduleMap_toOpen F K U)).trans
      (IsLocalizedModule.map_comp (Submonoid.powers r) a b i).symm
  change c.range = K.localized₀ (Submonoid.powers r) b
  exact (congrArg LinearMap.range hc).trans
    ((LinearMap.range_localizedMap_eq_localized₀_range
      (Submonoid.powers r) a b i).trans
        (congrArg (fun L => L.localized₀ (Submonoid.powers r) b) K.range_subtype))

end AlgebraicGeometry.Scheme.Modules
