/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of the canonical localization from actual affine sections

The original quasicoherent restriction map identifies the canonical
localized module with the actual sections on a principal open. The
canonical localization ring is identified with its actual section ring.
These proved localization equivalences transport finite generation without
requiring global finite type of the original sheaf.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

private def actualSpecSectionModule {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (U : (Spec R).Opens) : ModuleCat.{u} R :=
  (modulesSpecToSheaf.obj M).obj.obj (op U)

private instance actualSpecSectionModule_sectionAction {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (U : (Spec R).Opens) :
    Module Γ(Spec R, U) (actualSpecSectionModule M U) :=
  (M.val.obj (op U)).isModule

private instance actualSpecSectionModule_tower {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (U : (Spec R).Opens) :
    IsScalarTower R Γ(Spec R, U) (actualSpecSectionModule M U) :=
  inferInstanceAs (IsScalarTower R Γ(Spec R, U) Γ(M, U))

private theorem finite_actualSpecSectionModule {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (h : Module.Finite ((Spec R).ringCatSheaf.obj.obj (op U)) (M.val.obj (op U))) :
    Module.Finite Γ(Spec R, U) (actualSpecSectionModule M U) := by
  let K : ModuleCat.{u} Γ(Spec R, U) := M.val.obj (op U)
  have : Module.Finite Γ(Spec R, U) K := h
  let e : K →ₗ[Γ(Spec R, U)] actualSpecSectionModule M U :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective e (fun x => ⟨x, rfl⟩)

/-- Finite native sections on a principal open imply finiteness of the
canonical localization of the original global-section module. -/
theorem moduleFinite_localizedModule_of_finite_basicOpen
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (r : R) :
    let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
    Module.Finite ((Spec R).ringCatSheaf.obj.obj (op U)) (M.val.obj (op U)) →
      Module.Finite (Localization.Away r)
        (LocalizedModule.Away r ((moduleSpecΓFunctor (R := R)).obj M)) := by
  intro U hFinite
  let S : Submonoid R := Submonoid.powers r
  let A : CommRingCat.{u} := Γ(Spec R, U)
  let B : ModuleCat.{u} R := actualSpecSectionModule M U
  let : Algebra R A := inferInstanceAs (Algebra R Γ(Spec R, U))
  let : Module A B := actualSpecSectionModule_sectionAction M U
  have : IsScalarTower R A B := actualSpecSectionModule_tower M U
  have : IsLocalization.Away r A :=
    inferInstanceAs (IsLocalization.Away r Γ(Spec R, PrimeSpectrum.basicOpen r))
  let C : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj M
  let L : Type u := Localization.Away r
  let a : L ≃ₐ[R] A := IsLocalization.algEquiv S L A
  let : Module L B := Module.compHom B a.toRingHom
  have : IsScalarTower R L B := IsScalarTower.of_algebraMap_smul fun c x => by
    change a (algebraMap R L c) • x = c • x
    rw [a.commutes]
    exact IsScalarTower.algebraMap_smul A c x
  let idSemilinear : B →ₛₗ[a.symm.toRingHom] B :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro c x
        change c • x = a (a.symm c) • x
        rw [a.apply_symm_apply] }
  have : Module.Finite A B := finite_actualSpecSectionModule M U hFinite
  have : Module.Finite L B :=
    Module.Finite.of_surjective idSemilinear (fun x => ⟨x, rfl⟩)
  let f : C →ₗ[R] B :=
    ((modulesSpecToSheaf.obj M).obj.map U.leTop.op).hom
  have hLocalizing : IsLocalizing (modulesSpecToSheaf.obj M) :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp
      (isIso_fromTildeΓ_of_isQuasicoherent (R := R) M)
  have : IsLocalizedModule S f := hLocalizing r
  let e : LocalizedModule S C ≃ₗ[R] B := IsLocalizedModule.iso S f
  let eL : LocalizedModule S C ≃ₗ[L] B := e.extendScalarsOfIsLocalization S L
  exact Module.Finite.equiv eL.symm

/-- The localized top submodule is finitely generated whenever the actual
sections on that principal open are finite. This is the input to affine
finite-submodule extraction on a compact open. -/
theorem fg_localized_top_of_finite_basicOpen
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (r : R) :
    let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
    Module.Finite ((Spec R).ringCatSheaf.obj.obj (op U)) (M.val.obj (op U)) →
      ((⊤ : Submodule R ((moduleSpecΓFunctor (R := R)).obj M)).localized
        (Submonoid.powers r)).FG := by
  intro U hFinite
  have : Module.Finite (Localization.Away r)
      (LocalizedModule.Away r ((moduleSpecΓFunctor (R := R)).obj M)) :=
    moduleFinite_localizedModule_of_finite_basicOpen M r hFinite
  rw [Submodule.localized, Submodule.localized'_top]
  exact Module.Finite.fg_top

end AlgebraicGeometry.Scheme.Modules
