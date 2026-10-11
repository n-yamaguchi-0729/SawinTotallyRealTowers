/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Module.LocalizedModule.Away


/-!
# Affine localization of quasicoherent sections

Relates the actual basic-open restriction maps to their elementwise localization clauses.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The two elementwise localization conditions for the actual restriction
to a basic open. The scalar actions are the existing section actions. -/
def BasicOpenLocalization {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (f : Γ(X, U)) : Prop :=
  (∀ x : Γ(M, X.basicOpen f), ∃ (n : ℕ) (y : Γ(M, U)),
    M.presheaf.map (homOfLE (X.basicOpen_le f)).op y =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x) ∧
  (∀ y : Γ(M, U), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
    ∃ n : ℕ, (f ^ n : Γ(X, U)) • y = 0)

/-- Restriction along an open immersion preserves the localization clauses
on its actual image, including the section and scalar restriction maps. -/
theorem basicOpenLocalization_restrict_iff {X Y : Scheme.{u}}
    (M : X.Modules) (j : Y ⟶ X) [IsOpenImmersion j]
    (V : Y.Opens) (f : Γ(Y, V)) :
    BasicOpenLocalization (M.restrict j) V f ↔
      BasicOpenLocalization M (j ''ᵁ V) ((j.appIso V).inv f) := by
  have hcoef (n : ℕ) :
      (j.appIso (Y.basicOpen f)).inv
          (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (f ^ n)) =
        X.presheaf.map (homOfLE (j.image_mono (Y.basicOpen_le f))).op
          (((j.appIso V).inv f) ^ n) := by
    have h := congrArg
      (fun k : Γ(Y, V) ⟶ Γ(X, j ''ᵁ Y.basicOpen f) => k (f ^ n))
      (j.appIso_inv_naturality (homOfLE (Y.basicOpen_le f)).op)
    change (j.appIso (Y.basicOpen f)).inv
        (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (f ^ n)) =
      X.presheaf.map (homOfLE (j.image_mono (Y.basicOpen_le f))).op
        ((j.appIso V).inv (f ^ n)) at h
    simpa only [map_pow] using h
  have hmap (y : Γ(M.restrict j, V)) :
      (M.restrictAppIso j (Y.basicOpen f)).hom
          ((M.restrict j).presheaf.map (homOfLE (Y.basicOpen_le f)).op y) =
        M.presheaf.map (homOfLE (j.image_mono (Y.basicOpen_le f))).op
          ((M.restrictAppIso j V).hom y) :=
    congrArg
      (fun k : Γ(M.restrict j, V) ⟶ Γ(M, j ''ᵁ Y.basicOpen f) => k y)
      (M.map_restrictAppIso_hom j (homOfLE (Y.basicOpen_le f)).op)
  have hsmul (W : Y.Opens) (a : Γ(Y, W)) (x : Γ(M.restrict j, W)) :
      (M.restrictAppIso j W).hom (a • x) =
        (j.appIso W).inv a • (M.restrictAppIso j W).hom x :=
    congrArg
      (fun k : Γ(M.restrict j, W) ⟶ Γ(M, j ''ᵁ W) => k x)
      (M.smul_restrictAppIso_hom j W a)
  have htransport (W : X.Opens) (hWV : W ≤ j ''ᵁ V)
      (heq : W = j ''ᵁ Y.basicOpen f) :
      BasicOpenLocalization (M.restrict j) V f ↔
        ((∀ x : Γ(M, W), ∃ (n : ℕ) (y : Γ(M, j ''ᵁ V)),
          M.presheaf.map (homOfLE hWV).op y =
            X.presheaf.map (homOfLE hWV).op (((j.appIso V).inv f) ^ n) • x) ∧
        (∀ y : Γ(M, j ''ᵁ V), M.presheaf.map (homOfLE hWV).op y = 0 →
          ∃ n : ℕ, (((j.appIso V).inv f) ^ n : Γ(X, j ''ᵁ V)) • y = 0)) := by
    subst W
    unfold BasicOpenLocalization
    constructor
    · intro h
      constructor
      · intro x
        obtain ⟨n, y, hy⟩ := h.1 ((M.restrictAppIso j (Y.basicOpen f)).inv x)
        refine ⟨n, (M.restrictAppIso j V).hom y, ?_⟩
        rw [← hmap, hy, hsmul, Iso.inv_hom_id_apply, hcoef]
      · intro y hy
        have hy' : (M.restrict j).presheaf.map (homOfLE (Y.basicOpen_le f)).op
            ((M.restrictAppIso j V).inv y) = 0 := by
          apply (ConcreteCategory.bijective_of_isIso
            (M.restrictAppIso j (Y.basicOpen f)).hom).injective
          rw [hmap, Iso.inv_hom_id_apply, hy, map_zero]
        obtain ⟨n, hn⟩ := h.2 ((M.restrictAppIso j V).inv y) hy'
        refine ⟨n, ?_⟩
        have hn' := congrArg (fun x : Γ(M.restrict j, V) =>
          (M.restrictAppIso j V).hom x) hn
        simpa only [hsmul, map_pow, Iso.inv_hom_id_apply, map_zero] using hn'
    · intro h
      constructor
      · intro x
        obtain ⟨n, y, hy⟩ := h.1 ((M.restrictAppIso j (Y.basicOpen f)).hom x)
        refine ⟨n, (M.restrictAppIso j V).inv y, ?_⟩
        apply (ConcreteCategory.bijective_of_isIso
          (M.restrictAppIso j (Y.basicOpen f)).hom).injective
        rw [hmap, Iso.inv_hom_id_apply, hsmul, hcoef]
        exact hy
      · intro y hy
        have hy' : M.presheaf.map (homOfLE (j.image_mono (Y.basicOpen_le f))).op
            ((M.restrictAppIso j V).hom y) = 0 := by
          rw [← hmap, hy, map_zero]
        obtain ⟨n, hn⟩ := h.2 ((M.restrictAppIso j V).hom y) hy'
        refine ⟨n, ?_⟩
        apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso j V).hom).injective
        rw [hsmul, map_pow, hn, map_zero]
  exact htransport (X.basicOpen ((j.appIso V).inv f))
    (X.basicOpen_le ((j.appIso V).inv f)) (Scheme.image_basicOpen j f).symm

private theorem spec_native_localization (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [M.IsQuasicoherent] (r : R) :
    IsLocalizedModule (Submonoid.powers r)
      (((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom) :=
  (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance r

private theorem spec_native_surjectivity (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [M.IsQuasicoherent] (r : R)
    (x : (modulesSpecToSheaf.obj M).obj.obj (op (PrimeSpectrum.basicOpen r))) :
    ∃ (n : ℕ) (y : (modulesSpecToSheaf.obj M).obj.obj (op ⊤)),
      ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom y =
        r ^ n • x := by
  let l := ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  have h : IsLocalizedModule (Submonoid.powers r) l := spec_native_localization R M r
  obtain ⟨n, y, hy⟩ := IsLocalizedModule.Away.surj (r := r) (f := l) x
  exact ⟨n, y, hy.symm⟩

private theorem spec_native_kernel (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [M.IsQuasicoherent] (r : R) (y : Γ(M, ⊤))
    (hy : M.presheaf.map (PrimeSpectrum.basicOpen r).leTop.op y = 0) :
    ∃ n : ℕ, r ^ n • y = 0 := by
  let l := ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  have h : IsLocalizedModule (Submonoid.powers r) l := spec_native_localization R M r
  have hy' : l y = l 0 := by
    rw [map_zero]
    exact hy
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (r := r) (f := l) hy'
  exact ⟨n, (hn.trans (smul_zero _))⟩

private theorem spec_basic_scalar (R : CommRingCat.{u}) (M : (Spec R).Modules)
    (U : (Spec R).Opens) (r : R) (n : ℕ) (x : Γ(M, U)) :
    r ^ n • x = (Spec R).presheaf.map U.leTop.op
      (((Scheme.ΓSpecIso R).inv r) ^ n) • x := by
  rw [Scheme.Modules.smul_Spec_def, map_pow]

private theorem spec_top_scalar (R : CommRingCat.{u}) (M : (Spec R).Modules)
    (r : R) (n : ℕ) (y : Γ(M, ⊤)) :
    r ^ n • y = ((Scheme.ΓSpecIso R).inv r) ^ n • y := by
  rw [Scheme.Modules.smul_Spec_def, map_pow]
  have hid : (Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op = 𝟙 _ := by
    rw [Subsingleton.elim (⊤ : (Spec R).Opens).leTop (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rw [hid]
  rfl

private theorem spec_transported_clauses (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [M.IsQuasicoherent] (r : R) :
    (∀ x : Γ(M, (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv r)),
      ∃ (n : ℕ) (y : Γ(M, ⊤)),
        M.presheaf.map ((Spec R).basicOpen ((Scheme.ΓSpecIso R).inv r)).leTop.op y =
          (Spec R).presheaf.map
            ((Spec R).basicOpen ((Scheme.ΓSpecIso R).inv r)).leTop.op
            (((Scheme.ΓSpecIso R).inv r) ^ n) • x) ∧
    (∀ y : Γ(M, ⊤),
      M.presheaf.map ((Spec R).basicOpen ((Scheme.ΓSpecIso R).inv r)).leTop.op y = 0 →
        ∃ n : ℕ, ((Scheme.ΓSpecIso R).inv r) ^ n • y = 0) := by
  rw [basicOpen_eq_of_affine r]
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := spec_native_surjectivity R M r x
    exact ⟨n, y, hy.trans (spec_basic_scalar R M (PrimeSpectrum.basicOpen r) r n x)⟩
  · intro y hy
    obtain ⟨n, hn⟩ := spec_native_kernel R M r y hy
    exact ⟨n, (spec_top_scalar R M r n y).symm.trans hn⟩

private theorem basicOpenLocalization_spec {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : Γ(Spec R, ⊤)) :
    BasicOpenLocalization M ⊤ f := by
  let r : R := (Scheme.ΓSpecIso R).hom f
  have hr : (Scheme.ΓSpecIso R).inv r = f := (Scheme.ΓSpecIso R).hom_inv_id_apply f
  rw [← hr]
  exact spec_transported_clauses R M r

/-- Quasicoherence supplies the actual affine localization input to the
compact-open section-gluing argument. -/
theorem basicOpenLocalization_of_isQuasicoherent {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens) (f : Γ(X, U.1)) :
    BasicOpenLocalization M U.1 f := by
  let j : Spec Γ(X, U.1) ⟶ X := U.2.fromSpec
  have : IsOpenImmersion j := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have htop : j ''ᵁ ⊤ = U.1 := j.image_top_eq_opensRange.trans U.2.opensRange_fromSpec
  have hImage (g : Γ(X, j ''ᵁ ⊤)) : BasicOpenLocalization M (j ''ᵁ ⊤) g := by
    have h := (basicOpenLocalization_restrict_iff M j ⊤ ((j.appIso ⊤).hom g)).mp
      (basicOpenLocalization_spec (M.restrict j) ((j.appIso ⊤).hom g))
    simpa only [Iso.hom_inv_id_apply] using h
  rw [htop] at hImage
  exact hImage f

end AlgebraicGeometry.Scheme.Modules
