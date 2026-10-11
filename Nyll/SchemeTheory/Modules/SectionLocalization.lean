/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.AbelianSectionLocalization
import Nyll.SchemeTheory.Modules.QuasicoherentAffineLocalization
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.QuasiSeparated
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Geometry.RingedSpace.Basic


/-!
# Localization of section modules

Uses abelian-presheaf gluing to prove localization for the actual module restrictions.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Multiplication by an actual global section, as a natural endomorphism
of the existing abelian presheaf. -/
def sectionEnd {X : Scheme.{u}} (M : X.Modules) (f : Γ(X, ⊤)) : End M.presheaf where
  app V := M.smul (X.presheaf.map V.unop.leTop.op f)
  naturality {V W} i := by
    symm
    have hsmul : M.smul (X.presheaf.map V.unop.leTop.op f) ≫ M.presheaf.map i =
        M.presheaf.map i ≫ M.smul
          (X.presheaf.map i (X.presheaf.map V.unop.leTop.op f)) := by
      simpa only [Quiver.Hom.op_unop] using
        M.map_comp_smul i.unop (X.presheaf.map V.unop.leTop.op f)
    rw [hsmul]
    have h : X.presheaf.map i (X.presheaf.map V.unop.leTop.op f) =
        X.presheaf.map W.unop.leTop.op f := by
      change (X.presheaf.map V.unop.leTop.op ≫ X.presheaf.map i) f = _
      rw [← Functor.map_comp]
      rfl
    rw [h]

lemma sectionEnd_pow_app {X : Scheme.{u}} (M : X.Modules) (f : Γ(X, ⊤))
    (n : ℕ) (V : X.Opens) :
    ((sectionEnd M f) ^ n).app (op V) =
      M.smul (X.presheaf.map V.leTop.op (f ^ n)) := by
  have h := (Functor.mapEnd M.presheaf
    ((evaluation X.Opensᵒᵖ Ab).obj (op V))).map_pow (sectionEnd M f) n
  change ((sectionEnd M f) ^ n).app (op V) =
    (M.smul (X.presheaf.map V.leTop.op f)) ^ n at h
  calc
    ((sectionEnd M f) ^ n).app (op V) =
        (M.smul (X.presheaf.map V.leTop.op f)) ^ n := h
    _ = M.smul ((X.presheaf.map V.leTop.op f) ^ n) :=
      (map_pow (M.smul (U := V)) _ n).symm
    _ = M.smul (X.presheaf.map V.leTop.op (f ^ n)) :=
      congrArg (M.smul (U := V)) (map_pow (X.presheaf.map V.leTop.op).hom f n).symm

lemma sectionEnd_pow_apply {X : Scheme.{u}} (M : X.Modules) (f : Γ(X, ⊤))
    (n : ℕ) (V : X.Opens) (x : Γ(M, V)) :
    ((sectionEnd M f) ^ n).app (op V) x =
      X.presheaf.map V.leTop.op (f ^ n) • x := by
  rw [sectionEnd_pow_app]
  rfl

private lemma sectionEnd_act {X : Scheme.{u}} (M : X.Modules)
    (f : Γ(X, ⊤)) (n : ℕ) (V : X.Opens) (x : Γ(M, V)) :
    AbelianSectionLocalization.act M.presheaf (sectionEnd M f) n V x =
      (X.presheaf.map V.leTop.op f) ^ n • x := by
  calc
    AbelianSectionLocalization.act M.presheaf (sectionEnd M f) n V x =
        X.presheaf.map V.leTop.op (f ^ n) • x := sectionEnd_pow_apply M f n V x
    _ = (X.presheaf.map V.leTop.op f) ^ n • x :=
      congrArg (fun r : Γ(X, V) => r • x) (map_pow (X.presheaf.map V.leTop.op).hom f n)

private lemma restriction_eq_zero_iff {X : Scheme.{u}} (M : X.Modules)
    {U V W : X.Opens} (hVU : V ≤ U) (hWU : W ≤ U) (hVW : V = W) (z : Γ(M, U)) :
    M.presheaf.map (homOfLE hVU).op z = 0 ↔
      M.presheaf.map (homOfLE hWU).op z = 0 := by
  subst W
  rfl

private lemma clauses_iff {X : Scheme.{u}} (M : X.Modules)
    (f : Γ(X, ⊤)) (V : X.Opens) :
    BasicOpenLocalization M V (X.presheaf.map V.leTop.op f) ↔
      AbelianSectionLocalization.Clauses M.presheaf (sectionEnd M f) (X.basicOpen f) V := by
  have hD : X.basicOpen (X.presheaf.map V.leTop.op f) = V ⊓ X.basicOpen f :=
    X.basicOpen_res f V.leTop.op
  have hcomp : X.presheaf.map (homOfLE (inf_le_left : V ⊓ X.basicOpen f ≤ V)).op
        (X.presheaf.map V.leTop.op f) =
      X.presheaf.map (V ⊓ X.basicOpen f).leTop.op f := by
    change (X.presheaf.map V.leTop.op ≫
      X.presheaf.map (homOfLE (inf_le_left : V ⊓ X.basicOpen f ≤ V)).op) f = _
    rw [← Functor.map_comp]
    rfl
  have htransport (W : X.Opens) (hWV : W ≤ V) (heq : W = V ⊓ X.basicOpen f) :
      ((∀ x : Γ(M, W), ∃ (n : ℕ) (y : Γ(M, V)),
        M.presheaf.map (homOfLE hWV).op y =
          X.presheaf.map (homOfLE hWV).op ((X.presheaf.map V.leTop.op f) ^ n) • x) ∧
        (∀ y : Γ(M, V), M.presheaf.map (homOfLE hWV).op y = 0 →
          ∃ n : ℕ, (X.presheaf.map V.leTop.op f) ^ n • y = 0)) ↔
        AbelianSectionLocalization.Clauses M.presheaf (sectionEnd M f) (X.basicOpen f) V := by
    subst W
    simp only [AbelianSectionLocalization.Clauses, AbelianSectionLocalization.res,
      sectionEnd_act, map_pow, hcomp]
  exact htransport (X.basicOpen (X.presheaf.map V.leTop.op f))
    (X.basicOpen_le (X.presheaf.map V.leTop.op f)) hD

private lemma top_restriction {X : Scheme.{u}} (f : Γ(X, ⊤)) :
    X.presheaf.map (⊤ : X.Opens).leTop.op f = f := by
  rw [Subsingleton.elim (⊤ : X.Opens).leTop (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma affine_clauses_restrict {X Y : Scheme.{u}} (M : X.Modules)
    (hlocal : ∀ V : X.affineOpens, ∀ f : Γ(X, V.1), BasicOpenLocalization M V.1 f)
    (j : Y ⟶ X) [IsOpenImmersion j] :
    ∀ V : Y.affineOpens, ∀ f : Γ(Y, V.1), BasicOpenLocalization (M.restrict j) V.1 f := by
  intro V f
  have hV : IsAffineOpen (j ''ᵁ V.1) := j.isAffineOpen_iff_of_isOpenImmersion.mpr V.2
  exact (basicOpenLocalization_restrict_iff M j V.1 f).mpr
    (hlocal ⟨j ''ᵁ V.1, hV⟩ ((j.appIso V.1).inv f))

private lemma clauses_top_of_affine {X : Scheme.{u}} (M : X.Modules)
    (hlocal : ∀ V : X.affineOpens, ∀ f : Γ(X, V.1), BasicOpenLocalization M V.1 f)
    [CompactSpace X] [QuasiSeparatedSpace X] (f : Γ(X, ⊤)) :
    BasicOpenLocalization M ⊤ f := by
  have h : ∀ V : X.affineOpens,
      AbelianSectionLocalization.Clauses M.presheaf (sectionEnd M f) (X.basicOpen f) V.1 := by
    intro V
    exact (clauses_iff M f V.1).mp (hlocal V (X.presheaf.map V.1.leTop.op f))
  have htop := AbelianSectionLocalization.clauses_of_qcqs M.presheaf M.isSheaf
    (sectionEnd M f) (X.basicOpen f) h (U := ⊤) isCompact_univ isQuasiSeparated_univ
  have h' := (clauses_iff M f ⊤).mpr htop
  simpa only [top_restriction] using h'

/-- The compact-open kernel bound from the shared gluing core. -/
theorem exists_pow_smul_eq_zero_of_affine_localization {X : Scheme.{u}}
    (M : X.Modules)
    (hlocal : ∀ V : X.affineOpens, ∀ f : Γ(X, V.1), BasicOpenLocalization M V.1 f)
    {U : X.Opens} (hU : IsCompact (U : Set X)) (f : Γ(X, U)) (y : Γ(M, U))
    (hy : M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0) :
    ∃ n : ℕ, (f ^ n : Γ(X, U)) • y = 0 := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let N := M.restrict U.ι
  have hN := affine_clauses_restrict M hlocal U.ι
  have hkernel (g : Γ(U.toScheme, ⊤)) :
      ∀ z : Γ(N, ⊤), N.presheaf.map (homOfLE (U.toScheme.basicOpen_le g)).op z = 0 →
        ∃ n : ℕ, (g ^ n : Γ(U.toScheme, ⊤)) • z = 0 := by
    have ha : ∀ V : U.toScheme.affineOpens,
        AbelianSectionLocalization.Clauses N.presheaf (sectionEnd N g)
          (U.toScheme.basicOpen g) V.1 := by
      intro V
      exact (clauses_iff N g V.1).mp (hN V (U.toScheme.presheaf.map V.1.leTop.op g))
    have hc := AbelianSectionLocalization.ker_of_isCompact N.presheaf N.isSheaf
      (sectionEnd N g) (U.toScheme.basicOpen g) ha (U := ⊤) isCompact_univ
    intro z hz
    have hD : (⊤ : U.toScheme.Opens) ⊓ U.toScheme.basicOpen g = U.toScheme.basicOpen g :=
      inf_eq_right.mpr le_top
    have hz' : AbelianSectionLocalization.res N.presheaf
        (inf_le_left : (⊤ : U.toScheme.Opens) ⊓ U.toScheme.basicOpen g ≤ ⊤) z = 0 := by
      exact (restriction_eq_zero_iff N (U.toScheme.basicOpen_le g) inf_le_left hD.symm z).mp hz
    obtain ⟨n, hn⟩ := hc z hz'
    refine ⟨n, ?_⟩
    have hn' := (sectionEnd_act N g n ⊤ z).symm.trans hn
    rw [top_restriction] at hn'
    exact hn'
  have hImage (g : Γ(X, U.ι ''ᵁ ⊤)) :
      ∀ z : Γ(M, U.ι ''ᵁ ⊤),
        M.presheaf.map (homOfLE (X.basicOpen_le g)).op z = 0 → ∃ n : ℕ, g ^ n • z = 0 := by
    let a : Γ(U.toScheme, ⊤) := (U.ι.appIso ⊤).hom g
    have he : (U.ι.appIso ⊤).inv a = g := (U.ι.appIso ⊤).hom_inv_id_apply g
    have hD : U.ι ''ᵁ U.toScheme.basicOpen a = X.basicOpen g := by
      rw [Scheme.image_basicOpen U.ι a, he]
    intro z hz
    have hz' : N.presheaf.map (homOfLE (U.toScheme.basicOpen_le a)).op z = 0 := by
      change M.presheaf.map (homOfLE (U.ι.image_mono (U.toScheme.basicOpen_le a))).op z = 0
      exact (restriction_eq_zero_iff M (X.basicOpen_le g)
        (U.ι.image_mono (U.toScheme.basicOpen_le a)) hD.symm z).mp hz
    obtain ⟨n, hn⟩ := hkernel a z hz'
    refine ⟨n, ?_⟩
    change (U.ι.appIso ⊤).inv (a ^ n) • z = 0 at hn
    rw [map_pow, he] at hn
    exact hn
  have htop : U.ι ''ᵁ ⊤ = U := U.ι.image_top_eq_opensRange.trans U.opensRange_ι
  rw [htop] at hImage
  exact hImage f y hy

/-- The existing compact-open argument generalized from local triviality
to the actual affine localization property. -/
theorem basicOpenLocalization_of_affine_localization {X : Scheme.{u}}
    (M : X.Modules)
    (hlocal : ∀ V : X.affineOpens, ∀ f : Γ(X, V.1), BasicOpenLocalization M V.1 f)
    {U : X.Opens} (hU : IsCompact (U : Set X))
    (hqs : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) :
    BasicOpenLocalization M U f := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U := (isQuasiSeparated_iff_quasiSeparatedSpace (U : Set X) U.2).mp hqs
  have hN := affine_clauses_restrict M hlocal U.ι
  have hImage (g : Γ(X, U.ι ''ᵁ ⊤)) : BasicOpenLocalization M (U.ι ''ᵁ ⊤) g := by
    have h := (basicOpenLocalization_restrict_iff M U.ι ⊤ ((U.ι.appIso ⊤).hom g)).mp
      (clauses_top_of_affine (M.restrict U.ι) hN ((U.ι.appIso ⊤).hom g))
    simpa only [Iso.hom_inv_id_apply] using h
  have htop : U.ι ''ᵁ ⊤ = U := U.ι.image_top_eq_opensRange.trans U.opensRange_ι
  rw [htop] at hImage
  exact hImage f

/-- Quasicoherent modules satisfy section localization on every
quasi-compact, quasi-separated open. All affine localization inputs are
supplied from quasicoherence in this same owner chain. -/
theorem basicOpenLocalization_of_isQuasicoherent_of_qcqs {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hqs : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) :
    BasicOpenLocalization M U f :=
  basicOpenLocalization_of_affine_localization M
    (basicOpenLocalization_of_isQuasicoherent M) hU hqs f

/-- On a quasi-compact, quasi-separated open, restriction of a quasicoherent
module to a basic open is the localization of its sections. The linear map
and its restriction-of-scalars codomain are the existing presheaf data. -/
theorem isLocalizedModule_basicOpen_of_isQuasicoherent_of_qcqs {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hqs : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) :
    IsLocalizedModule.Away f
      (show Γ(M, U) →ₗ[Γ(X, U)]
        (ModuleCat.restrictScalars (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom).obj
          (ModuleCat.of Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)) from
        (M.val.map (homOfLE (X.basicOpen_le f)).op).hom) := by
  have h := basicOpenLocalization_of_isQuasicoherent_of_qcqs M hU hqs f
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · rw [Module.End.isUnit_iff]
    change Function.Bijective (fun x :
      (ModuleCat.restrictScalars
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom).obj
          (ModuleCat.of Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)) => f • x)
    have hf : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f) :=
      RingedSpace.isUnit_res_basicOpen X.toRingedSpace f
    have hfun : (fun x :
        (ModuleCat.restrictScalars
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom).obj
            (ModuleCat.of Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)) => f • x) =
        (fun x : ModuleCat.of Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) =>
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f • x) := by
      funext x
      exact ModuleCat.restrictScalars.smul_def
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f x
    rw [hfun]
    exact hf.smul_bijective (β := ModuleCat.of Γ(X, X.basicOpen f) Γ(M, X.basicOpen f))
  · intro x
    obtain ⟨n, y, hy⟩ := h.1 x
    refine ⟨n, y, ?_⟩
    rw [ModuleCat.restrictScalars.smul_def]
    exact hy.symm
  · intro y hy
    exact h.2 y hy

end AlgebraicGeometry.Scheme.Modules
