/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.RingHom.Finite

/-!
# Points and sections of finite étale covers over a ring

The canonical affine presentation and the native spectrum algebra-hom
equivalence identify points with algebra maps on sections over any base
ring. The comparison is natural and respects actual point automorphisms.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (H : Type u) [CommRing H]

/-- The existing section algebra has the literal affine structure map. -/
theorem sectionsScalarMap_eq (X : FiniteEtale (Spec (.of H))) :
    CommRingCat.ofHom (algebraMap H Γ(X.left, ⊤)) =
      (Scheme.ΓSpecIso (.of H)).inv ≫ X.hom.appTop := by
  change (Scheme.ΓSpecIso (.of H)).inv ≫ X.hom.appLE ⊤ ⊤ le_rfl =
    (Scheme.ΓSpecIso (.of H)).inv ≫ X.hom.appTop
  exact congrArg (fun k : Γ(Spec (.of H), ⊤) ⟶ Γ(X.left, ⊤) =>
    (Scheme.ΓSpecIso (.of H)).inv ≫ k) (Scheme.Hom.app_eq_appLE X.hom).symm

/-- Finiteness of the actual scheme morphism gives finite sections over the
original ring, with the existing section-algebra structure. -/
theorem sections_moduleFinite (X : FiniteEtale (Spec (.of H))) :
    Module.Finite H Γ(X.left, ⊤) := by
  have he : (Scheme.ΓSpecIso (.of H)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _
      (((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (.of H)).inv).mp
        inferInstance).surjective)
  let f : X.left ⟶ Spec (.of H) := X.hom
  have hf : (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of H)).inv.hom).Finite :=
    f.finite_appTop.comp he
  have hmap : algebraMap H Γ(X.left, ⊤) =
      X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of H)).inv.hom :=
    congrArg CommRingCat.Hom.hom (sectionsScalarMap_eq H X)
  exact RingHom.finite_algebraMap.mp (hmap.symm ▸ hf)

/-- The canonical affine presentation lies over the original base ring. -/
theorem isoSpec_over (X : FiniteEtale (Spec (.of H))) :
    X.left.isoSpec.hom ≫ Spec.algebraMap H Γ(X.left, ⊤) = X.hom := by
  let f : X.left ⟶ Spec (.of H) := X.hom
  change X.left.isoSpec.hom ≫ Spec.map
    (CommRingCat.ofHom (algebraMap H Γ(X.left, ⊤))) = f
  rw [sectionsScalarMap_eq, Spec.map_comp, ← Category.assoc]
  change (X.left.isoSpec.hom ≫ Spec.map f.appTop) ≫
    Spec.map (Scheme.ΓSpecIso (.of H)).inv = f
  rw [Scheme.isoSpec_hom_naturality f, Category.assoc, ← Scheme.isoSpec_Spec_inv,
    Iso.hom_inv_id, Category.comp_id]

/-- Restriction of sections along an actual finite étale-cover morphism. -/
def sectionsAlgHom {X Y : FiniteEtale (Spec (.of H))} (f : X ⟶ Y) :
    Γ(Y.left, ⊤) →ₐ[H] Γ(X.left, ⊤) where
  __ := f.left.appTop.hom
  commutes' h := by
    have : f.left.IsOver (Spec (.of H)) := ⟨MorphismProperty.Over.w f⟩
    have hLE := appLE_comp_algebraMap f.left H ⊤ ⊤ le_rfl
    have hTop : f.left.appTop.hom.comp (algebraMap H Γ(Y.left, ⊤)) =
        algebraMap H Γ(X.left, ⊤) :=
      (congrArg (fun k : Γ(Y.left, ⊤) ⟶ Γ(X.left, ⊤) =>
        k.hom.comp (algebraMap H Γ(Y.left, ⊤)))
          (Scheme.Hom.app_eq_appLE f.left)).trans hLE
    exact RingHom.congr_fun hTop h

variable (Ω : Type u) [CommRing Ω] [Algebra H Ω]

private def pointHomSpecEquiv (X : FiniteEtale (Spec (.of H))) :
    (Over.mk (Spec.algebraMap H Ω) ⟶ X.toComma) ≃
      {f : Spec (.of Ω) ⟶ Spec Γ(X.left, ⊤) //
        f ≫ Spec.algebraMap H Γ(X.left, ⊤) = Spec.algebraMap H Ω} where
  toFun x := ⟨x.left ≫ X.left.isoSpec.hom,
    (Category.assoc _ _ _).trans
      ((congrArg (fun k : X.left ⟶ Spec (.of H) => x.left ≫ k)
        (isoSpec_over H X)).trans x.w)⟩
  invFun x := Over.homMk (x.val ≫ X.left.isoSpec.inv) (by
    have hInv : X.left.isoSpec.inv ≫ X.hom = Spec.algebraMap H Γ(X.left, ⊤) :=
      (congrArg (fun k : X.left ⟶ Spec (.of H) => X.left.isoSpec.inv ≫ k)
        (isoSpec_over H X).symm).trans (Iso.inv_hom_id_assoc _ _)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k : Spec Γ(X.left, ⊤) ⟶ Spec (.of H) => x.val ≫ k) hInv).trans
        x.property))
  left_inv x := by
    apply Over.OverMorphism.ext
    change (x.left ≫ X.left.isoSpec.hom) ≫ X.left.isoSpec.inv = x.left
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv x := by
    apply Subtype.ext
    change (x.val ≫ X.left.isoSpec.inv) ≫ X.left.isoSpec.hom = x.val
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual over-point/section-algebra correspondence over a ring base. -/
def pointHomAlgEquiv (X : FiniteEtale (Spec (.of H))) :
    (Over.mk (Spec.algebraMap H Ω) ⟶ X.toComma) ≃ (Γ(X.left, ⊤) →ₐ[H] Ω) :=
  (pointHomSpecEquiv H Ω X).trans (Spec.homEquivAlgHom (R := H))

/-- The inverse spectrum computation retains the actual point morphism. -/
theorem pointHomAlgEquiv_specMap (X : FiniteEtale (Spec (.of H)))
    (x : Over.mk (Spec.algebraMap H Ω) ⟶ X.toComma) :
    Spec.map (CommRingCat.ofHom (pointHomAlgEquiv H Ω X x).toRingHom) =
      x.left ≫ X.left.isoSpec.hom :=
  congrArg Subtype.val
    ((Spec.homEquivAlgHom (R := H) (A := Γ(X.left, ⊤)) (B := Ω)).symm_apply_apply
      (pointHomSpecEquiv H Ω X x))

/-- The section correspondence commutes with actual cover morphisms. -/
theorem pointHomAlgEquiv_naturality {X Y : FiniteEtale (Spec (.of H))}
    (f : X ⟶ Y) (x : Over.mk (Spec.algebraMap H Ω) ⟶ X.toComma) :
    pointHomAlgEquiv H Ω Y (x ≫ f.hom) =
      (pointHomAlgEquiv H Ω X x).comp (sectionsAlgHom H f) := by
  apply AlgHom.coe_ringHom_injective
  have hRight :
      Spec.map (CommRingCat.ofHom
        ((pointHomAlgEquiv H Ω X x).comp (sectionsAlgHom H f)).toRingHom) =
        Spec.map (CommRingCat.ofHom (pointHomAlgEquiv H Ω X x).toRingHom) ≫
          Spec.map f.left.appTop :=
    Spec.map_comp f.left.appTop (CommRingCat.ofHom (pointHomAlgEquiv H Ω X x).toRingHom)
  refine congrArg (fun k : Γ(Y.left, ⊤) ⟶ CommRingCat.of Ω => k.hom) ?_
  apply Spec.map_injective
  calc
    Spec.map (CommRingCat.ofHom (pointHomAlgEquiv H Ω Y (x ≫ f.hom)).toRingHom) =
        (x.left ≫ f.left) ≫ Y.left.isoSpec.hom :=
      pointHomAlgEquiv_specMap H Ω Y (x ≫ f.hom)
    _ = x.left ≫ (f.left ≫ Y.left.isoSpec.hom) := Category.assoc _ _ _
    _ = x.left ≫ (X.left.isoSpec.hom ≫ Spec.map f.left.appTop) :=
      congrArg (fun k : X.left ⟶ Spec Γ(Y.left, ⊤) => x.left ≫ k)
        (Scheme.isoSpec_hom_naturality f.left).symm
    _ = (x.left ≫ X.left.isoSpec.hom) ≫ Spec.map f.left.appTop :=
      (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom (pointHomAlgEquiv H Ω X x).toRingHom) ≫
        Spec.map f.left.appTop :=
      congrArg (fun k : Spec (.of Ω) ⟶ Spec Γ(X.left, ⊤) => k ≫ Spec.map f.left.appTop)
        (pointHomAlgEquiv_specMap H Ω X x).symm
    _ = Spec.map (CommRingCat.ofHom
        ((pointHomAlgEquiv H Ω X x).comp (sectionsAlgHom H f)).toRingHom) := hRight.symm

/-- The actual action of a base-linear field automorphism on over-points. -/
def mapPointHom (σ : Ω ≃ₐ[H] Ω) (X : FiniteEtale (Spec (.of H)))
    (x : Over.mk (Spec.algebraMap H Ω) ⟶ X.toComma) :
    Over.mk (Spec.algebraMap H Ω) ⟶ X.toComma :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left) (by
    have hb : CommRingCat.ofHom (algebraMap H Ω) ≫ CommRingCat.ofHom σ.toRingHom =
        CommRingCat.ofHom (algebraMap H Ω) :=
      CommRingCat.hom_ext σ.toAlgHom.comp_algebraMap
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k : Spec (.of Ω) ⟶ Spec (.of H) =>
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ k) x.w).trans
          ((Spec.map_comp (CommRingCat.ofHom (algebraMap H Ω))
            (CommRingCat.ofHom σ.toRingHom)).symm.trans
              (congrArg (fun k : CommRingCat.of H ⟶ CommRingCat.of Ω => Spec.map k) hb))))

/-- The same point action is postcomposition on its section-algebra map. -/
theorem pointHomAlgEquiv_mapPointHom (σ : Ω ≃ₐ[H] Ω)
    (X : FiniteEtale (Spec (.of H))) (x : Over.mk (Spec.algebraMap H Ω) ⟶ X.toComma) :
    pointHomAlgEquiv H Ω X (mapPointHom H Ω σ X x) =
      σ.toAlgHom.comp (pointHomAlgEquiv H Ω X x) := by
  apply AlgHom.coe_ringHom_injective
  refine congrArg (fun k : Γ(X.left, ⊤) ⟶ CommRingCat.of Ω => k.hom) ?_
  apply Spec.map_injective
  calc
    Spec.map (CommRingCat.ofHom
        (pointHomAlgEquiv H Ω X (mapPointHom H Ω σ X x)).toRingHom) =
        (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left) ≫ X.left.isoSpec.hom :=
      pointHomAlgEquiv_specMap H Ω X (mapPointHom H Ω σ X x)
    _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (x.left ≫ X.left.isoSpec.hom) :=
      Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (pointHomAlgEquiv H Ω X x).toRingHom) :=
      congrArg (fun k : Spec (.of Ω) ⟶ Spec Γ(X.left, ⊤) =>
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ k)
        (pointHomAlgEquiv_specMap H Ω X x).symm
    _ = Spec.map (CommRingCat.ofHom
        (σ.toAlgHom.comp (pointHomAlgEquiv H Ω X x)).toRingHom) :=
      (Spec.map_comp (CommRingCat.ofHom (pointHomAlgEquiv H Ω X x).toRingHom)
        (CommRingCat.ofHom σ.toRingHom)).symm

end AlgebraicGeometry.FiniteEtale
