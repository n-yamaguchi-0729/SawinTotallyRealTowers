/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Relative normalization of an affine morphism

The relative normalization of `Spec B → Spec R` is canonically isomorphic to
`Spec (integralClosure R B)`. The comparison intertwines the canonical map into
the normalization with the map induced by the inclusion of the integral
closure into `B`. Thus Zariski's main theorem makes this literal inclusion an
open immersion when `B` is a quasi-finite algebra of finite type over `R`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The affine scheme morphism induced by the structural algebra map. -/
abbrev affineStructureMap : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R B))

/-- The global-section identifications restrict to the corresponding integral
closures. -/
def specIntegralClosureIso :
    letI := (affineStructureMap R B).appTop.hom.toAlgebra
    CommRingCat.of (integralClosure Γ(Spec (CommRingCat.of R), ⊤)
      Γ(Spec (CommRingCat.of B), ⊤)) ≅ CommRingCat.of (integralClosure R B) := by
  letI := (affineStructureMap R B).appTop.hom.toAlgebra
  let e := (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv
  refine (e.restrict (integralClosure Γ(Spec (CommRingCat.of R), ⊤)
    Γ(Spec (CommRingCat.of B), ⊤)) (integralClosure R B) ?_).toCommRingCatIso
  intro x
  change _root_.IsIntegral Γ(Spec (CommRingCat.of R), ⊤) x ↔ _root_.IsIntegral R (e x)
  constructor
  · intro hx
    exact _root_.IsIntegral.map_of_comp_eq
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
      (congrArg (fun k : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of B ↦ k.hom)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R B))).symm) hx
  · intro hx
    have hx' := _root_.IsIntegral.map_of_comp_eq
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
      (congrArg (fun k : CommRingCat.of R ⟶ Γ(Spec (CommRingCat.of B), ⊤) ↦ k.hom)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R B))).symm) hx
    change _root_.IsIntegral Γ(Spec (CommRingCat.of R), ⊤) (e.symm (e x)) at hx'
    simpa only [RingEquiv.symm_apply_apply] using hx'

/-- The ring of global sections of the relative normalization of an affine
morphism is its literal integral closure. -/
def specNormalizationRingIso :
    Γ((affineStructureMap R B).normalization, ⊤) ≅
      CommRingCat.of (integralClosure R B) := by
  letI := (affineStructureMap R B).appTop.hom.toAlgebra
  exact (affineStructureMap R B).normalizationObjIso
    (isAffineOpen_top (Spec (CommRingCat.of R))) ≪≫ specIntegralClosureIso R B

@[reassoc]
lemma specNormalizationRingIso_hom_val :
    (specNormalizationRingIso R B).hom ≫
        CommRingCat.ofHom (integralClosure R B).val.toRingHom =
      (affineStructureMap R B).toNormalization.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom := by
  let := (affineStructureMap R B).appTop.hom.toAlgebra
  have hval : (specIntegralClosureIso R B).hom ≫
      CommRingCat.ofHom (integralClosure R B).val.toRingHom =
      CommRingCat.ofHom (integralClosure Γ(Spec (CommRingCat.of R), ⊤)
        Γ(Spec (CommRingCat.of B), ⊤)).val.toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom := by
    ext x
    rfl
  let m : Γ((affineStructureMap R B).normalization, ⊤) ⟶
      CommRingCat.of (integralClosure Γ(Spec (CommRingCat.of R), ⊤)
        Γ(Spec (CommRingCat.of B), ⊤)) :=
    ((affineStructureMap R B).normalizationObjIso
      (isAffineOpen_top (Spec (CommRingCat.of R)))).hom
  change (m ≫ (specIntegralClosureIso R B).hom) ≫ _ = _
  rw [Category.assoc, hval, ← Category.assoc]
  have hnorm :
      m ≫ CommRingCat.ofHom (integralClosure Γ(Spec (CommRingCat.of R), ⊤)
            Γ(Spec (CommRingCat.of B), ⊤)).val.toRingHom =
        (affineStructureMap R B).toNormalization.appTop := by
    have h := Scheme.Hom.normalizationObjIso_hom_val (affineStructureMap R B)
      (isAffineOpen_top (Spec (CommRingCat.of R)))
    have h' : m ≫ CommRingCat.ofHom
        (integralClosure Γ(Spec (CommRingCat.of R), ⊤)
          Γ(Spec (CommRingCat.of B), ⊤)).val.toRingHom =
        (affineStructureMap R B).toNormalization.appTop ≫
          (Spec (CommRingCat.of B)).presheaf.map (𝟙 (Opposite.op ⊤)) := h
    exact h'.trans ((congrArg (fun k : Γ(Spec (CommRingCat.of B), ⊤) ⟶
        Γ(Spec (CommRingCat.of B), ⊤) =>
          (affineStructureMap R B).toNormalization.appTop ≫ k)
      ((Spec (CommRingCat.of B)).presheaf.map_id (Opposite.op ⊤))).trans
        (Category.comp_id _))
  exact congrArg (fun k : Γ((affineStructureMap R B).normalization, ⊤) ⟶
    Γ(Spec (CommRingCat.of B), ⊤) => k ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom) hnorm

/-- The relative normalization of `Spec B → Spec R`, identified with the
spectrum of the integral closure of `R` in `B`. -/
def specNormalizationIso :
    (Spec.map (CommRingCat.ofHom (algebraMap R B))).normalization ≅
      Spec (CommRingCat.of (integralClosure R B)) := by
  letI : IsAffine (affineStructureMap R B).normalization :=
    isAffine_of_isAffineHom (affineStructureMap R B).fromNormalization
  exact (affineStructureMap R B).normalization.isoSpec ≪≫
    Scheme.Spec.mapIso (specNormalizationRingIso R B).symm.op

/-- The affine normalization comparison sends the canonical normalization map
to the map induced by the actual integral-closure inclusion. -/
@[reassoc]
lemma toNormalization_specNormalizationIso_hom :
    (Spec.map (CommRingCat.ofHom (algebraMap R B))).toNormalization ≫
        (specNormalizationIso R B).hom =
      Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom) := by
  let : IsAffine (affineStructureMap R B).normalization :=
    isAffine_of_isAffineHom (affineStructureMap R B).fromNormalization
  change (affineStructureMap R B).toNormalization ≫
    ((affineStructureMap R B).normalization.isoSpec.hom ≫
      Spec.map (specNormalizationRingIso R B).inv) = _
  rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality,
    Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    Category.assoc, ← specNormalizationRingIso_hom_val, Iso.inv_hom_id_assoc]

/-- Morphisms from an affine relative normalization to an affine scheme are
uniquely determined by their composites with the original affine scheme.
The integral-closure inclusion is injective on coordinate rings. -/
theorem spec_toNormalization_hom_ext
    {T : Scheme.{u}} [IsAffine T]
    {f g : (Spec.map (CommRingCat.ofHom (algebraMap R B))).normalization ⟶ T}
    (h : (Spec.map (CommRingCat.ofHom (algebraMap R B))).toNormalization ≫ f =
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).toNormalization ≫ g) :
    f = g := by
  have hval (x : Γ((affineStructureMap R B).normalization, ⊤)) :
      ((specNormalizationRingIso R B).hom x : B) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom
          ((affineStructureMap R B).toNormalization.appTop x) :=
    congrArg (fun k : Γ((affineStructureMap R B).normalization, ⊤) ⟶
      CommRingCat.of B ↦ k x) (specNormalizationRingIso_hom_val R B)
  have hinj : Function.Injective
      (affineStructureMap R B).toNormalization.appTop.hom := by
    intro x y hxy
    apply (specNormalizationRingIso R B).commRingCatIsoToRingEquiv.injective
    apply Subtype.val_injective
    change ((specNormalizationRingIso R B).hom x : B) =
      ((specNormalizationRingIso R B).hom y : B)
    rw [hval x, hval y, hxy]
  apply ext_of_isAffine
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply hinj
  have hΓ := congrArg (fun k ↦ k.appTop) h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hΓ
  exact congrArg (fun k : Γ(T, ⊤) ⟶ Γ(Spec (CommRingCat.of B), ⊤) ↦ k x) hΓ

/-- Zariski's main theorem for the literal integral-closure inclusion of a
quasi-finite algebra of finite type. -/
theorem isOpenImmersion_spec_integralClosure
    [Algebra.FiniteType R B] [Algebra.QuasiFinite R B] :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom)) := by
  let : LocallyOfFiniteType (affineStructureMap R B) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let : LocallyQuasiFinite (affineStructureMap R B) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mpr
      (RingHom.quasiFinite_algebraMap.mpr inferInstance)
  rw [← toNormalization_specNormalizationIso_hom R B]
  infer_instance

end AlgebraicGeometry
