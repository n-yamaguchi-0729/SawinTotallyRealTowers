/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.EtalePostcomposition
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Geometric integrality of function fields

This file proves that passing from a geometrically integral domain over a field
to its fraction field preserves geometric integrality.  It then applies this
ring-theoretic fact to the function field of an integral scheme.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open Opposite TopologicalSpace

namespace Algebra

namespace TensorProduct

/-- Base change of a domain along a fraction field remains a domain whenever
the base change of the original domain is a domain. -/
theorem isDomain_of_isFractionRing_left
    {k R K L : Type u}
    [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
    [IsFractionRing R K] [Field L] [Algebra k L]
    [IsDomain (TensorProduct k R L)] :
    IsDomain (TensorProduct k K L) := by
  let map : TensorProduct k R L →ₐ[k] TensorProduct k K L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R K) (AlgHom.id k L)
  let sourceTargetAlgebra :
      Algebra (TensorProduct k R L) (TensorProduct k K L) :=
    map.toRingHom.toAlgebra
  let targetAlgebraR : Algebra R (TensorProduct k K L) := inferInstance
  let : Algebra (TensorProduct k R L) (TensorProduct k K L) :=
    sourceTargetAlgebra
  let : IsScalarTower R (TensorProduct k R L) (TensorProduct k K L) :=
    @IsScalarTower.of_algebraMap_eq R (TensorProduct k R L)
      (TensorProduct k K L) _ _ _
      (inferInstance : Algebra R (TensorProduct k R L))
      sourceTargetAlgebra targetAlgebraR fun x => by
        change (@algebraMap R (TensorProduct k K L) _ _ targetAlgebraR) x =
          map (x ⊗ₜ[k] (1 : L))
        simp [map, targetAlgebraR]
  have hMap :
      (algebraMap (TensorProduct k R L) (TensorProduct k K L)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    change map ((1 : R) ⊗ₜ[k] x) = (1 : K) ⊗ₜ[k] x
    simp [map]
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (TensorProduct k R L) (nonZeroDivisors R))
      (TensorProduct k K L) :=
    IsLocalization.tensorProduct_tensorProduct k L (nonZeroDivisors R) K hMap
  have hSub :
      Algebra.algebraMapSubmonoid (TensorProduct k R L) (nonZeroDivisors R) ≤
        nonZeroDivisors (TensorProduct k R L) := by
    intro x hx
    change x ∈ (nonZeroDivisors R).map
      (algebraMap R (TensorProduct k R L)) at hx
    rcases hx with ⟨r, hr, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hx
    apply nonZeroDivisors.ne_zero hr
    apply FaithfulSMul.algebraMap_injective R (TensorProduct k R L)
    simpa using hx
  exact IsLocalization.isDomain_of_le_nonZeroDivisors
    (R := TensorProduct k R L)
    (M := Algebra.algebraMapSubmonoid
      (TensorProduct k R L) (nonZeroDivisors R))
    (TensorProduct k K L) hSub

end TensorProduct

end Algebra

namespace AlgebraicGeometry

/-- A surjective open subscheme of a geometrically integral scheme is
geometrically integral over the same base. -/
theorem GeometricallyIntegral.comp_of_isOpenImmersion
    {U X S : Scheme.{u}} (i : U ⟶ X) (f : X ⟶ S)
    [IsOpenImmersion i] [GeometricallyIntegral f] [Surjective (i ≫ f)] :
    GeometricallyIntegral (i ≫ f) := by
  let : GeometricallyReduced (i ≫ f) :=
    GeometricallyReduced.comp_of_isOpenImmersion i f
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

/-- If `K` is a fraction field of a geometrically integral `k`-domain `R`, then
`Spec K` is geometrically integral over `k`. -/
theorem GeometricallyIntegral.spec_of_isFractionRing
    {k R K : Type u}
    [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
    [IsFractionRing R K]
    [GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))] :
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing]
  intro L _ _ Y fst snd h
  have hDomainR : IsDomain (TensorProduct k R L) := by
    let f := Spec.map (CommRingCat.ofHom (algebraMap k R))
    let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let : IsIntegral (pullback f g) :=
      GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
    let : IsIntegral (Spec (.of (TensorProduct k R L))) :=
      IsIntegral.of_isIso (pullbackSpecIso k R L).hom
    exact (affine_isIntegral_iff (.of (TensorProduct k R L))).mp inferInstance
  let : IsDomain (TensorProduct k R L) := hDomainR
  have hDomainK : IsDomain (TensorProduct k K L) :=
    Algebra.TensorProduct.isDomain_of_isFractionRing_left
      (k := k) (R := R) (K := K) (L := L)
  have hIntegralK : IsIntegral (Spec (.of (TensorProduct k K L))) :=
    (affine_isIntegral_iff (.of (TensorProduct k K L))).mpr hDomainK
  let : IsIntegral (Spec (.of (TensorProduct k K L))) := hIntegralK
  let : IsIntegral
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
    IsIntegral.of_isIso (pullbackSpecIso k K L).inv
  exact IsIntegral.of_isIso h.isoPullback.inv

/-- The algebra structure on the function field induced by a morphism to an
affine base. -/
@[reducible] noncomputable def Scheme.Hom.functionFieldAlgebra
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (.of R)) : Algebra R X.functionField :=
  (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) trivial).hom).toAlgebra

@[reducible] private noncomputable def sectionAlgebra
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (U : X.Opens) :
    Algebra k Γ(X, U) :=
  (((Scheme.ΓSpecIso (.of k)).inv ≫
    (U.ι ≫ f).appTop ≫ U.topIso.hom).hom).toAlgebra

private lemma hom_eq_isoSpec_hom_comp_specMap
    {R : Type u} [CommRing R] {Z : Scheme.{u}} [IsAffine Z]
    (p : Z ⟶ Spec (.of R)) :
    p = Z.isoSpec.hom ≫ Spec.map
      ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) := by
  have hnat : Z.isoSpec.hom ≫ Spec.map p.appTop =
      p ≫ (Spec (.of R)).isoSpec.hom :=
    Scheme.isoSpec_hom_naturality p
  have hcancel : (Spec (.of R)).isoSpec.hom ≫
      Spec.map (Scheme.ΓSpecIso (.of R)).inv = 𝟙 _ := by
    rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id]
  calc
    p = p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = p ≫ ((Spec (.of R)).isoSpec.hom ≫
        Spec.map (Scheme.ΓSpecIso (.of R)).inv) :=
      congrArg (fun q ↦ p ≫ q) hcancel.symm
    _ = (p ≫ (Spec (.of R)).isoSpec.hom) ≫
        Spec.map (Scheme.ΓSpecIso (.of R)).inv :=
      (Category.assoc _ _ _).symm
    _ = (Z.isoSpec.hom ≫ Spec.map p.appTop) ≫
        Spec.map (Scheme.ΓSpecIso (.of R)).inv :=
      congrArg (fun q ↦ q ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv)
        hnat.symm
    _ = Z.isoSpec.hom ≫
        (Spec.map p.appTop ≫
          Spec.map (Scheme.ΓSpecIso (.of R)).inv) :=
      Category.assoc _ _ _
    _ = Z.isoSpec.hom ≫
        Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) := by
      rw [Spec.map_comp]

private lemma comp_open_eq_isoSpec_hom_comp_specMap_algebraMap
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (U : X.Opens) (hU : IsAffineOpen U) :
    U.ι ≫ f = hU.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom
        (@algebraMap k Γ(X, U) _ _ (sectionAlgebra f U))) := by
  let : Algebra k Γ(X, U) := sectionAlgebra f U
  let : IsAffine U := hU
  change U.ι ≫ f = hU.isoSpec.hom ≫
    Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫
      (U.ι ≫ f).appTop ≫ U.topIso.hom)
  calc
    U.ι ≫ f = U.toScheme.isoSpec.hom ≫
        Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫
          (U.ι ≫ f).appTop) :=
      hom_eq_isoSpec_hom_comp_specMap (U.ι ≫ f)
    _ = hU.isoSpec.hom ≫
        Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫
          (U.ι ≫ f).appTop ≫ U.topIso.hom) := by
      change U.toScheme.isoSpec.hom ≫
          Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appTop) =
        (U.toScheme.isoSpec.hom ≫ Spec.map U.topIso.inv) ≫
          Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫
            (U.ι ≫ f).appTop ≫ U.topIso.hom)
      rw [Category.assoc, ← Spec.map_comp, cancel_epi, Spec.map_inj]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma comp_open_appTop_topIso
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (U : X.Opens) :
    (U.ι ≫ f).appTop ≫ U.topIso.hom =
      f.appTop ≫ X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  rw [Scheme.Hom.comp_appTop, Category.assoc]
  congr 1
  change X.presheaf.map (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op ≫
      X.presheaf.map (eqToHom U.ι_image_top.symm).op = _
  rw [← Functor.map_comp]
  rfl

private lemma functionFieldAlgebra_eq_comp_sectionAlgebra
    {k : Type u} [CommRing k] {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (.of k)) (U : X.Opens) [Nonempty U] :
    @algebraMap k X.functionField _ _ f.functionFieldAlgebra =
      (@algebraMap Γ(X, U) X.functionField _ _
        (inferInstance : Algebra Γ(X, U) X.functionField)).comp
        (@algebraMap k Γ(X, U) _ _ (sectionAlgebra f U)) := by
  let : Algebra k Γ(X, U) := sectionAlgebra f U
  let : Algebra k X.functionField := f.functionFieldAlgebra
  ext a
  change X.presheaf.germ ⊤ (genericPoint X) trivial
      (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a)) =
    X.germToFunctionField U
      (U.topIso.hom ((U.ι ≫ f).appTop
        ((Scheme.ΓSpecIso (.of k)).inv a)))
  have hsection :
      U.topIso.hom ((U.ι ≫ f).appTop
        ((Scheme.ΓSpecIso (.of k)).inv a)) =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a)) := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom
        (comp_open_appTop_topIso f U)
        ((Scheme.ΓSpecIso (.of k)).inv a)
  rw [hsection]
  exact (X.presheaf.germ_res_apply
    (homOfLE (show U ≤ ⊤ from le_top))
    (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U)))
    (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a))).symm

/-- The function field of an integral, geometrically integral scheme over a
field is geometrically integral over that field. -/
theorem GeometricallyIntegral.spec_functionField
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f] :
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (@algebraMap k X.functionField _ _ f.functionFieldAlgebra))) := by
  let x : X := Nonempty.some inferInstance
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U :=
    isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))
  let : Nonempty U := ⟨⟨x, X.affineCover.covers x⟩⟩
  let : Algebra k Γ(X, U) := sectionAlgebra f U
  let : Algebra k X.functionField := f.functionFieldAlgebra
  let : Surjective (U.ι ≫ f) :=
    ⟨fun y ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ y⟩⟩
  have hOpen : GeometricallyIntegral (U.ι ≫ f) :=
    GeometricallyIntegral.comp_of_isOpenImmersion U.ι f
  have hSpec : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) := by
    have hComp : GeometricallyIntegral
        (hU.isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) := by
      rw [← comp_open_eq_isoSpec_hom_comp_specMap_algebraMap f U hU]
      exact hOpen
    let : MorphismProperty.RespectsIso
        (@GeometricallyIntegral : MorphismProperty Scheme.{u}) := by
      rw [GeometricallyIntegral.eq_geometrically, geometrically_eq_universally]
      exact MorphismProperty.universally_respectsIso _
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := (@GeometricallyIntegral : MorphismProperty Scheme.{u})) hU.isoSpec.hom _).mp hComp
  let : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) := hSpec
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsScalarTower k Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq'
      (functionFieldAlgebra_eq_comp_sectionAlgebra f U)
  exact GeometricallyIntegral.spec_of_isFractionRing
    (k := k) (R := Γ(X, U)) (K := X.functionField)

end AlgebraicGeometry
