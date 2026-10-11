/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Artinian.Module

/-!
# Residue fields of Artinian pullback tensors

For a point of a scheme-theoretic pullback, the pullback carrier API gives a
canonical map from the tensor product of the two residue fields to the
residue field of the point.  When that tensor product is Artinian, this map
is surjective: the prime selected by the point is maximal, so its canonical
residue map is already a quotient map.
-/

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Pullback

universe u

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

namespace Triplet

/-- The categorical pushout used in the pullback-carrier description is
canonically the ordinary tensor product of the two residue fields. -/
noncomputable def tensorIsoTensorProduct (T : Triplet f g) :
    letI : Algebra (S.residueField T.s) (X.residueField T.x) :=
      (((S.residueFieldCongr T.hx).inv ≫
        f.residueFieldMap T.x).hom).toAlgebra
    letI : Algebra (S.residueField T.s) (Y.residueField T.y) :=
      (((S.residueFieldCongr T.hy).inv ≫
        g.residueFieldMap T.y).hom).toAlgebra
    T.tensor ≅ CommRingCat.of
      (X.residueField T.x ⊗[S.residueField T.s]
        Y.residueField T.y) := by
  letI : Algebra (S.residueField T.s) (X.residueField T.x) :=
    (((S.residueFieldCongr T.hx).inv ≫
      f.residueFieldMap T.x).hom).toAlgebra
  letI : Algebra (S.residueField T.s) (Y.residueField T.y) :=
    (((S.residueFieldCongr T.hy).inv ≫
      g.residueFieldMap T.y).hom).toAlgebra
  exact (IsPushout.of_hasPushout _ _).isoIsPushout _ _
    (CommRingCat.isPushout_tensorProduct
      (S.residueField T.s) (X.residueField T.x)
      (Y.residueField T.y))

@[reassoc (attr := simp)]
theorem tensorInl_tensorIsoTensorProduct_hom (T : Triplet f g) :
    letI : Algebra (S.residueField T.s) (X.residueField T.x) :=
      (((S.residueFieldCongr T.hx).inv ≫
        f.residueFieldMap T.x).hom).toAlgebra
    letI : Algebra (S.residueField T.s) (Y.residueField T.y) :=
      (((S.residueFieldCongr T.hy).inv ≫
        g.residueFieldMap T.y).hom).toAlgebra
    T.tensorInl ≫ (tensorIsoTensorProduct T).hom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := S.residueField T.s) (A := X.residueField T.x)
        (B := Y.residueField T.y)) := by
  let : Algebra (S.residueField T.s) (X.residueField T.x) :=
    (((S.residueFieldCongr T.hx).inv ≫
      f.residueFieldMap T.x).hom).toAlgebra
  let : Algebra (S.residueField T.s) (Y.residueField T.y) :=
    (((S.residueFieldCongr T.hy).inv ≫
      g.residueFieldMap T.y).hom).toAlgebra
  exact IsPushout.inl_isoIsPushout_hom
    (X.residueField T.x) (Y.residueField T.y)
    (IsPushout.of_hasPushout _ _)
    (CommRingCat.isPushout_tensorProduct
      (S.residueField T.s) (X.residueField T.x)
      (Y.residueField T.y))

@[reassoc (attr := simp)]
theorem tensorInr_tensorIsoTensorProduct_hom (T : Triplet f g) :
    letI : Algebra (S.residueField T.s) (X.residueField T.x) :=
      (((S.residueFieldCongr T.hx).inv ≫
        f.residueFieldMap T.x).hom).toAlgebra
    letI : Algebra (S.residueField T.s) (Y.residueField T.y) :=
      (((S.residueFieldCongr T.hy).inv ≫
        g.residueFieldMap T.y).hom).toAlgebra
    T.tensorInr ≫ (tensorIsoTensorProduct T).hom =
      CommRingCat.ofHom ((Algebra.TensorProduct.includeRight
        (R := S.residueField T.s) (A := X.residueField T.x)
        (B := Y.residueField T.y)).toRingHom) := by
  let : Algebra (S.residueField T.s) (X.residueField T.x) :=
    (((S.residueFieldCongr T.hx).inv ≫
      f.residueFieldMap T.x).hom).toAlgebra
  let : Algebra (S.residueField T.s) (Y.residueField T.y) :=
    (((S.residueFieldCongr T.hy).inv ≫
      g.residueFieldMap T.y).hom).toAlgebra
  exact IsPushout.inr_isoIsPushout_hom
    (X.residueField T.x) (Y.residueField T.y)
    (IsPushout.of_hasPushout _ _)
    (CommRingCat.isPushout_tensorProduct
      (S.residueField T.s) (X.residueField T.x)
      (Y.residueField T.y))

end Triplet

private theorem ofPointTensor_SpecTensorTo_surjective
    (T : Triplet f g) (p : Spec T.tensor)
    [IsArtinianRing T.tensor] :
    Function.Surjective (ofPointTensor (T.SpecTensorTo p)) := by
  let : p.asIdeal.IsPrime := p.isPrime
  let : p.asIdeal.IsMaximal :=
    IsArtinianRing.isMaximal_of_isPrime p.asIdeal
  let e :=
    (Scheme.Spec.residueFieldIso T.tensor p).commRingCatIsoToRingEquiv
  let q : T.tensor ⟶ (Spec T.tensor).residueField p :=
    CommRingCat.ofHom (algebraMap T.tensor p.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso T.tensor p).inv
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨a, ha⟩ :=
      p.asIdeal.algebraMap_residueField_surjective (e z)
    refine ⟨a, e.injective ?_⟩
    change e (e.symm (algebraMap T.tensor p.asIdeal.ResidueField a)) = e z
    rw [e.apply_symm_apply, ha]
  let c := (Triplet.tensorCongr (T.ofPoint_SpecTensorTo p).symm).hom
  let a := ofPointTensor (T.SpecTensorTo p)
  let r := Scheme.Hom.residueFieldMap T.SpecTensorTo p
  have hmap : c ≫ a ≫ r = q := by
    rw [← Spec.map_inj]
    rw [Spec.map_comp, Spec.map_comp]
    change Spec.map r ≫ Spec.map a ≫ Spec.map c = Spec.map q
    rw [Triplet.Spec_ofPointTensor_SpecTensorTo]
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    rw [← Spec.map_comp]
    rfl
  intro z
  obtain ⟨x, hx⟩ := hq (r z)
  refine ⟨c x, r.hom.injective ?_⟩
  have hcx := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmap) x
  change r (a (c x)) = q x at hcx
  exact hcx.trans hx

/-- The canonical map from the tensor product of the projected residue
fields to the residue field of a pullback point is surjective whenever the
tensor product is Artinian. -/
theorem ofPointTensor_surjective_of_isArtinian
    (t : ↑(pullback f g))
    [IsArtinianRing (Triplet.ofPoint t).tensor] :
    Function.Surjective (ofPointTensor t) := by
  have h := ofPointTensor_SpecTensorTo_surjective
    (Triplet.ofPoint t) (SpecOfPoint t)
  rw [SpecTensorTo_SpecOfPoint] at h
  exact h

end AlgebraicGeometry.Scheme.Pullback
