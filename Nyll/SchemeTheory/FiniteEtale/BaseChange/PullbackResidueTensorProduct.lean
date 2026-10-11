/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackResidue

/-!
# The explicit residue-field tensor map of a pullback point

This file replaces the categorical pushout in the pullback-carrier API by
the ordinary tensor product and records the two factor maps.  The resulting
map is surjective as soon as the categorical residue tensor is Artinian.
-/

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Pullback

universe u

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- The canonical map from the ordinary tensor product of the projected
residue fields to the residue field of a pullback point. -/
noncomputable def tensorProductToResidueField (t : ↑(pullback f g)) :
    let T := Triplet.ofPoint t
    letI : Algebra (S.residueField T.s) (X.residueField T.x) :=
      (((S.residueFieldCongr T.hx).inv ≫
        f.residueFieldMap T.x).hom).toAlgebra
    letI : Algebra (S.residueField T.s) (Y.residueField T.y) :=
      (((S.residueFieldCongr T.hy).inv ≫
        g.residueFieldMap T.y).hom).toAlgebra
    CommRingCat.of (X.residueField T.x ⊗[S.residueField T.s]
      Y.residueField T.y) ⟶ (pullback f g).residueField t := by
  let T := Triplet.ofPoint t
  letI : Algebra (S.residueField T.s) (X.residueField T.x) :=
    (((S.residueFieldCongr T.hx).inv ≫
      f.residueFieldMap T.x).hom).toAlgebra
  letI : Algebra (S.residueField T.s) (Y.residueField T.y) :=
    (((S.residueFieldCongr T.hy).inv ≫
      g.residueFieldMap T.y).hom).toAlgebra
  exact (T.tensorIsoTensorProduct).inv ≫ ofPointTensor t

/-- The inverse tensor-product comparison sends the explicit left inclusion
to the categorical pushout inclusion. -/
theorem includeLeft_tensorIsoTensorProduct_inv
    (T : Triplet f g) :
    letI : Algebra (S.residueField T.s) (X.residueField T.x) :=
      (((S.residueFieldCongr T.hx).inv ≫
        f.residueFieldMap T.x).hom).toAlgebra
    letI : Algebra (S.residueField T.s) (Y.residueField T.y) :=
      (((S.residueFieldCongr T.hy).inv ≫
        g.residueFieldMap T.y).hom).toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := S.residueField T.s) (A := X.residueField T.x)
        (B := Y.residueField T.y)) ≫
      (T.tensorIsoTensorProduct).inv = T.tensorInl := by
  let : Algebra (S.residueField T.s) (X.residueField T.x) :=
    (((S.residueFieldCongr T.hx).inv ≫
      f.residueFieldMap T.x).hom).toAlgebra
  let : Algebra (S.residueField T.s) (Y.residueField T.y) :=
    (((S.residueFieldCongr T.hy).inv ≫
      g.residueFieldMap T.y).hom).toAlgebra
  rw [← cancel_mono (T.tensorIsoTensorProduct).hom]
  simp

/-- The inverse tensor-product comparison sends the explicit right inclusion
to the categorical pushout inclusion. -/
theorem includeRight_tensorIsoTensorProduct_inv
    (T : Triplet f g) :
    letI : Algebra (S.residueField T.s) (X.residueField T.x) :=
      (((S.residueFieldCongr T.hx).inv ≫
        f.residueFieldMap T.x).hom).toAlgebra
    letI : Algebra (S.residueField T.s) (Y.residueField T.y) :=
      (((S.residueFieldCongr T.hy).inv ≫
        g.residueFieldMap T.y).hom).toAlgebra
    CommRingCat.ofHom ((Algebra.TensorProduct.includeRight
        (R := S.residueField T.s) (A := X.residueField T.x)
        (B := Y.residueField T.y)).toRingHom) ≫
      (T.tensorIsoTensorProduct).inv = T.tensorInr := by
  let : Algebra (S.residueField T.s) (X.residueField T.x) :=
    (((S.residueFieldCongr T.hx).inv ≫
      f.residueFieldMap T.x).hom).toAlgebra
  let : Algebra (S.residueField T.s) (Y.residueField T.y) :=
    (((S.residueFieldCongr T.hy).inv ≫
      g.residueFieldMap T.y).hom).toAlgebra
  rw [← cancel_mono (T.tensorIsoTensorProduct).hom]
  simp

/-- The explicit residue-field tensor map is surjective whenever the
categorical residue tensor selected by the pullback carrier is Artinian. -/
theorem tensorProductToResidueField_surjective_of_isArtinian
    (t : ↑(pullback f g))
    [IsArtinianRing (Triplet.ofPoint t).tensor] :
    let T := Triplet.ofPoint t
    letI : Algebra (S.residueField T.s) (X.residueField T.x) :=
      (((S.residueFieldCongr T.hx).inv ≫
        f.residueFieldMap T.x).hom).toAlgebra
    letI : Algebra (S.residueField T.s) (Y.residueField T.y) :=
      (((S.residueFieldCongr T.hy).inv ≫
        g.residueFieldMap T.y).hom).toAlgebra
    Function.Surjective (tensorProductToResidueField t) := by
  dsimp only
  let T := Triplet.ofPoint t
  let : Algebra (S.residueField T.s) (X.residueField T.x) :=
    (((S.residueFieldCongr T.hx).inv ≫
      f.residueFieldMap T.x).hom).toAlgebra
  let : Algebra (S.residueField T.s) (Y.residueField T.y) :=
    (((S.residueFieldCongr T.hy).inv ≫
      g.residueFieldMap T.y).hom).toAlgebra
  exact (ofPointTensor_surjective_of_isArtinian t).comp
    (T.tensorIsoTensorProduct).commRingCatIsoToRingEquiv.symm.surjective

end AlgebraicGeometry.Scheme.Pullback
