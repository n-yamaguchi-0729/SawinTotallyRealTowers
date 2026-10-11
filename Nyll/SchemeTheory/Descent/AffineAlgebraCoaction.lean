/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.AlgebraCoaction
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Algebra coactions from affine overlap isomorphisms

The two affine overlap schemes have coordinate rings `C ⊗[R] B` and
`B ⊗[R] C`. An isomorphism between them over `Spec (B ⊗[R] B)` determines
an actual algebra equivalence by the full faithfulness of `Spec`. Its
linearity follows from the given square over the overlap base. The scheme
diagonal normalization gives the literal diagonal law used by
`Algebra.Descent.tensorCoaction_counit`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Algebra.Descent

variable (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

/-- The structure map of the first affine overlap over the tensor-square base. -/
def affineOverlapSourceBase : B ⊗[R] B →ₐ[B] C ⊗[R] B :=
  Algebra.TensorProduct.map (Algebra.ofId B C) (.id R B)

/-- The structure map of the second affine overlap over the tensor-square base. -/
def affineOverlapTargetBase : B ⊗[R] B →ₐ[B] B ⊗[R] C :=
  Algebra.TensorProduct.map (.id B B) (IsScalarTower.toAlgHom R B C)

/-- The ring equivalence induced contravariantly by an isomorphism of the affine overlap schemes. -/
def affineOverlapRingEquiv
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B))) :
    C ⊗[R] B ≃+* B ⊗[R] C :=
  (Spec.fullyFaithful.preimageIso
    (X := Opposite.op (CommRingCat.of (B ⊗[R] C)))
    (Y := Opposite.op (CommRingCat.of (C ⊗[R] B))) α).unop.commRingCatIsoToRingEquiv

omit [Algebra B C] [IsScalarTower R B C] in
private theorem affineOverlapRingEquiv_spec
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B))) :
    Spec.map (CommRingCat.ofHom (affineOverlapRingEquiv R B C α).toRingHom) =
      α.hom :=
  Spec.map_preimage_unop α.hom

private theorem affineOverlapRingEquiv_base
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B)))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom))
    (z : B ⊗[R] B) :
    affineOverlapRingEquiv R B C α (affineOverlapSourceBase R B C z) =
      affineOverlapTargetBase R B C z := by
  have h :
      CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom ≫
        CommRingCat.ofHom (affineOverlapRingEquiv R B C α).toRingHom =
      CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, affineOverlapRingEquiv_spec]
    exact hα
  exact congrArg (fun k : CommRingCat.of (B ⊗[R] B) ⟶
    CommRingCat.of (B ⊗[R] C) ↦ k.hom z) h

/-- The algebra overlap equivalence extracted from a scheme isomorphism over
the actual affine overlap base. The direction reverses under `Spec`. -/
def affineOverlapAlgEquiv
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B)))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom)) :
    C ⊗[R] B ≃ₐ[B] B ⊗[R] C :=
  AlgEquiv.ofRingEquiv (f := affineOverlapRingEquiv R B C α) fun b ↦ by
    calc
      affineOverlapRingEquiv R B C α (algebraMap B (C ⊗[R] B) b) =
          affineOverlapRingEquiv R B C α
            (affineOverlapSourceBase R B C (algebraMap B (B ⊗[R] B) b)) :=
        congrArg (affineOverlapRingEquiv R B C α)
          ((affineOverlapSourceBase R B C).commutes b).symm
      _ = affineOverlapTargetBase R B C (algebraMap B (B ⊗[R] B) b) :=
        affineOverlapRingEquiv_base R B C α hα _
      _ = algebraMap B (B ⊗[R] C) b :=
        (affineOverlapTargetBase R B C).commutes b

/-- The constructed algebra equivalence induces the given overlap map exactly. -/
theorem affineOverlapAlgEquiv_spec
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B)))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom)) :
    Spec.map (CommRingCat.ofHom (affineOverlapAlgEquiv R B C α hα).toRingHom) =
      α.hom :=
  affineOverlapRingEquiv_spec R B C α

/-- The whole tensor-square structure map is preserved, including its second
coordinate, not only the scalar action used to bundle the equivalence. -/
theorem affineOverlapAlgEquiv_base
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B)))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom)) :
    (affineOverlapAlgEquiv R B C α hα).toAlgHom.comp (affineOverlapSourceBase R B C) =
      affineOverlapTargetBase R B C :=
  AlgHom.ext (affineOverlapRingEquiv_base R B C α hα)

/-- Diagonal normalization of the scheme overlap isomorphism yields the exact
algebra diagonal law required by the coaction construction. -/
theorem affineOverlapAlgEquiv_diagonal
    (α : Spec (.of (B ⊗[R] C)) ≅ Spec (.of (C ⊗[R] B)))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom (affineOverlapSourceBase R B C).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineOverlapTargetBase R B C).toRingHom))
    (hdiag : Spec.map (CommRingCat.ofHom (tensorTargetDiagonal R B C).toRingHom) ≫
        α.hom = Spec.map (CommRingCat.ofHom (tensorSourceDiagonal R B C).toRingHom)) :
    (tensorTargetDiagonal R B C).comp (affineOverlapAlgEquiv R B C α hα).toAlgHom =
      tensorSourceDiagonal R B C := by
  have h :
      CommRingCat.ofHom (affineOverlapAlgEquiv R B C α hα).toRingHom ≫
        CommRingCat.ofHom (tensorTargetDiagonal R B C).toRingHom =
      CommRingCat.ofHom (tensorSourceDiagonal R B C).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, affineOverlapAlgEquiv_spec]
    exact hdiag
  exact AlgHom.ext fun z ↦ congrArg (fun k : CommRingCat.of (C ⊗[R] B) ⟶
    CommRingCat.of C ↦ k.hom z) h

end Algebra.Descent
