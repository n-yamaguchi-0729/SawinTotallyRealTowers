/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Algebra maps on reduction modulo a base ideal

The map between the quotients by the extended base ideal is an algebra map
over the quotient base. The quotient/tensor equivalences identify it with
the canonical tensor-product base change.
-/


@[expose] public section

open scoped TensorProduct

universe u v w

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- An algebra map carries the ideal extended from the base to the corresponding
extended ideal in the target. -/
  theorem map_extendedIdeal (f : A →ₐ[R] B) (I : Ideal R) :
    (I.map (algebraMap R A)).map f.toRingHom = I.map (algebraMap R B) := by
  rw [Ideal.map_map]
  congr 1
  ext r
  exact f.commutes r

/-- The quotient-base algebra map induced by an algebra map. -/
def quotientBaseChange (f : A →ₐ[R] B) (I : Ideal R) :
    A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I] B ⧸ I.map (algebraMap R B) :=
  (Ideal.quotientMapₐ (I.map (algebraMap R B)) f
    (Ideal.map_le_iff_le_comap.mp (f.map_extendedIdeal I).le)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective

@[simp]
theorem quotientBaseChange_mk (f : A →ₐ[R] B) (I : Ideal R) (a : A) :
    f.quotientBaseChange I (Ideal.Quotient.mk (I.map (algebraMap R A)) a) =
      Ideal.Quotient.mk (I.map (algebraMap R B)) (f a) := rfl

/-- The concrete quotient map agrees with tensor-product base change under
the canonical quotient/tensor comparisons. -/
theorem quotientBaseChange_tensorProduct (f : A →ₐ[R] B) (I : Ideal R) :
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toAlgHom.comp
        (f.quotientBaseChange I) =
      (Algebra.TensorProduct.map (.id (R ⧸ I) (R ⧸ I)) f).comp
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).toAlgHom := by
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (1 : R ⧸ I) ⊗ₜ[R] f a =
    Algebra.TensorProduct.map (.id (R ⧸ I) (R ⧸ I)) f ((1 : R ⧸ I) ⊗ₜ[R] a)
  rw [Algebra.TensorProduct.map_tmul, map_one]

end AlgHom
