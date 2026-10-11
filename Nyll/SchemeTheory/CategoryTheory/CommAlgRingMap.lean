/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Native categorical algebra maps from their proved coefficient squares

The coefficient maps are the native maps stored by the commutative algebra
objects. The categorical morphism is constructed only after its actual
RingHom coefficient square has been proved. No new algebra action is used.
-/

noncomputable section

namespace SchemeTheory

universe u v

variable {A : Type u} [CommRing A]

/-- The coefficient map of the actual native commutative algebra object. -/
def commAlgCoefficientMap (R : CommAlgCat.{v} A) : A →+* R :=
  algebraMap A R

/-- The computed coefficient map is precisely the stored native action. -/
theorem commAlgCoefficientMap_eq_algebraMap (R : CommAlgCat.{v} A) :
    commAlgCoefficientMap R = algebraMap A R := rfl

/-- The same native object in the category of algebras. -/
def commAlgToAlgCat (R : CommAlgCat.{v} A) : AlgCat.{v} A :=
  AlgCat.of A R

/-- Construct the native categorical morphism from the actual ring map
and its proved square with the stored coefficient maps. -/
def commAlgRingHomToAlgCatHom (R S : CommAlgCat.{v} A) (f : R →+* S)
    (h : f.comp (commAlgCoefficientMap R) = commAlgCoefficientMap S) :
    AlgCat.Hom (commAlgToAlgCat R) (commAlgToAlgCat S) :=
  AlgCat.ofHom
    ({ f with commutes' := fun a => congrArg (fun g : A →+* S => g a) h } : R →ₐ[A] S)

/-- The categorical construction retains the given actual RingHom. -/
theorem commAlgRingHomToAlgCatHom_toRingHom
    (R S : CommAlgCat.{v} A) (f : R →+* S)
    (h : f.comp (commAlgCoefficientMap R) = commAlgCoefficientMap S) :
    (commAlgRingHomToAlgCatHom R S f h).hom.toRingHom = f := rfl

end SchemeTheory
