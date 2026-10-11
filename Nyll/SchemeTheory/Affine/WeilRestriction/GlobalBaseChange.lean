/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.Global
public import Nyll.SchemeTheory.Affine.WeilRestriction.FiniteEtale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Base change of the global affine internal Hom

For finite free `A/R` and finitely presented `B/R`, the explicit spectrum
representing the relative internal Hom commutes with arbitrary affine base change.
The comparison is an isomorphism over `Spec S`, obtained from the algebraic
base-change isomorphism and the spectrum of a tensor product.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped TensorProduct

universe u

noncomputable section

namespace SchemeTheory.Affine

/-- The pullback of a spectrum to `Spec S` is the spectrum of its scalar extension. -/
def specOverBaseChangeIso
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] :
    (Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
        ((specOverFunctor (CommRingCat.of R)).obj
          (Opposite.op (CommAlgCat.of R C))) ≅
      (specOverFunctor (CommRingCat.of S)).obj
        (Opposite.op (CommAlgCat.of S (S ⊗[R] C))) :=
  Over.isoMk
    (pullbackSymmetry
      (Spec.map (CommRingCat.ofHom (algebraMap R C)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≪≫
        pullbackSpecIso R S C) (by
      change
        ((pullbackSymmetry
          (Spec.map (CommRingCat.ofHom (algebraMap R C)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom ≫
            (pullbackSpecIso R S C).hom) ≫
              Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] C))) =
          pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap R C)))
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      rw [Category.assoc, pullbackSpecIso_hom_fst',
        pullbackSymmetry_hom_comp_fst])

section BaseChange

variable {R S A B : Type u}
  [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B]
  [Module.Free R A] [Module.Finite R A]
  [Algebra.FinitePresentation R B]

/-- The global affine internal Hom representer commutes with affine base change. -/
def globalInternalHomSpecBaseChangeIso :
    (Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
        (globalInternalHomSpecRepresenter (R := R) (A := A) (B := B)) ≅
      globalInternalHomSpecRepresenter
        (R := S) (A := S ⊗[R] A) (B := S ⊗[R] B) :=
  (specOverBaseChangeIso R S
    (algebraRepresenter (R := R) (A := A) (B := B))).trans
      ((specOverFunctor (CommRingCat.of S)).mapIso
        (CommAlgCat.affineWeilRestrictionBaseChangeIso
          (R := R) (S := S) (A := A) (B := B)).symm.op)

/-- The pulled-back representer represents the internal Hom after scalar extension. -/
def globalInternalHomSpecBaseChangeRepresentable :
    (globalInternalHomFunctor
      (R := S) (A := S ⊗[R] A) (B := S ⊗[R] B)).RepresentableBy
        ((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
            (globalInternalHomSpecRepresenter (R := R) (A := A) (B := B))) :=
  (globalInternalHomSpecRepresentable
    (R := S) (A := S ⊗[R] A) (B := S ⊗[R] B)).ofIsoObj
      (globalInternalHomSpecBaseChangeIso (R := R) (S := S) (A := A) (B := B))

end BaseChange

end SchemeTheory.Affine
