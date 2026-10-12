/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.Global
public import Nyll.SchemeTheory.Affine.WeilRestriction.Glued
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Nyll.SchemeTheory.WeilRestriction.BaseChange
public import Nyll.SchemeTheory.WeilRestriction.GluedRepresentable
public import Nyll.SchemeTheory.WeilRestriction.Sheaf

/-!
# Finite étale internal Hom without a global basis

For finite étale `R`-algebras `A` and `B`, the locally constructed internal
Hom schemes glue to a finite étale scheme representing the internal Hom on
all schemes over `Spec R`. The sheaf condition supplies the global representing
property. Pulling this object back represents the internal Hom after an
arbitrary scheme base change.

No global freeness assumption on `A` is used.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry
open SchemeTheory.WeilRestriction

noncomputable section

universe u

namespace SchemeTheory.Affine

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Algebra.Etale R A]
  [Module.Finite R B] [Algebra.Etale R B]

/-- The glued finite étale scheme represents the internal Hom on all test schemes. -/
def finiteEtaleInternalHomGluedRepresentable :
    (globalInternalHomFunctor (R := R) (A := A) (B := B)).RepresentableBy
      ((FiniteEtale.forget (Spec (CommRingCat.of R))).obj
        (finiteEtaleInternalHomGlued (R := R) (A := A) (B := B))) :=
  gluedLocalRepresentable
    (globalInternalHomFunctor (R := R) (A := A) (B := B))
    (finiteEtaleInternalHomDirectedCover (R := R) (A := A) (B := B))
    (fun i ↦ (FiniteEtale.forget ((finiteEtaleInternalHomDirectedCover
      (R := R) (A := A) (B := B)).X i)).obj
        (finiteEtaleInternalHomDirectedRepresenter (R := R) (A := A) (B := B) i))
    (fun i ↦ finiteEtaleInternalHomDirectedRepresentable (R := R) (A := A) (B := B) i)
    (relativeInternalHom_isSheaf Scheme.zariskiTopology
      (specAOver (R := R) (A := A)) (specBOver (R := R) (B := B)))

/-- The finite étale internal Hom remains a representer after arbitrary scheme base change. -/
def finiteEtaleInternalHomGluedBaseChangeRepresentable {S : Scheme.{u}}
    (f : S ⟶ Spec (CommRingCat.of R)) :
    (relativeInternalHomFunctor
      ((Over.pullback f).obj (specAOver (R := R) (A := A)))
      ((Over.pullback f).obj (specBOver (R := R) (B := B)))).RepresentableBy
        ((FiniteEtale.forget S).obj ((FiniteEtale.pullback f).obj
          (finiteEtaleInternalHomGlued (R := R) (A := A) (B := B)))) :=
  relativeInternalHomRepresentableBaseChange f
    (U := specAOver (R := R) (A := A))
    (V := specBOver (R := R) (B := B))
    (W := (FiniteEtale.forget (Spec (CommRingCat.of R))).obj
      (finiteEtaleInternalHomGlued (R := R) (A := A) (B := B)))
    (finiteEtaleInternalHomGluedRepresentable (R := R) (A := A) (B := B))

end SchemeTheory.Affine
