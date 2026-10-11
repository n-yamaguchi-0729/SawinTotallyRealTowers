/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.Global
public import Nyll.SchemeTheory.WeilRestriction.BaseChange
public import Nyll.SchemeTheory.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Finite étale internal Homs over an affine base

For finite étale `R`-algebras `A` and `B`, with `A` free as an `R`-module,
the relative internal Hom from `Spec A` to `Spec B` is represented by a
finite étale scheme over `Spec R`. The representing equivalence applies
to every scheme over `Spec R`.

The finite étale structure is obtained from the algebraic Weil restriction
theorem and the affine criteria for finite and étale scheme morphisms.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeTheory.Affine

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [Module.Free R A] [Module.Finite R A] [Algebra.Etale R A]
  [Module.Finite R B] [Algebra.Etale R B]

/-- The structure morphism of the internal Hom's explicit affine representer
is finite étale. -/
instance globalInternalHomSpecRepresenter_isFiniteEtale :
    IsFiniteEtale (globalInternalHomSpecRepresenter
      (R := R) (A := A) (B := B)).hom := by
  let H : CommAlgCat.{u} R := algebraRepresenter (R := R) (A := A) (B := B)
  have hH : Module.Finite R H ∧ Algebra.Etale R H :=
    CommAlgCat.affineWeilRestriction_finiteEtale (R := R) (A := A) (B := B)
  refine { toIsFinite := ?_, toEtale := ?_ }
  · change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R H)))
    exact (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R H))).2
      ((RingHom.finite_algebraMap (A := R) (B := H)).2 hH.1)
  · change Etale (Spec.map (CommRingCat.ofHom (algebraMap R H)))
    exact (HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom (algebraMap R H))).2
      ((RingHom.etale_algebraMap (R := R) (S := H)).2 hH.2)

/-- The finite étale scheme representing the relative internal Hom from
`Spec A` to `Spec B` over `Spec R`. -/
def finiteEtaleInternalHomRepresenter : FiniteEtale (Spec (CommRingCat.of R)) where
  toComma := globalInternalHomSpecRepresenter (R := R) (A := A) (B := B)
  prop := globalInternalHomSpecRepresenter_isFiniteEtale (R := R) (A := A) (B := B)

/-- The finite étale internal Hom represents morphisms from
`T ×_{Spec R} Spec A` to `Spec B` for every scheme `T` over `Spec R`. -/
def finiteEtaleInternalHomRepresentable :
    (globalInternalHomFunctor (R := R) (A := A) (B := B)).RepresentableBy
      ((FiniteEtale.forget (Spec (CommRingCat.of R))).obj
        (finiteEtaleInternalHomRepresenter (R := R) (A := A) (B := B))) :=
  globalInternalHomSpecRepresentable (R := R) (A := A) (B := B)

/-- After any scheme base change, the finite etale pullback of the affine
internal Hom still represents morphisms between the two pulled-back schemes. -/
def finiteEtaleInternalHomBaseChangeRepresentable
    {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of R)) :
    (SchemeTheory.WeilRestriction.relativeInternalHomFunctor
      ((Over.pullback f).obj (specAOver (R := R) (A := A)))
      ((Over.pullback f).obj (specBOver (R := R) (B := B)))).RepresentableBy
        ((FiniteEtale.forget S).obj
          ((FiniteEtale.pullback f).obj
            (finiteEtaleInternalHomRepresenter (R := R) (A := A) (B := B)))) :=
  SchemeTheory.WeilRestriction.relativeInternalHomRepresentableBaseChange f
    (finiteEtaleInternalHomRepresentable (R := R) (A := A) (B := B))

end SchemeTheory.Affine
