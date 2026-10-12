/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.DVRFiniteEtaleAlgebra
import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.DVRNormalization
import Mathlib.Algebra.Algebra.Tower
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Opposites
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Extending unramified generic covers over a DVR

Let `R` be a discrete valuation ring with fraction field `K`. For an
arbitrary finite étale cover of `Spec K`, take the finite étale coordinate
algebra supplied by the affine equivalence. If all its actual field factors
are unramified over `R`, the integral closure gives a finite étale model
over `R`.

The affine equivalence transports that model back to a cover of `Spec R`.
Its compatibility with tensor-product base change, together with the
integral-closure generic-fibre equivalence, gives an isomorphism from the
actual scheme pullback to the original cover, over `Spec K`.

This is the DVR-local extension in the proof of
[Stacks Project, Tag 0H2W](https://stacks.math.columbia.edu/tag/0H2W).
Spreading this model to an open neighbourhood and applying purity to the
remaining boundary are separate steps.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

attribute [local instance] Ideal.Quotient.field

/-- A finite étale cover of a DVR's fraction field extends over the DVR when
every field factor of its coordinate algebra has ramification index one and
separable residue extensions over the DVR.

The coordinate algebra and its induced `R`-algebra structure are retained
from the statement into the proof. The model is obtained from their actual
integral closure, and the displayed isomorphism is in the finite étale
category over `Spec K`, so it respects the structure maps. -/
theorem exists_dvr_extension_of_unramified_field_factors
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (Y : FiniteEtale (Spec (.of K))) :
    let A : CommAlgCat.FiniteEtale.{u} K :=
      (affineEquivalence (.of K)).functor.obj (Opposite.op Y)
    let : Algebra R A := Algebra.compHom A (algebraMap R K)
    (∀ m : MaximalSpectrum A, SchemeTheory.IsUnramifiedOverDVR R (A ⧸ m.asIdeal)) →
      ∃ Z : FiniteEtale (Spec (.of R)),
        Nonempty ((FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj Z ≅ Y) := by
  intro A hRA hunramified
  have : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq' rfl
  have hfiniteEtale : Module.Finite R (integralClosure R A) ∧
      Algebra.Etale R (integralClosure R A) :=
    SchemeTheory.finite_etale_integralClosure_of_finiteEtale_unramifiedOverDVR
      R K A hunramified
  have : Module.Finite R (integralClosure R A) := hfiniteEtale.1
  have : Algebra.Etale R (integralClosure R A) := hfiniteEtale.2
  let B : CommAlgCat.FiniteEtale.{u} R :=
    CommAlgCat.FiniteEtale.of R (integralClosure R A)
  let Z : FiniteEtale (Spec (.of R)) :=
    ((affineEquivalence (.of R)).inverse.obj B).unop
  let eCoordinates : (affineEquivalence (.of R)).functor.obj (Opposite.op Z) ≅ B :=
    (affineEquivalence (.of R)).counitIso.app B
  let eGeneric : (CommAlgCat.FiniteEtale.baseChange R K).obj B ≅ A :=
    CommAlgCat.FiniteEtale.isoMk
      (SchemeTheory.integralClosureFiniteEtaleGenericFiberEquiv R K A)
  let F : FiniteEtale (Spec (.of R)) ⥤ FiniteEtale (Spec (.of K)) :=
    FiniteEtale.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let eBaseChange : (affineEquivalence (.of K)).functor.obj (Opposite.op (F.obj Z)) ≅ A :=
    ((affineEquivalenceCompBaseChangeIso R K).app (Opposite.op Z)).symm ≪≫
      (CommAlgCat.FiniteEtale.baseChange R K).mapIso eCoordinates ≪≫ eGeneric
  let eCover : Opposite.op (F.obj Z) ≅ Opposite.op Y :=
    (affineEquivalence (.of K)).functor.preimageIso eBaseChange
  exact ⟨Z, ⟨eCover.unop.symm⟩⟩

end AlgebraicGeometry.FiniteEtale
