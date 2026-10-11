/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Descent of geometric integrality

This file records a descent criterion for geometric integrality over a
field.  The morphism used for descent need not be flat: quasicompact
scheme-theoretic dominance is enough, since it remains scheme-theoretically
dominant after every field extension of the base.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The morphism from the residue field of the generic point of an integral
scheme is flat. -/
lemma Scheme.flat_fromSpecResidueField_genericPoint
    (S : Scheme.{u}) [IsIntegral S] :
    Flat (S.fromSpecResidueField (genericPoint S)) := by
  apply Flat.of_stalkMap
  intro x
  have hx : S.fromSpecResidueField (genericPoint S) x = genericPoint S := by
    simp [Scheme.fromSpecResidueField]
  let e : S.presheaf.stalk (S.fromSpecResidueField (genericPoint S) x) ≃+*
      S.functionField :=
    RingEquiv.cast (congrArg (fun y ↦ S.presheaf.stalk y) hx)
  exact RingHom.Flat.of_isField
    (e.toMulEquiv.isField (Field.toIsField S.functionField)) _

/-- Geometric integrality over a field descends through a quasicompact,
scheme-theoretically dominant morphism. -/
lemma GeometricallyIntegral.of_comp_of_isSchemeTheoreticallyDominant
    {k : CommRingCat.{u}} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec k) (hk : IsField k)
    [QuasiCompact f] [IsSchemeTheoreticallyDominant f]
    (h : GeometricallyIntegral (f ≫ g)) : GeometricallyIntegral g := by
  rw [geometricallyIntegral_iff] at h ⊢
  intro K _ y P fst snd H
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  have hflat : Flat (Spec.map φ) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField hk φ.hom
  let : Flat fst :=
    MorphismProperty.of_isPullback H.flip hflat
  let Q := pullback f fst
  let q : Q ⟶ P := pullback.snd f fst
  let : IsSchemeTheoreticallyDominant q := inferInstance
  let : QuasiCompact q := inferInstance
  have hQ : IsIntegral Q := by
    apply h (Spec.map φ) (pullback.fst f fst)
      (pullback.snd f fst ≫ snd)
    exact (IsPullback.of_hasPullback f fst).paste_vert H
  let : IsIntegral Q := hQ
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  constructor
  · rw [irreducibleSpace_def]
    change IsIrreducible (Set.univ : Set P)
    rw [← q.denseRange.closure_eq]
    simpa only [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ Q).image q
        q.continuous.continuousOn).closure
  · exact IsSchemeTheoreticallyDominant.isReduced q

/-- Geometric integrality over a field descends through a quasicompact
dominant morphism with reduced target. -/
lemma GeometricallyIntegral.of_comp_of_isDominant
    {k : CommRingCat.{u}} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec k) (hk : IsField k)
    [QuasiCompact f] [IsDominant f] [IsReduced Y]
    (h : GeometricallyIntegral (f ≫ g)) : GeometricallyIntegral g := by
  let : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant f
  exact h.of_comp_of_isSchemeTheoreticallyDominant f g hk

/-- Geometric integrality of the generic fiber descends through a
quasicompact scheme-theoretically dominant morphism. -/
lemma GeometricallyIntegral.genericFiber_of_comp_of_isSchemeTheoreticallyDominant
    {X Y S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [QuasiCompact f] [IsSchemeTheoreticallyDominant f]
    (h : GeometricallyIntegral
      ((f ≫ g).fiberToSpecResidueField (genericPoint S))) :
    GeometricallyIntegral
      (g.fiberToSpecResidueField (genericPoint S)) := by
  let r := S.fromSpecResidueField (genericPoint S)
  let : Flat r := S.flat_fromSpecResidueField_genericPoint
  let q : pullback f (pullback.fst g r) ⟶ pullback g r :=
    pullback.snd f (pullback.fst g r)
  let : IsSchemeTheoreticallyDominant q := inferInstance
  let : QuasiCompact q := inferInstance
  apply GeometricallyIntegral.of_comp_of_isSchemeTheoreticallyDominant
    q (g.fiberToSpecResidueField (genericPoint S))
      (Field.toIsField (S.residueField (genericPoint S)))
  let e := pullbackRightPullbackFstIso g r f
  let : MorphismProperty.RespectsIso
      (@GeometricallyIntegral : MorphismProperty Scheme.{u}) := by
    rw [GeometricallyIntegral.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_respectsIso _
  have he : GeometricallyIntegral
      (e.hom ≫ (f ≫ g).fiberToSpecResidueField (genericPoint S)) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyIntegral : MorphismProperty Scheme.{u})
      e.hom _).mpr h
  simpa only [Scheme.Hom.fiberToSpecResidueField, e, q, r,
    pullbackRightPullbackFstIso_hom_snd] using he

/-- Geometric integrality of the generic fiber descends through a
quasicompact dominant morphism with reduced target. -/
lemma GeometricallyIntegral.genericFiber_of_comp_of_isDominant
    {X Y S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [QuasiCompact f] [IsDominant f] [IsReduced Y]
    (h : GeometricallyIntegral
      ((f ≫ g).fiberToSpecResidueField (genericPoint S))) :
    GeometricallyIntegral
      (g.fiberToSpecResidueField (genericPoint S)) := by
  let : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant f
  exact h.genericFiber_of_comp_of_isSchemeTheoreticallyDominant f g

end AlgebraicGeometry
