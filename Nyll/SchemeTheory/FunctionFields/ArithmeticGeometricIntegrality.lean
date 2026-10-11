/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.PlainIntegerBase
import Nyll.SchemeTheory.Morphisms.SmoothGeometricallyIntegral
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleOverAlgebraicallyClosed
import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralFieldDescent
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Arithmetic geometric integrality from the function field

A field tensor product with the algebraic closure of the rationals makes the
corresponding base change of the generic point integral. Scheme-theoretic
dominance transports this to the whole scheme. Smoothness and field descent
then give geometric integrality of the arithmetic generic fiber.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem integral_pullback_algebraicClosure_of_functionField_tensor_isField
    {X : Scheme} [IsIntegral X] [CharZero X.functionField]
    (p : X ⟶ Spec (CommRingCat.of ℤ))
    (h : IsField (X.functionField ⊗[ℚ] AlgebraicClosure ℚ)) :
    IsIntegral (pullback p
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) := by
  let F := X.functionField
  let Ω := AlgebraicClosure ℚ
  let s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of ℤ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω))
  let j : Spec F ⟶ X := X.fromSpecStalk (genericPoint X)
  let : QuasiCompact j := ⟨fun U _ _ => (Set.toFinite (j ⁻¹' U)).isCompact⟩
  have hη : genericPoint X ∈ Set.range j := by
    rw [show Set.range j = {y | y ⤳ genericPoint X} from Scheme.range_fromSpecStalk]
    exact specializes_rfl
  let : IsDominant j := ⟨by
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← (genericPoint_spec X).def]
    exact closure_mono (Set.singleton_subset_iff.mpr hη)⟩
  let : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  let : Module.Flat ℤ Ω := Module.Flat.trans ℤ ℚ Ω
  let : Flat s := by
    rw [Flat.SpecMap_iff]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := Ω)).mpr inferInstance
  let P : Scheme := pullback p s
  let q : pullback j (pullback.fst p s) ⟶ P := pullback.snd j (pullback.fst p s)
  let : IsSchemeTheoreticallyDominant q := inferInstance
  let : Field (F ⊗[ℚ] Ω) := h.toField
  let e : F ⊗[ℚ] Ω ≃ₐ[ℚ] F ⊗[ℤ] Ω :=
    IsLocalization.algebraTensorEquiv (nonZeroDivisors ℤ) ℚ F Ω
  let : IsDomain (F ⊗[ℤ] Ω) := e.toRingEquiv.symm.toMulEquiv.isDomain _
  let : IsIntegral (Spec (CommRingCat.of (F ⊗[ℤ] Ω))) := inferInstance
  have hjp : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap ℤ F)) :=
    specZIsTerminal.hom_ext _ _
  let : IsIntegral (pullback (j ≫ p) s) := by
    rw [hjp]
    exact IsIntegral.of_isIso (pullbackSpecIso ℤ F Ω).inv
  let : IsIntegral (pullback j (pullback.fst p s)) :=
    IsIntegral.of_isIso (pullbackRightPullbackFstIso p s j).inv
  let : IrreducibleSpace P := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← q.denseRange.closure_eq]
    simpa only [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ (pullback j (pullback.fst p s) : Scheme)).image
        q q.continuous.continuousOn).closure
  let : IsReduced P := IsSchemeTheoreticallyDominant.isReduced q
  exact isIntegral_of_irreducibleSpace_of_isReduced P

/-- If the function field stays a field after tensoring with the algebraic
closure of the rationals, a smooth integral arithmetic scheme has a
geometrically integral generic fiber. -/
theorem geometricallyIntegral_arithmeticGenericFiber_of_functionField_tensor_isField
    {X : Scheme} [IsIntegral X] [CharZero X.functionField]
    (p : X ⟶ Spec (CommRingCat.of ℤ)) [Smooth p]
    (h : IsField (X.functionField ⊗[ℚ] AlgebraicClosure ℚ)) :
    GeometricallyIntegral
      (p.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of ℤ)))) := by
  let Ω := AlgebraicClosure ℚ
  let S := Spec (CommRingCat.of ℤ)
  let κ := S.residueField (genericPoint S)
  let s : Spec (CommRingCat.of Ω) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω))
  let P := pullback p s
  let g : P ⟶ Spec (CommRingCat.of Ω) := pullback.snd p s
  let : IsIntegral P := integral_pullback_algebraicClosure_of_functionField_tensor_isField p h
  let : GeometricallyIrreducible g :=
    GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed g
  let : GeometricallyConnected g := by
    constructor
    intro K _ y Y fst snd hpb
    let : IrreducibleSpace Y :=
      GeometricallyIrreducible.geometrically_irreducibleSpace (f := g) y fst snd hpb
    infer_instance
  let : GeometricallyIntegral g := Smooth.geometricallyIntegral_of_geometricallyConnected g
  let : Algebra κ Ω :=
    ((algebraMap ℚ Ω).comp specZGenericResidueFieldEquivQ.toRingHom).toAlgebra
  let t : Spec (CommRingCat.of Ω) ⟶ Spec κ :=
    Spec.map (CommRingCat.ofHom (algebraMap κ Ω))
  let r : Spec κ ⟶ S := S.fromSpecResidueField (genericPoint S)
  have htr : t ≫ r = s := specZIsTerminal.hom_ext _ _
  let l : P ⟶ pullback p r :=
    pullback.lift (pullback.fst p s) (g ≫ t) (by
      rw [Category.assoc, htr]
      exact pullback.condition)
  have hpb : IsPullback l g (pullback.snd p r) t := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p r) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p r)
    simpa only [l, pullback.lift_fst, htr] using
      (IsPullback.of_hasPullback p s)
  exact GeometricallyIntegral.of_isPullback_of_geometricallyIntegral (κ := κ) (k := Ω)
    (p.fiberToSpecResidueField (genericPoint S)) g l hpb

end AlgebraicGeometry
