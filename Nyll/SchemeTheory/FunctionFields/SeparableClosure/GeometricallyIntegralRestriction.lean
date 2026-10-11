/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FunctionFields.SeparableClosure.SeparableClosureRestriction
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Geometrically integral field extensions and Galois restriction

A field extension `K / k` is regular in the geometric sense when
`Spec K → Spec k` is geometrically integral. This file derives the linear
disjointness with a separable closure directly from that geometric condition,
then obtains surjectivity of the corresponding restriction map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits IntermediateField
open AlgebraicGeometry

namespace EtaleFundamentalGroups

variable {k K Ω : Type u}
variable [Field k] [Field K] [Field Ω]
variable [Algebra k K] [Algebra K Ω] [Algebra k Ω]
variable [IsScalarTower k K Ω]

/-- A geometrically integral field extension is linearly disjoint from the
separable closure of its base inside any common overfield. -/
theorem separableClosure_linearDisjoint_of_geometricallyIntegral
    [GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))] :
    (separableClosure k Ω).LinearDisjoint K := by
  let S := separableClosure k Ω
  have hField : IsField (TensorProduct k K S) := by
    let f := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let g := Spec.map (CommRingCat.ofHom (algebraMap k S))
    let : IsIntegral (pullback f g) :=
      GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
    let : IsIntegral (Spec (.of (TensorProduct k K S))) :=
      IsIntegral.of_isIso (pullbackSpecIso k K S).hom
    have hDomain : IsDomain (TensorProduct k K S) :=
      (affine_isIntegral_iff (.of (TensorProduct k K S))).mp inferInstance
    exact Algebra.TensorProduct.isField_of_isAlgebraic k K S (.inr inferInstance)
  let iK : K →ₐ[k] Ω := IsScalarTower.toAlgHom k K Ω
  have hLD : iK.fieldRange.LinearDisjoint S.val.fieldRange :=
    IntermediateField.LinearDisjoint.of_isField' (K := Ω)
      hField iK S.val
  rw [IntermediateField.fieldRange_val] at hLD
  have hLD' : S.LinearDisjoint iK.fieldRange := hLD.symm
  rw [IntermediateField.linearDisjoint_iff'] at hLD'
  exact hLD'

/-- Restriction from a separable closure of a geometrically integral field
extension onto the separable closure of the base field is surjective. -/
theorem separableClosureRestriction_surjective_of_geometricallyIntegral
    [IsSepClosure K Ω]
    [GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))] :
    Function.Surjective
      (separableClosureRestriction (k := k) (K := K) (Ω := Ω)) :=
  separableClosureRestriction_surjective_of_linearDisjoint
    separableClosure_linearDisjoint_of_geometricallyIntegral

end EtaleFundamentalGroups
