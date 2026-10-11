/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.Sober

/-!+# The stalk puncture at a generic point of an open complement

At a generic point of an irreducible component of the complement of an
open subscheme, the pullback of the open to the actual stalk spectrum is
exactly the puncture. This supplies the local identification used in the
Noetherian induction of Stacks 0BQF. No ring Noetherianity is required.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A generic point of a complement component has no other complement
points among its generizations, so the stalk inverse image is the puncture. -/
theorem fromSpecStalk_preimage_open_eq_puncturedSpectrumOpen
    {X : Scheme.{u}} (U : X.Opens)
    (x : genericPoints {z : X // z ∉ U}) :
    X.fromSpecStalk x.1.1 ⁻¹ᵁ U = puncturedSpectrumOpen (X.presheaf.stalk x.1.1) := by
  ext p
  change X.fromSpecStalk x.1.1 p ∈ U ↔
    p ≠ IsLocalRing.closedPoint (X.presheaf.stalk x.1.1)
  constructor
  · intro hp hpc
    rw [hpc, Scheme.fromSpecStalk_closedPoint] at hp
    exact x.1.2 hp
  · intro hp
    by_contra hU
    let y : {z : X // z ∉ U} := ⟨X.fromSpecStalk x.1.1 p, hU⟩
    have hyx : y ⤳ x.1 := by
      apply (subtype_specializes_iff y x.1).mpr
      have hy : X.fromSpecStalk x.1.1 p ∈ Set.range (X.fromSpecStalk x.1.1) :=
        ⟨p, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hy
      exact hy
    have hxy : x.1 ⤳ y := by
      apply specializes_iff_closure_subset.mpr
      exact x.2.2 isIrreducible_singleton.closure hyx.closure_subset
    have hy : y = x.1 := (hyx.antisymm hxy).eq
    apply hp
    apply (X.fromSpecStalk x.1.1).isEmbedding.injective
    exact (congrArg Subtype.val hy).trans Scheme.fromSpecStalk_closedPoint.symm

/-- The native pullback over a generic complement point is the punctured
actual local spectrum. -/
def genericComplementPuncturedSpectrumPullbackIso
    {X : Scheme.{u}} (U : X.Opens)
    (x : genericPoints {z : X // z ∉ U}) :
    pullback (X.fromSpecStalk x.1.1) U.ι ≅
      puncturedSpectrum (X.presheaf.stalk x.1.1) :=
  pullbackRestrictIsoRestrict (X.fromSpecStalk x.1.1) U ≪≫
    (Spec (X.presheaf.stalk x.1.1)).isoOfEq
      (fromSpecStalk_preimage_open_eq_puncturedSpectrumOpen U x)

/-- The comparison retains the original map to the full stalk spectrum. -/
@[reassoc]
theorem genericComplementPuncturedSpectrumPullbackIso_hom_inclusion
    {X : Scheme.{u}} (U : X.Opens)
    (x : genericPoints {z : X // z ∉ U}) :
    (genericComplementPuncturedSpectrumPullbackIso U x).hom ≫
        puncturedSpectrumInclusion (X.presheaf.stalk x.1.1) =
      pullback.fst (X.fromSpecStalk x.1.1) U.ι := by
  change ((pullbackRestrictIsoRestrict (X.fromSpecStalk x.1.1) U).hom ≫
    ((Spec (X.presheaf.stalk x.1.1)).isoOfEq
      (fromSpecStalk_preimage_open_eq_puncturedSpectrumOpen U x)).hom) ≫
      (puncturedSpectrumOpen (X.presheaf.stalk x.1.1)).ι = _
  have he : ((Spec (X.presheaf.stalk x.1.1)).isoOfEq
        (fromSpecStalk_preimage_open_eq_puncturedSpectrumOpen U x)).hom ≫
      (puncturedSpectrumOpen (X.presheaf.stalk x.1.1)).ι =
      (X.fromSpecStalk x.1.1 ⁻¹ᵁ U).ι :=
    (Spec (X.presheaf.stalk x.1.1)).isoOfEq_hom_ι
      (fromSpecStalk_preimage_open_eq_puncturedSpectrumOpen U x)
  rw [Category.assoc]
  exact (congrArg
    (fun z : (X.fromSpecStalk x.1.1 ⁻¹ᵁ U).toScheme ⟶ Spec (X.presheaf.stalk x.1.1) =>
      (pullbackRestrictIsoRestrict (X.fromSpecStalk x.1.1) U).hom ≫ z) he).trans
    (pullbackRestrictIsoRestrict_hom_ι (X.fromSpecStalk x.1.1) U)

end AlgebraicGeometry.Scheme
