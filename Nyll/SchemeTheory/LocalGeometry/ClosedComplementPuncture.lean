/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.Inseparable

/-!
# Stalk punctures when the open complement consists of closed points

Every generization of a missing point, other than that point itself,
lies in the original open. Its pullback to the actual local spectrum is
therefore the punctured spectrum, without finiteness assumptions on X.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Closedness of every missing point identifies the actual stalk pullback
of the original open with the puncture. -/
theorem fromSpecStalk_preimage_open_eq_puncturedSpectrumOpen_of_closed_complement
    {X : Scheme.{u}} (U : X.Opens)
    (hclosed : ∀ y : X, y ∉ U → IsClosed ({y} : Set X))
    (x : X) (hx : x ∉ U) :
    X.fromSpecStalk x ⁻¹ᵁ U = puncturedSpectrumOpen (X.presheaf.stalk x) := by
  ext p
  change X.fromSpecStalk x p ∈ U ↔ p ≠ IsLocalRing.closedPoint (X.presheaf.stalk x)
  constructor
  · intro hp hpc
    rw [hpc, Scheme.fromSpecStalk_closedPoint] at hp
    exact hx hp
  · intro hp
    by_contra hU
    have hyx : X.fromSpecStalk x p ⤳ x := by
      have hy : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hy
      exact hy
    have hxy : x = X.fromSpecStalk x p := by
      have hy := specializes_iff_mem_closure.mp hyx
      rw [(hclosed _ hU).closure_eq] at hy
      exact Set.mem_singleton_iff.mp hy
    apply hp
    apply (X.fromSpecStalk x).isEmbedding.injective
    exact hxy.symm.trans Scheme.fromSpecStalk_closedPoint.symm

/-- The native pullback over any closed complement point is the punctured
actual local spectrum. -/
def closedComplementPuncturedSpectrumPullbackIso
    {X : Scheme.{u}} (U : X.Opens)
    (hclosed : ∀ y : X, y ∉ U → IsClosed ({y} : Set X))
    (x : X) (hx : x ∉ U) :
    pullback (X.fromSpecStalk x) U.ι ≅
      puncturedSpectrum (X.presheaf.stalk x) :=
  pullbackRestrictIsoRestrict (X.fromSpecStalk x) U ≪≫
    (Spec (X.presheaf.stalk x)).isoOfEq
      (fromSpecStalk_preimage_open_eq_puncturedSpectrumOpen_of_closed_complement U hclosed x hx)

/-- The comparison retains the original map to the full stalk spectrum. -/
@[reassoc]
theorem closedComplementPuncturedSpectrumPullbackIso_hom_inclusion
    {X : Scheme.{u}} (U : X.Opens)
    (hclosed : ∀ y : X, y ∉ U → IsClosed ({y} : Set X))
    (x : X) (hx : x ∉ U) :
    (closedComplementPuncturedSpectrumPullbackIso U hclosed x hx).hom ≫
        puncturedSpectrumInclusion (X.presheaf.stalk x) =
      pullback.fst (X.fromSpecStalk x) U.ι := by
  change ((pullbackRestrictIsoRestrict (X.fromSpecStalk x) U).hom ≫
    ((Spec (X.presheaf.stalk x)).isoOfEq
      (fromSpecStalk_preimage_open_eq_puncturedSpectrumOpen_of_closed_complement
        U hclosed x hx)).hom) ≫
      (puncturedSpectrumOpen (X.presheaf.stalk x)).ι = _
  have he : ((Spec (X.presheaf.stalk x)).isoOfEq
        (fromSpecStalk_preimage_open_eq_puncturedSpectrumOpen_of_closed_complement
        U hclosed x hx)).hom ≫
      (puncturedSpectrumOpen (X.presheaf.stalk x)).ι =
      (X.fromSpecStalk x ⁻¹ᵁ U).ι :=
    (Spec (X.presheaf.stalk x)).isoOfEq_hom_ι
      (fromSpecStalk_preimage_open_eq_puncturedSpectrumOpen_of_closed_complement U hclosed x hx)
  rw [Category.assoc]
  exact (congrArg
    (fun z : (X.fromSpecStalk x ⁻¹ᵁ U).toScheme ⟶ Spec (X.presheaf.stalk x) =>
      (pullbackRestrictIsoRestrict (X.fromSpecStalk x) U).hom ≫ z) he).trans
    (pullbackRestrictIsoRestrict_hom_ι (X.fromSpecStalk x) U)

end AlgebraicGeometry.Scheme
