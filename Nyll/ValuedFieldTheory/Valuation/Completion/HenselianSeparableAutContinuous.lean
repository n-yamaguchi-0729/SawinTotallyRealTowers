/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianSeparableAutEquiv
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Continuity of restriction across Henselian completion

A finite separable intermediate field has a primitive element. The open
stabilizer of its image is sent into the subgroup fixing that intermediate
field, proving continuity for the Krull topologies at the identity.
-/

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

open scoped Topology

variable {K : Type*} [Field K] (base : HenselianDVF K)
  {S E : Type*} [Field S] [Field E] [Algebra K S]
  [Algebra base.valuation.Completion E] [Algebra K E]
  [IsScalarTower K base.valuation.Completion E] [Algebra.IsSeparable K S]
  [IsSepClosed S] [Algebra.IsSeparable base.valuation.Completion E]

/-- Restriction through the chosen embedding is continuous for the Krull
topologies on both automorphism groups. -/
theorem continuous_separableClosedAutEquiv_symm (i : S →ₐ[K] E) :
    Continuous (base.separableClosedAutEquiv i).symm := by
  apply continuous_of_tendsto_nhds_one (base.separableClosedAutEquiv i).symm
  rw [Filter.Tendsto]
  intro U hU
  obtain ⟨F, hF, hFU⟩ := (krullTopology_mem_nhds_one_iff K S U).mp hU
  let pb : PowerBasis K F := Field.powerBasisOfFiniteOfSeparable K F
  have hH : (MulAction.stabilizer (E ≃ₐ[base.valuation.Completion] E)
      (i (pb.gen : S)) : Set (E ≃ₐ[base.valuation.Completion] E)) ∈ 𝓝 1 :=
    (stabilizer_isOpen_of_isIntegral (K := base.valuation.Completion)
      (i (pb.gen : S))).mem_nhds (Subgroup.one_mem _)
  apply Filter.mem_of_superset hH
  intro σ hσ
  apply hFU
  have hgen : (base.separableClosedAutEquiv i).symm σ (pb.gen : S) = (pb.gen : S) := by
    apply i.injective
    change i ((base.separableClosedAutEquiv i).symm σ (pb.gen : S)) = i (pb.gen : S)
    rw [separableClosedAutEquiv_symm_apply]
    exact MulAction.mem_stabilizer_iff.mp hσ
  have hhom : ((base.separableClosedAutEquiv i).symm σ).toAlgHom.comp F.val = F.val :=
    pb.algHom_ext hgen
  apply (IntermediateField.mem_fixingSubgroup_iff F
    ((base.separableClosedAutEquiv i).symm σ)).mpr
  intro s hs
  exact congrArg (fun f : F →ₐ[K] S => f ⟨s, hs⟩) hhom

end ValuationTheory.DiscreteValuationField.HenselianDVF
