/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFinrankTransfer
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteExtensionClassFieldAxiom

/-!
# Finite local reciprocity: the normalized local valuation is Henselian

For a nonarchimedean local field, the normalized discrete valuation on the
base unit group satisfies the Henselian valuation condition.  The value group is the copy of
the ordinary integers in the profinite integers.  For every finite abstract
field, including a non-normal one, the image after the abstract norm is the
ordinary residue-degree multiple of that value group.
-/

@[expose] public section

namespace LocalClassFieldTheory

open ClassFormation LocalFieldTheory



noncomputable section

open scoped ValuativeRel

universe u

/-- **Finite local reciprocity.**  The normalized valuation of a nonarchimedean local
field, on the actual fixed coefficient group in its separable closure, is a
Henselian valuation relative to the residue Frobenius degree datum. -/
noncomputable def localHenselianValuation
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ValuationData (localResidueDatum K)
      (galoisAmbientUnitsRep K (SeparableClosure K)) := by
  refine
    { toAddMonoidHom := localBaseValuation K
      integers_mem := intToProCInteger_mem_localBaseValuation_range K
      canonical_value_quotient_bijective :=
        localCanonicalValueQuotientMap_bijective K
      norm_range := ?_ }
  intro F
  let H := F.field
  let := F.finite
  let E := abstractFixedField K (SeparableClosure K) H
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) H F.finite
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let : IsIntegralClosure 𝒪[E] 𝒪[K] E := localCompleteDVF_integerRing_isIntegralClosure K E
  rw [localResidueDatum_residueDegree_eq_residueFinrank K F]
  exact localBaseValuation_comp_normToBase_range_eq_residueFinrank K H

end
end LocalClassFieldTheory
