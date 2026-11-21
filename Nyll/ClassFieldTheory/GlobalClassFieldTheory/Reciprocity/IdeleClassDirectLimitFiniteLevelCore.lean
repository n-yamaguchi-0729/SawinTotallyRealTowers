/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitCore
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimit
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteEmbedding
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm

/-!
# Finite levels of the rational idele-class direct limit

Normal closures, finite-level scalar extension, tower base change, and the
canonical embeddings into the rational idele-class direct limit.
-/



@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

attribute [local instance]
  relativeAdeleRingIntermediateAlgebra

/-- Absolute left cosets fixing a finite rational intermediate field,
identified with its embeddings into the canonical normal closure. -/
noncomputable def
    rationalBaseFixingCosetEquivNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    ((RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ))).toSubgroup ⧸
      extensionSubgroup
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)) ≃
      (K →ₐ[ℚ] finiteIdeleClassNormalClosure ℚ K) :=
  (LocalClassFieldTheory.baseFixingCosetEquivAlgHom
      ℚ (SeparableClosure ℚ) K).trans
    (normalClosure.algHomEquiv
      (F := ℚ) (K := K) (L := SeparableClosure ℚ)).symm

/-- The canonical map from the actual idele class group of a finite
rational intermediate field to the absolute idele-class direct limit. -/
noncomputable abbrev rationalIntermediateIdeleClassToDirectLimit
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    IdeleClassGroup K →* (ideleClassDirectLimit ℚ) :=
  intermediateIdeleClassToDirectLimit ℚ K

/-- Passing from the relative presentation of a finite rational
intermediate field to its ordinary idele class group commutes with the
canonical map to the absolute direct limit. -/
theorem
    rationalIntermediateIdeleClassToDirectLimit_baseChange
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    rationalIntermediateIdeleClassToDirectLimit K
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) c) =
      rationalRelativeIdeleClassToDirectLimit
        (finiteIdeleClassNormalClosure ℚ K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion
          (IntermediateField.le_normalClosure K)) c) := by
  let M : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
    finiteIdeleClassNormalClosure ℚ K
  let h : K ≤ M.toIntermediateField := IntermediateField.le_normalClosure K
  have hClass := rationalRelativeIdeleClassEquivStandard_embedding
    (E := K) (F := M.toIntermediateField) h c
  exact (congrArg (finiteIdeleClassToDirectLimit ℚ M) hClass).symm

/-- At a finite Galois rational intermediate field, the ordinary
idele-class comparison followed by the absolute direct-limit map is the
canonical finite-level map itself. -/
theorem
    rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    rationalIntermediateIdeleClassToDirectLimit
        (E : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) c) =
      rationalRelativeIdeleClassToDirectLimit E c := by
  rw [rationalIntermediateIdeleClassToDirectLimit_baseChange]
  exact rationalIdeleClassDirectLimit_mk_apply c
    (IntermediateField.le_normalClosure
      (E : IntermediateField ℚ (SeparableClosure ℚ)))

/-- The canonical maps from nested rational intermediate fields to the
idele-class direct limit agree after scalar extension. -/
theorem
    rationalIntermediateIdeleClassToDirectLimit_extension
    {F E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ E]
    (hFE : F ≤ E)
    (c : RelativeIdeleGroup.ClassGroup ℚ F) :
    rationalIntermediateIdeleClassToDirectLimit E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
            (IntermediateField.inclusion hFE) c)) =
      rationalIntermediateIdeleClassToDirectLimit F
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c) := by
  change intermediateIdeleClassToDirectLimit ℚ E
      (rationalRelativeIdeleClassEquivStandard E
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hFE) c)) =
    intermediateIdeleClassToDirectLimit ℚ F (rationalRelativeIdeleClassEquivStandard F c)
  rw [rationalRelativeIdeleClassEquivStandard_embedding]
  exact intermediateIdeleClassToDirectLimit_embedding ℚ hFE
    (rationalRelativeIdeleClassEquivStandard F c)

end Reciprocity
end GlobalClassFieldTheory
