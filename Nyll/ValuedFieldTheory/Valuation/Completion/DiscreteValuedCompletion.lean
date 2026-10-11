/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.WithValScalars
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import Nyll.ValuedFieldTheory.Valuation.ValuedAdicComplete
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Complete discrete valuations on the actual valued completion

The extended valuation has the same value group as the original valuation.
For any discretely valued field, the native completeness of the valued completion
therefore supplies a complete discrete valuation. The canonical field map
preserves valuation values and hence the residue characteristic.
-/

namespace ValuationTheory.DiscreteValuationField.Valuation

universe u v

private theorem completion_valueGroup_eq
    {K : Type u} [Field K] {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
    (val : _root_.Valuation K Γ) :
    MonoidWithZeroHom.valueGroup
        (.ofClass (Valued.v : _root_.Valuation val.Completion Γ)) =
      MonoidWithZeroHom.valueGroup (.ofClass val) := by
  change (Valued.v : _root_.Valuation val.Completion Γ).valueGroup = val.valueGroup
  rw [← WithVal.valueGroup_eq val]
  ext γ
  constructor
  · intro hγ
    apply MonoidWithZeroHom.mem_valueGroup
    have himg : (γ : Γ) ∈ Units.val ''
        MonoidWithZeroHom.valueGroup
          (.ofClass (Valued.v : _root_.Valuation val.Completion Γ)) :=
      ⟨γ, hγ, rfl⟩
    rw [MonoidWithZeroHom.valueGroup_eq_range] at himg
    obtain ⟨⟨x, hx⟩, _⟩ := himg
    obtain ⟨a, ha⟩ := Valued.exists_coe_eq_v (K := WithVal val) (Γ₀ := Γ) x
    exact ⟨a, (hx.symm.trans ha).symm⟩
  · intro hγ
    apply MonoidWithZeroHom.mem_valueGroup
    have himg : (γ : Γ) ∈ Units.val ''
        MonoidWithZeroHom.valueGroup
          (.ofClass (Valued.v : _root_.Valuation (WithVal val) Γ)) :=
      ⟨γ, hγ, rfl⟩
    rw [MonoidWithZeroHom.valueGroup_eq_range] at himg
    obtain ⟨⟨a, ha⟩, _⟩ := himg
    refine ⟨(a : val.Completion), ?_⟩
    change (Valued.v : _root_.Valuation val.Completion Γ)
      (a : val.Completion) = (γ : Γ)
    rw [Valued.valuedCompletion_apply]
    exact ha

variable {K : Type u} [Field K] {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]

/-- The canonical valuation on the completion preserves the original values
along the existing ground-field algebra map. -/
theorem completion_valuation_algebraMap
    (val : _root_.Valuation K Γ) (x : K) :
    (Valued.v : _root_.Valuation val.Completion Γ)
      (algebraMap K val.Completion x) = val x := by
  change (Valued.v : _root_.Valuation val.Completion Γ)
    ((WithVal.toVal val x : WithVal val) : val.Completion) = val x
  exact Valued.valuedCompletion_apply (WithVal.toVal val x)

/-- Completion preserves rank-one discreteness; the generator remains a
generator because the value group is unchanged. -/
theorem completion_isRankOneDiscrete
    (val : _root_.Valuation K Γ) [val.IsRankOneDiscrete] :
    (Valued.v : _root_.Valuation val.Completion
      Γ).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    refine ⟨_root_.Valuation.IsRankOneDiscrete.generator val, ?_,
      _root_.Valuation.IsRankOneDiscrete.generator_lt_one val⟩
    exact (_root_.Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup val).trans
      (completion_valueGroup_eq val).symm

/-- The actual completion of a discretely valued field is complete discrete.
Adic completeness is generated from its native valued-field completeness. -/
theorem completion_isCompleteDiscrete
    (val : _root_.Valuation K Γ) [val.IsRankOneDiscrete] :
    IsCompleteDiscrete (Valued.v : _root_.Valuation val.Completion
      Γ) := by
  have : (Valued.v : _root_.Valuation val.Completion
      Γ).IsRankOneDiscrete :=
    completion_isRankOneDiscrete val
  exact (ValuationTheory.Valuations.completeDVFOfCompleteValuedField
    (K := val.Completion) (Gamma := Γ)).instCompleteDiscrete

/-- The canonical completion valuation actually extends the original valuation. -/
theorem completion_hasExtension
    (val : _root_.Valuation K Γ) :
    val.HasExtension (Valued.v : _root_.Valuation val.Completion
      Γ) := by
  refine ⟨?_⟩
  intro x y
  change val x ≤ val y ↔
    (Valued.v : _root_.Valuation val.Completion Γ)
        (algebraMap K val.Completion x) ≤
      (Valued.v : _root_.Valuation val.Completion Γ)
        (algebraMap K val.Completion y)
  rw [completion_valuation_algebraMap, completion_valuation_algebraMap]

/-- Completion preserves residue characteristic through the induced residue
field embedding, with no residue-field comparison assumed as input. -/
theorem completion_residueChar
    (val : _root_.Valuation K Γ) (p : ℕ)
    [hres : CharP (IsLocalRing.ResidueField val.valuationSubring) p] :
    CharP (IsLocalRing.ResidueField
      (Valued.v : _root_.Valuation val.Completion
        Γ).valuationSubring) p := by
  have : val.HasExtension (Valued.v : _root_.Valuation val.Completion
      Γ) := completion_hasExtension val
  exact (Algebra.charP_iff (IsLocalRing.ResidueField val.valuationSubring)
    (IsLocalRing.ResidueField (Valued.v : _root_.Valuation val.Completion
      Γ).valuationSubring) p).mp hres

end ValuationTheory.DiscreteValuationField.Valuation
