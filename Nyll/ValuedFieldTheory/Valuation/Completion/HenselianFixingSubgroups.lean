/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianSeparableAutEquiv
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Fixing subgroups across Henselian completion

The field generated over the completion by the image of an intermediate
field has exactly the corresponding fixing subgroup. The equality is for
the actual constructed automorphism correspondence, and holds without
requiring the intermediate field to be finite or normal.
-/


namespace ValuationTheory.DiscreteValuationField.HenselianDVF

variable {K : Type*} [Field K] (base : HenselianDVF K)
  {S E : Type*} [Field S] [Field E] [Algebra K S]
  [Algebra base.valuation.Completion E] [Algebra K E]
  [IsScalarTower K base.valuation.Completion E] [Algebra.IsSeparable K S]
  [IsSepClosed S] [Algebra.IsSeparable base.valuation.Completion E]

/-- Fixing the completed image is equivalent to fixing the original
intermediate field under the actual completion correspondence. -/
theorem separableClosedAutEquiv_comap_fixingSubgroup
    (i : S →ₐ[K] E) (F : IntermediateField K S) :
    (IntermediateField.adjoin base.valuation.Completion (i '' (F : Set S))).fixingSubgroup.comap
      (base.separableClosedAutEquiv i).toMonoidHom = F.fixingSubgroup := by
  apply Subgroup.ext
  intro σ
  change (base.separableClosedAutEquiv i σ ∈
    (IntermediateField.adjoin base.valuation.Completion (i '' (F : Set S))).fixingSubgroup) ↔
      σ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  change (∀ x ∈ IntermediateField.adjoin base.valuation.Completion (i '' (F : Set S)),
    base.separableClosedAutEquiv i σ • x = x) ↔ ∀ s ∈ F, σ s = s
  rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  constructor
  · intro h s hs
    apply i.injective
    change i (σ s) = i s
    rw [← base.separableClosedAutEquiv_apply i σ s]
    exact h (i s) ⟨s, hs, rfl⟩
  · intro h x hx
    obtain ⟨s, hs, rfl⟩ := hx
    change base.separableClosedAutEquiv i σ (i s) = i s
    rw [separableClosedAutEquiv_apply, h s hs]

end ValuationTheory.DiscreteValuationField.HenselianDVF
