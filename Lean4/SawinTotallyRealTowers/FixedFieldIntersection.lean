/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Order.GaloisConnection.Basic

set_option autoImplicit false

universe u v w
namespace ClassFieldTower.Sawin

/-- Intersecting closed Galois subgroups forms the compositum of their
fixed fields, without a finite-generation or normality assumption. -/
theorem fixedField_iInf_eq_iSup_of_isClosed
    (F : Type u) (Ω : Type v) [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    {ι : Sort w} (H : ι → Subgroup (Ω ≃ₐ[F] Ω))
    (hClosed : ∀ i : ι, IsClosed (H i : Set (Ω ≃ₐ[F] Ω))) :
    IntermediateField.fixedField (⨅ i : ι, H i) =
      ⨆ i : ι, IntermediateField.fixedField (H i) := by
  have hFix : (⨆ i : ι, IntermediateField.fixedField (H i)).fixingSubgroup =
      ⨅ i : ι, H i := by
    calc
      (⨆ i : ι, IntermediateField.fixedField (H i)).fixingSubgroup =
          ⨅ i : ι, (IntermediateField.fixedField (H i)).fixingSubgroup :=
        (InfiniteGalois.GaloisCoinsertionIntermediateFieldSubgroup (k := F) (K := Ω)).gc.l_iSup
      _ = ⨅ i : ι, H i := iInf_congr fun i ↦
        InfiniteGalois.fixingSubgroup_fixedField (⟨H i, hClosed i⟩ : ClosedSubgroup (Ω ≃ₐ[F] Ω))
  calc
    IntermediateField.fixedField (⨅ i : ι, H i) =
        IntermediateField.fixedField
          (⨆ i : ι, IntermediateField.fixedField (H i)).fixingSubgroup :=
      congrArg IntermediateField.fixedField hFix.symm
    _ = ⨆ i : ι, IntermediateField.fixedField (H i) :=
      InfiniteGalois.fixedField_fixingSubgroup _

end ClassFieldTower.Sawin
