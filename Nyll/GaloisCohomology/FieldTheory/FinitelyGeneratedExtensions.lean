/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # Finite extensions of finitely generated fields -/

namespace FieldTheory
universe u v

/-- Finite extensions of finitely generated fields are finitely generated. -/
theorem fg_of_finiteDimensional
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hfg : Field.FG K) : Field.FG L := by
  classical
  obtain ⟨s, hs⟩ := hfg.finitely_generated
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_finiteType K L
  obtain ⟨t, ht⟩ := IntermediateField.fg_top K L
  let w : Finset L := s.image (algebraMap K L) ∪ t
  let S : Subfield L := Subfield.closure (w : Set L)
  have hbase : Set.range (algebraMap K L) ⊆ S := by
    have hle : (Subfield.closure (s : Set K)).map (algebraMap K L) ≤ S := by
      rw [RingHom.map_field_closure]
      apply Subfield.closure_le.mpr
      rintro x ⟨y, hy, rfl⟩
      apply Subfield.subset_closure
      exact Finset.mem_union_left t (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    rw [hs] at hle
    rintro x ⟨y, rfl⟩
    exact hle (Subfield.mem_map.mpr ⟨y, Subfield.mem_top y, rfl⟩)
  have htop : (IntermediateField.adjoin K (t : Set L)).toSubfield ≤ S := by
    rw [IntermediateField.adjoin_toSubfield]
    apply Subfield.closure_le.mpr
    apply Set.union_subset hbase
    intro x hx
    exact Subfield.subset_closure (Finset.mem_union_right _ hx)
  have hS : S = ⊤ := by
    rw [ht] at htop
    exact top_unique htop
  exact ⟨⟨w, hS⟩⟩

end FieldTheory
