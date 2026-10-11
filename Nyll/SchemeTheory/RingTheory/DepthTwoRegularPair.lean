/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.LocalAlgebra
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular pairs in local rings of depth at least two
-/

open RingTheory IsLocalRing

namespace SchemeTheory

/-- Depth at least two supplies two elements of the maximal ideal that are
regular in either order. -/
theorem exists_regular_pair_of_two_le_depth
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdepth : (2 : ℕ∞) ≤ Module.depth R R) :
    ∃ x ∈ maximalIdeal R, ∃ y ∈ maximalIdeal R,
      Sequence.IsWeaklyRegular R [x, y] ∧ Sequence.IsWeaklyRegular R [y, x] := by
  have hpos : (1 : ℕ∞) < Module.depth R R := lt_of_lt_of_le (by norm_num) hdepth
  obtain ⟨_, ⟨s, hs, hmem, rfl⟩, hlen⟩ := lt_sSup_iff.mp hpos
  cases s with
  | nil => simp only [List.length_nil, Nat.cast_zero, not_lt_zero] at hlen
  | cons x s =>
    cases s with
    | nil => norm_num only [List.length_cons, List.length_nil] at hlen
    | cons y s =>
      have hxmem : x ∈ maximalIdeal R := hmem x (List.mem_cons_self)
      have hymem : y ∈ maximalIdeal R := hmem y (List.mem_cons_of_mem x List.mem_cons_self)
      have hxy : Sequence.IsWeaklyRegular R [x, y] := by
        obtain ⟨hx, hs⟩ := (Sequence.isWeaklyRegular_cons_iff R x (y :: s)).mp hs
        obtain ⟨hy, -⟩ := (Sequence.isWeaklyRegular_cons_iff (QuotSMulTop x R) y s).mp hs
        exact Sequence.IsWeaklyRegular.cons hx
          (Sequence.IsWeaklyRegular.cons hy (Sequence.IsWeaklyRegular.nil R _))
      refine ⟨x, hxmem, y, hymem, hxy, ?_⟩
      apply IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hxy
        (List.Perm.swap y x [])
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hxmem
      · exact (List.mem_singleton.mp hr) ▸ hymem

end SchemeTheory
