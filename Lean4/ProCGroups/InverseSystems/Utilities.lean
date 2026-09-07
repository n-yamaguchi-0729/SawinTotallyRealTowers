import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

/-!
# Order-theoretic utilities for inverse systems

The finite-upper-bound lemma in this module turns directedness of a preorder into a single stage
dominating any nonempty finite set of indices.  It is the common combinatorial step in
compactness, cofinality, and finite-coordinate arguments for inverse limits.
-/

namespace ProCGroups.InverseSystems

universe u

section

variable {I : Type u} [Preorder I]

/-- A finite subset of a directed preorder admits an upper bound. -/
theorem exists_upperBound_finset (hdir : Directed (· ≤ ·) (id : I → I)) :
    ∀ s : Finset I, s.Nonempty → ∃ j, ∀ i ∈ s, i ≤ j := by
  classical
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro hs
    rcases hs with ⟨i, hi⟩
    simp only [Finset.notMem_empty] at hi
  · intro a s ha ih hs
    by_cases hs' : s.Nonempty
    · rcases ih hs' with ⟨j, hj⟩
      rcases hdir a j with ⟨k, hak, hjk⟩
      refine ⟨k, ?_⟩
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hak
      · exact (hj i hi).trans hjk
    · have hs'' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst hs''
      refine ⟨a, ?_⟩
      intro i hi
      simp only [insert_empty_eq, Finset.mem_singleton] at hi
      simp only [hi, le_refl]

end

end ProCGroups.InverseSystems
