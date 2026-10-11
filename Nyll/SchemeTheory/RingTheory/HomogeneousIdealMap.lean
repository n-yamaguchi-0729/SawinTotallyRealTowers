/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from the proof and theorem statement at pinned revision
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_HomogeneousIdeal_irrelevant_le_map_of_forall_le_span_image.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HomogeneousIdeal_irrelevant_le_map_of_forall_le_span_image.lean
Upstream NOTICE and per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for retained notices.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
# The irrelevant ideal under a graded map

Positive-degree spanning suffices for the irrelevant-ideal containment needed by Proj.
-/

universe u

/-- A degree-preserving map whose positive homogeneous images span the target sends the
irrelevant ideal onto an ideal containing the target irrelevant ideal. -/
theorem HomogeneousIdeal.irrelevant_le_map_of_forall_le_span_image
    {S : Type u} [CommRing S] {S' : Type u} [CommRing S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ϑ : R →+* R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hspan : ∀ n, 0 < n → 𝓡' n ≤ Submodule.span S' (ϑ '' (𝓡 n : Set R))) :
    HomogeneousIdeal.irrelevant 𝓡' ≤
      (HomogeneousIdeal.irrelevant 𝓡).map
        ({ ϑ with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') := by
  classical
  refine toIdeal_le_toIdeal_iff.mp fun x hx => ?_
  rw [HomogeneousIdeal.toIdeal_map]
  rw [← DirectSum.sum_support_decompose 𝓡' x]
  refine Ideal.sum_mem _ fun n _ => ?_
  by_cases h0 : n = 0
  · subst h0
    have h00 : (DirectSum.decompose 𝓡' x 0 : R') = 0 := by
      exact (HomogeneousIdeal.mem_irrelevant_iff 𝓡' x).mp hx
    rw [h00]
    exact Ideal.zero_mem _
  · have hmem : (DirectSum.decompose 𝓡' x n : R') ∈ Submodule.span S' (ϑ '' (𝓡 n : Set R)) :=
      hspan n (Nat.pos_of_ne_zero h0) (DirectSum.decompose 𝓡' x n).2
    have hT : ϑ '' (𝓡 n : Set R) ⊆
        ((((HomogeneousIdeal.irrelevant 𝓡).toIdeal.map
          ({ ϑ with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡')).restrictScalars S' :
            Submodule S' R') : Set R') := by
      rintro _ ⟨r, hr, rfl⟩
      exact Ideal.mem_map_of_mem _
        (HomogeneousIdeal.mem_irrelevant_of_mem 𝓡 (Nat.pos_of_ne_zero h0) hr)
    exact Submodule.span_le.mpr hT hmem
