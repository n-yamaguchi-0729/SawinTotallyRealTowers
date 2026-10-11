/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationGroup
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianDecomposition

/-!
# Ambient normality of inertia and ramification over a Henselian base

The defining principal-unit condition for ramification is preserved by
conjugation by every decomposition automorphism. Over a Henselian base,
decomposition is the full automorphism group, so both actual inertia and
actual ramification are normal subgroups of that group.
-/


namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Ramification, embedded in decomposition through inertia, is normal in
decomposition. No finiteness, algebraicity, or Henselianity is required. -/
theorem ramificationGroup_map_inertiaSubtype_normal
    (A : _root_.ValuationSubring L) :
    ((ramificationGroup K A).map (inertiaGroup K A).subtype).Normal := by
  refine ⟨?_⟩
  rintro σ ⟨s, hs, rfl⟩ τ
  have hconj : τ * (s : decompositionGroup K A) * τ⁻¹ ∈ inertiaGroup K A :=
    (inertiaGroup_normal (K := K) A).conj_mem s s.property τ
  refine ⟨⟨τ * (s : decompositionGroup K A) * τ⁻¹, hconj⟩, ?_, rfl⟩
  change ∀ x : Lˣ,
    automorphismUnitQuotient K A (τ * (s : decompositionGroup K A) * τ⁻¹) x ∈
      A.principalUnitGroup
  intro x
  have hquot :
      automorphismUnitQuotient K A (τ * (s : decompositionGroup K A) * τ⁻¹) x =
        Units.mapEquiv ((τ : L ≃ₐ[K] L).toMulEquiv)
          (automorphismUnitQuotient K A (s : decompositionGroup K A)
            (Units.mapEquiv ((τ⁻¹ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv x)) := by
    ext
    simp [automorphismUnitQuotient, div_eq_mul_inv, mul_assoc]
  rw [hquot]
  exact decompositionGroup_mapEquiv_mem_principalUnitGroup (K := K) A τ
    (hs (Units.mapEquiv ((τ⁻¹ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv x))

/-- Actual inertia is normal in the full automorphism group of an algebraic
extension of a Henselian valued field. -/
theorem inertiaGroupInAut_normal_of_henselianRing
    [Algebra.IsAlgebraic K L]
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation] :
    (inertiaGroupInAut K A).Normal := by
  have hsurj : Function.Surjective (decompositionGroup K A).subtype := by
    intro σ
    have hσ : σ ∈ decompositionGroup K A := by
      rw [decompositionGroup_eq_top_of_henselianRing V A]
      exact Subgroup.mem_top σ
    exact ⟨⟨σ, hσ⟩, rfl⟩
  exact (inertiaGroup_normal (K := K) A).map (decompositionGroup K A).subtype hsurj

/-- Actual ramification is normal in the full automorphism group of an
algebraic extension of a Henselian valued field. -/
theorem ramificationGroupInAut_normal_of_henselianRing
    [Algebra.IsAlgebraic K L]
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation] :
    (ramificationGroupInAut K A).Normal := by
  have hsurj : Function.Surjective (decompositionGroup K A).subtype := by
    intro σ
    have hσ : σ ∈ decompositionGroup K A := by
      rw [decompositionGroup_eq_top_of_henselianRing V A]
      exact Subgroup.mem_top σ
    exact ⟨⟨σ, hσ⟩, rfl⟩
  have h := (ramificationGroup_map_inertiaSubtype_normal K A).map
    (decompositionGroup K A).subtype hsurj
  simpa only [Subgroup.map_map, ramificationGroupInAut, inertiaGroupToAut] using h

end RamificationTheory.HilbertRamification.ValuationSubring
