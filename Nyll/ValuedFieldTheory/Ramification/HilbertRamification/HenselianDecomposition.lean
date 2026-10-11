/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence
import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Decomposition over a Henselian valuation ring

Henselianity identifies the selected extension valuation ring with the
integral closure, so every base-field automorphism preserves it. Consequently
the fixed integers in the residue exact sequence over an intermediate field
come from that intermediate field's actual pulled-back valuation ring.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

open scoped Pointwise

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The decomposition group of an algebraic extension of a Henselian
valuation ring is the full automorphism group. -/
theorem decompositionGroup_eq_top_of_henselianRing
    [Algebra.IsAlgebraic K L]
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation] :
    decompositionGroup K A = ⊤ := by
  have hA : A.toSubring = (integralClosure V L).toSubring := by
    simpa only [_root_.ValuationSubring.valuationSubring_valuation] using
      ValuationTheory.Henselian.valuationSubring_eq_integralClosure_of_henselianRing
        V A.valuation
  have hmem (x : L) : x ∈ A ↔ IsIntegral V x := by
    change x ∈ A.toSubring ↔ IsIntegral V x
    rw [hA]
    exact mem_integralClosure_iff V L
  apply top_unique
  intro σ _hσ
  change σ • A = A
  apply SetLike.ext
  intro x
  rw [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  change σ⁻¹ x ∈ A ↔ x ∈ A
  rw [hmem, hmem]
  exact isIntegral_algEquiv ((σ⁻¹).restrictScalars V)

/-- Every fixed integer used in the residue exact sequence over an
intermediate field is the image of an integer in the actual comap valuation
ring. No normality or finiteness of the intermediate field is needed. -/
theorem exists_comap_integer_of_decompositionFixedSubring_of_henselianRing
    [IsGalois K L]
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation]
    (E : IntermediateField K L) (a : decompositionFixedSubring E A) :
    ∃ b : A.comap E.val.toRingHom, ((b : E) : L) = ((a : A) : L) := by
  have htop : decompositionGroup K A = ⊤ :=
    decompositionGroup_eq_top_of_henselianRing V A
  have hfixed : ∀ σ : L ≃ₐ[E] L, σ ((a : A) : L) = ((a : A) : L) := by
    intro σ
    have hσK : restrictAutomorphismScalars (K := K) (M := E) σ ∈
        decompositionGroup K A := by
      rw [htop]
      exact Subgroup.mem_top _
    have hσE : σ ∈ decompositionGroup E A :=
      (mem_decompositionGroup_restrictScalars_iff
        (K := K) (M := E) A σ).mp hσK
    exact congrArg (fun z : A => (z : L)) (a.property ⟨σ, hσE⟩)
  obtain ⟨b, hb⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := E) (K := L) ((a : A) : L)).mpr hfixed
  refine ⟨⟨b, ?_⟩, hb⟩
  change (b : L) ∈ A
  rw [show (b : L) = ((a : A) : L) from hb]
  exact (a : A).property

end RamificationTheory.HilbertRamification.ValuationSubring
