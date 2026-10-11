/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianDecomposition
import Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction
import Nyll.ValuedFieldTheory.Valuation.UniqueRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Valuation.Extension

/-!
# Actual residue scalars in the Henselian decomposition sequence

The residue field of the fixed integer ring and the actual residue field of
an intermediate field have the same image in the selected residue field.
The comparison is proved on integer representatives. It does not assume
an identification of residue fields or separability of residue extensions.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The selected valuation extends the canonical valuation of its actual
pullback to an intermediate field. -/
theorem intermediateFieldComap_hasExtension
    (A : _root_.ValuationSubring L) (E : IntermediateField K L) :
    (A.comap E.val.toRingHom).valuation.HasExtension A.valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, _root_.Valuation.mem_integer_iff,
    _root_.ValuationSubring.valuation_le_one_iff, _root_.ValuationSubring.mem_comap]
  rfl

private theorem decompositionResidue_algebraMap_mk
    (A : _root_.ValuationSubring L) (E : IntermediateField K L)
    (a : decompositionFixedSubring E A) :
    algebraMap (decompositionResidueField E A) (selectedResidueField A)
        (Ideal.Quotient.mk (decompositionFixedMaximalIdeal E A) a) =
      IsLocalRing.residue A (a : A) :=
  Ideal.quotientMap_mk

/-- In the residue exact sequence over an intermediate field, the intrinsic
base scalars have exactly the image of the actual intermediate residue
field. Henselianity supplies the fixed-integer descent used in this comparison. -/
theorem decompositionResidue_scalar_range_eq_comap_residueMap_of_henselianRing
    [IsGalois K L]
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation]
    (E : IntermediateField K L) :
    Set.range (algebraMap (decompositionResidueField E A) (selectedResidueField A)) =
      Set.range (ValuationTheory.Valuations.residueFieldMapOfHasExtension
        (A.comap E.val.toRingHom) A (intermediateFieldComap_hasExtension A E)) := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, hb⟩ :=
      exists_comap_integer_of_decompositionFixedSubring_of_henselianRing V A E a
    refine ⟨IsLocalRing.residue (A.comap E.val.toRingHom) b, ?_⟩
    rw [AlgebraicNumberTheory.Valuations.residueFieldMapOfHasExtension_residue,
      decompositionResidue_algebraMap_mk]
    apply congrArg (IsLocalRing.residue A)
    apply Subtype.ext
    exact hb
  · rintro ⟨x, rfl⟩
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
    let a : A := ⟨((b : E) : L), b.property⟩
    have ha : a ∈ decompositionFixedSubring E A := by
      intro σ
      apply Subtype.ext
      change (σ : L ≃ₐ[E] L) (algebraMap E L (b : E)) =
        algebraMap E L (b : E)
      exact (σ : L ≃ₐ[E] L).commutes (b : E)
    refine ⟨Ideal.Quotient.mk (decompositionFixedMaximalIdeal E A) ⟨a, ha⟩, ?_⟩
    rw [decompositionResidue_algebraMap_mk,
      AlgebraicNumberTheory.Valuations.residueFieldMapOfHasExtension_residue]
    apply congrArg (IsLocalRing.residue A)
    apply Subtype.ext
    rfl

end RamificationTheory.HilbertRamification.ValuationSubring
