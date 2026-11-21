/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Finiteness.Small
public import Nyll.ClassFieldTheory.Algebra.ShrinkFiniteExtension
public import Nyll.ValuedFieldTheory.LocalField.NormUnitsBaseChange
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkOpenSubgroups
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
public import Nyll.ProCGroups.Topologies.QuotientMaps
public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormQuotient

/-!
# Local Artin comparison with compatible small fields

The semilinear comparison identifies the original Artin action on field elements with
the action on the chosen small fields.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory.Universe

open LocalFieldTheory

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Shrinking the base field preserves its supplied valuation relation. -/
theorem shrink_semilinearValuationCompatible :
    let : Small.{0} K := smallLocalField K
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    SemilinearValuationCompatible K (Shrink.{0} K) (Shrink.ringEquiv K).symm := by
  intro sharedSmall sharedValuation
  let : Algebra K (Shrink.{0} K) := (Shrink.ringEquiv K).symm.toRingHom.toAlgebra
  change (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation (Shrink.{0} K))
  constructor
  rw [Valuation.isEquiv_iff_val_le_one]
  intro a
  let w := shrinkLocalFieldValuation K
  have hw : (ValuativeRel.valuation (Shrink.{0} K)).IsEquiv w :=
    let : w.Compatible := Valuation.Compatible.ofValuation w
    ValuativeRel.isEquiv _ _
  change ValuativeRel.valuation K a ≤ 1 ↔
    ValuativeRel.valuation (Shrink.{0} K) ((Shrink.ringEquiv K).symm a) ≤ 1
  rw [hw.le_one_iff_le_one]
  change ValuativeRel.valuation K a ≤ 1 ↔
    ValuativeRel.valuation K (Shrink.ringEquiv K ((Shrink.ringEquiv K).symm a)) ≤ 1
  rw [RingEquiv.apply_symm_apply]

/-- Evaluation uses the actual native Artin action through the same two field equivalences. -/
theorem abelianLocalArtinMap_apply_shrink :
    let : Small.{0} K := smallLocalField K
    let : Small.{0} L := Module.Finite.small K L
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := HasseArf.shrinkAlgebra K L
    let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
      HasseArf.shrink_finiteDimensional K L
    let : IsAbelianGalois (Shrink.{0} K) (Shrink.{0} L) :=
      HasseArf.shrink_isAbelianGalois K L
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    let : IsNonarchimedeanLocalField (Shrink.{0} K) :=
      shrinkLocalField_isNonarchimedeanLocalField K
    ∀ (a : Kˣ) (z : Shrink.{0} L),
      abelianLocalArtinMap K L a (Shrink.ringEquiv L z) =
        Shrink.ringEquiv L (_root_.LocalClassFieldTheory.abelianLocalArtinMap
          (Shrink.{0} K) (Shrink.{0} L) ((shrinkUnitsContinuousMulEquiv K).symm a) z) := by
  intro sharedSmallK sharedSmallL sharedAlgebra sharedFinite sharedGalois sharedValuation
    sharedLocal a z
  let eK := (Shrink.ringEquiv K).symm
  let eL := (Shrink.ringEquiv L).symm
  have hc (x : K) :
      eL (algebraMap K L x) =
        algebraMap (Shrink.{0} K) (Shrink.{0} L) (eK x) :=
    (congrArg (fun f : K →+* Shrink.{0} L => f x)
      (HasseArf.shrinkAlgebra_commutes K L)).symm
  have h := _root_.LocalClassFieldTheory.abelianLocalArtinMonoidHom_semilinear_action
    K (Shrink.{0} K) L (Shrink.{0} L) eK eL hc
      (shrink_semilinearValuationCompatible K) a (Shrink.ringEquiv L z)
  rw [← _root_.LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom K L,
    ← _root_.LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom
      (Shrink.{0} K) (Shrink.{0} L)] at h
  apply eL.injective
  dsimp only [eL]
  rw [RingEquiv.symm_apply_apply]
  change eL (_root_.LocalClassFieldTheory.abelianLocalArtinMap K L a (Shrink.ringEquiv L z)) =
    _root_.LocalClassFieldTheory.abelianLocalArtinMap (Shrink.{0} K) (Shrink.{0} L)
      ((shrinkUnitsContinuousMulEquiv K).symm a) z
  change _ = _root_.LocalClassFieldTheory.abelianLocalArtinMap
    (Shrink.{0} K) (Shrink.{0} L) ((shrinkUnitsContinuousMulEquiv K).symm a)
      ((Shrink.ringEquiv L).symm (Shrink.ringEquiv L z)) at h
  rw [RingEquiv.symm_apply_apply] at h
  exact h

/-- Shrinking the coefficient and acting fields preserves the algebraic
Artin value under the same unit equivalence and Galois conjugation. -/
theorem abelianLocalArtinMonoidHom_apply_shrink :
    let : Small.{0} K := smallLocalField K
    let : Small.{0} L := Module.Finite.small K L
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := HasseArf.shrinkAlgebra K L
    let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
      HasseArf.shrink_finiteDimensional K L
    let : IsAbelianGalois (Shrink.{0} K) (Shrink.{0} L) :=
      HasseArf.shrink_isAbelianGalois K L
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    let : IsNonarchimedeanLocalField (Shrink.{0} K) :=
      shrinkLocalField_isNonarchimedeanLocalField K
    ∀ a : (Shrink.{0} K)ˣ,
      abelianLocalArtinMonoidHom K L (shrinkUnitsContinuousMulEquiv K a) =
        HasseArf.shrinkGalMulEquiv K L
          (abelianLocalArtinMonoidHom (Shrink.{0} K) (Shrink.{0} L) a) := by
  intro smallK smallL algebra finite galois valuation localField a
  rw [← abelianLocalArtinMap_toMonoidHom K L,
    ← abelianLocalArtinMap_toMonoidHom (Shrink.{0} K) (Shrink.{0} L)]
  apply AlgEquiv.ext
  intro x
  obtain ⟨z, rfl⟩ := (Shrink.ringEquiv L).surjective x
  change abelianLocalArtinMap K L (shrinkUnitsContinuousMulEquiv K a) (Shrink.ringEquiv L z) =
    HasseArf.shrinkGalEquiv K L (abelianLocalArtinMap (Shrink.{0} K) (Shrink.{0} L) a)
      (Shrink.ringEquiv L z)
  rw [abelianLocalArtinMap_apply_shrink, ContinuousMulEquiv.symm_apply_apply,
    HasseArf.shrinkGalEquiv_apply]

/-- The unique norm-quotient equivalence induced by this specified Artin map. -/
theorem quotientEquiv_existsUnique :
    ∃! e : ClassFieldTheory.FieldNormQuotient K L ≃ₜ* Gal(L/K),
      ∀ a : Kˣ, e (QuotientGroup.mk' (localNormSubgroup K L) a) =
        abelianLocalArtinMap K L a :=
  ProCGroups.QuotientGroup.existsUnique_quotientContinuousMulEquiv_of_surjective
    (abelianLocalArtinMap K L) (localNormSubgroup K L)
    (abelianLocalArtinMap_surjective K L) (abelianLocalArtinMap_ker K L)

end LocalClassFieldTheory.Universe
