/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Finiteness.Small
public import Nyll.ClassFieldTheory.Algebra.ShrinkFiniteExtension
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupRingEquiv
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkOpenSubgroups
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
public import Nyll.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocityQuotientEquivOfArtin

/-!
# The same local Artin map in independent field universes

The construction uses the original native local Artin map on the same two small field
representatives. The actual field equivalences transport its action, its norm kernel and its
normalization. No isomorphism of the Galois group is chosen from a norm-quotient existence theorem.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory.Universe

open LocalFieldTheory

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The continuous Artin map transported through the fixed field equivalences. -/
def abelianLocalArtinMap : Kˣ →ₜ* Gal(L/K) := by
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
  let eG : Gal(Shrink.{0} L / Shrink.{0} K) ≃ₜ* Gal(L/K) :=
    { HasseArf.shrinkGalMulEquiv K L with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  exact (ContinuousMonoidHom.toContinuousMonoidHom eG).comp
    ((_root_.LocalClassFieldTheory.abelianLocalArtinMap (Shrink.{0} K) (Shrink.{0} L)).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (shrinkUnitsContinuousMulEquiv K).symm))

/-- The same algebraic map, obtained by forgetting continuity. -/
def abelianLocalArtinMonoidHom : Kˣ →* Gal(L/K) :=
  (abelianLocalArtinMap K L).toMonoidHom

/-- The continuous and algebraic maps have the same values. -/
theorem abelianLocalArtinMap_toMonoidHom :
    (abelianLocalArtinMap K L).toMonoidHom = abelianLocalArtinMonoidHom K L := rfl

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
  change Shrink.ringEquiv L (_root_.LocalClassFieldTheory.abelianLocalArtinMap
    (Shrink.{0} K) (Shrink.{0} L) ((shrinkUnitsContinuousMulEquiv K).symm a)
      ((Shrink.ringEquiv L).symm (Shrink.ringEquiv L z))) = _
  rw [RingEquiv.symm_apply_apply]

/-- Transport of the actual native surjective map is surjective. -/
theorem abelianLocalArtinMap_surjective : Function.Surjective (abelianLocalArtinMap K L) := by
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
  exact (HasseArf.shrinkGalMulEquiv K L).surjective.comp
    ((_root_.LocalClassFieldTheory.abelianLocalArtinMap_surjective
      (Shrink.{0} K) (Shrink.{0} L)).comp (shrinkUnitsContinuousMulEquiv K).symm.surjective)

/-- The transported map has the original extension's field-norm kernel. -/
theorem abelianLocalArtinMap_ker :
    (abelianLocalArtinMap K L).toMonoidHom.ker = ClassFieldTheory.fieldNormSubgroup K L := by
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
  let eK := (Shrink.ringEquiv K).symm
  let eL := (Shrink.ringEquiv L).symm
  let eU := (shrinkUnitsContinuousMulEquiv K).symm
  let eG := HasseArf.shrinkGalMulEquiv K L
  have hn := ClassFieldTheory.fieldNormSubgroup_map_ringEquiv eK eL
    (HasseArf.shrinkAlgebra_commutes K L)
  have hker :
      (_root_.LocalClassFieldTheory.abelianLocalArtinMap
        (Shrink.{0} K) (Shrink.{0} L)).toMonoidHom.ker =
        ClassFieldTheory.fieldNormSubgroup (Shrink.{0} K) (Shrink.{0} L) :=
    _root_.LocalClassFieldTheory.abelianLocalArtinMap_ker (Shrink.{0} K) (Shrink.{0} L)
  ext a
  change eG (_root_.LocalClassFieldTheory.abelianLocalArtinMap
    (Shrink.{0} K) (Shrink.{0} L) (eU a)) = 1 ↔ a ∈ _
  rw [eG.map_eq_one_iff]
  change eU a ∈ (_root_.LocalClassFieldTheory.abelianLocalArtinMap
    (Shrink.{0} K) (Shrink.{0} L)).toMonoidHom.ker ↔ a ∈ _
  rw [hker, ← hn]
  constructor
  · rintro ⟨b, hb, heq⟩
    have hba : b = a := eU.injective heq
    exact hba ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- Forgetting continuity preserves the surjectivity of the same Artin map. -/
theorem abelianLocalArtinMonoidHom_surjective :
    Function.Surjective (abelianLocalArtinMonoidHom K L) :=
  abelianLocalArtinMap_surjective K L

/-- The algebraic Artin map has the actual local norm subgroup as its kernel. -/
theorem abelianLocalArtinMonoidHom_ker :
    (abelianLocalArtinMonoidHom K L).ker = LocalFieldTheory.localNormSubgroup K L :=
  abelianLocalArtinMap_ker K L

/-- The unique norm-quotient equivalence induced by this specified Artin map. -/
theorem quotientEquiv_existsUnique :
    ∃! e : ClassFieldTheory.FieldNormQuotient K L ≃ₜ* Gal(L/K),
      ∀ a : Kˣ, e (QuotientGroup.mk' (ClassFieldTheory.fieldNormSubgroup K L) a) =
        abelianLocalArtinMap K L a :=
  ClassFieldTheory.finiteAbelianLocalReciprocity_quotientEquiv_of_artin
    K L (abelianLocalArtinMap K L) (abelianLocalArtinMap_surjective K L)
      (abelianLocalArtinMap_ker K L)

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

/-- On native fields this is exactly the original named Artin map. -/
theorem abelianLocalArtinMap_eq_native
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    abelianLocalArtinMap K L = _root_.LocalClassFieldTheory.abelianLocalArtinMap K L := by
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
  apply ContinuousMonoidHom.ext
  intro a
  apply AlgEquiv.ext
  intro z
  apply (Shrink.ringEquiv L).symm.injective
  have hc (x : K) :
      (Shrink.ringEquiv L).symm (algebraMap K L x) =
        algebraMap (Shrink.{0} K) (Shrink.{0} L) ((Shrink.ringEquiv K).symm x) :=
    (congrArg (fun f : K →+* Shrink.{0} L => f x)
      (HasseArf.shrinkAlgebra_commutes K L)).symm
  have h := _root_.LocalClassFieldTheory.abelianLocalArtinMonoidHom_semilinear_action
    K (Shrink.{0} K) L (Shrink.{0} L) (Shrink.ringEquiv K).symm
      (Shrink.ringEquiv L).symm hc (shrink_semilinearValuationCompatible K) a z
  have hnative := _root_.LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom K L
  have hsmall := _root_.LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom
    (Shrink.{0} K) (Shrink.{0} L)
  rw [← hnative, ← hsmall] at h
  change (Shrink.ringEquiv L).symm
    (Shrink.ringEquiv L (_root_.LocalClassFieldTheory.abelianLocalArtinMap
      (Shrink.{0} K) (Shrink.{0} L) ((shrinkUnitsContinuousMulEquiv K).symm a)
        ((Shrink.ringEquiv L).symm z))) = _
  rw [RingEquiv.symm_apply_apply]
  exact h.symm

/-- On native fields, forgetting continuity also recovers the original named algebraic map. -/
theorem abelianLocalArtinMonoidHom_eq_native
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    abelianLocalArtinMonoidHom K L =
      _root_.LocalClassFieldTheory.abelianLocalArtinMonoidHom K L := by
  change (abelianLocalArtinMap K L).toMonoidHom = _
  rw [abelianLocalArtinMap_eq_native,
    _root_.LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom]

end LocalClassFieldTheory.Universe
