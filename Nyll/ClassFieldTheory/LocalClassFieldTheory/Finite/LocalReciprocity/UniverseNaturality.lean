/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin

/-!
# Naturality of the same Artin map in independent universes

Every field in a tower uses its fixed small representative. The three algebra maps are
transported simultaneously, so restriction is the original restriction of automorphisms.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory.Universe

open LocalFieldTheory

universe u v w x

/-- The specified Artin maps commute with the actual restriction in a finite abelian tower. -/
theorem abelianLocalArtinMonoidHom_restrict_tower
    (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L] :
    (AlgEquiv.restrictNormalHom E).comp (abelianLocalArtinMonoidHom K L) =
      abelianLocalArtinMonoidHom K E := by
  let : Small.{0} K := smallLocalField K
  let : Small.{0} E := Module.Finite.small K E
  let : Small.{0} L := Module.Finite.small K L
  let : Algebra (Shrink.{0} K) (Shrink.{0} E) := HasseArf.shrinkAlgebra K E
  let : Algebra (Shrink.{0} E) (Shrink.{0} L) := HasseArf.shrinkAlgebra E L
  let : Algebra (Shrink.{0} K) (Shrink.{0} L) := HasseArf.shrinkAlgebra K L
  let : IsScalarTower (Shrink.{0} K) (Shrink.{0} E) (Shrink.{0} L) :=
    HasseArf.shrink_isScalarTower K E L
  let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} E) :=
    HasseArf.shrink_finiteDimensional K E
  let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_finiteDimensional K L
  let : IsAbelianGalois (Shrink.{0} K) (Shrink.{0} E) :=
    HasseArf.shrink_isAbelianGalois K E
  let : IsAbelianGalois (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_isAbelianGalois K L
  let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
  let : IsNonarchimedeanLocalField (Shrink.{0} K) :=
    shrinkLocalField_isNonarchimedeanLocalField K
  apply MonoidHom.ext
  intro a
  let a₀ := (shrinkUnitsContinuousMulEquiv K).symm a
  have hsmall := DFunLike.congr_fun
    (_root_.LocalClassFieldTheory.abelianLocalArtinMonoidHom_restrict_tower
      (Shrink.{0} K) (Shrink.{0} E) (Shrink.{0} L)) a₀
  rw [← _root_.LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom,
    ← _root_.LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom] at hsmall
  change AlgEquiv.restrictNormalHom (Shrink.{0} E)
    (_root_.LocalClassFieldTheory.abelianLocalArtinMap (Shrink.{0} K) (Shrink.{0} L) a₀) =
      _root_.LocalClassFieldTheory.abelianLocalArtinMap (Shrink.{0} K) (Shrink.{0} E) a₀
    at hsmall
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (Shrink.ringEquiv E).surjective x
  apply (algebraMap E L).injective
  change algebraMap E L
      ((abelianLocalArtinMap K L a).restrictNormal E (Shrink.ringEquiv E y)) =
      algebraMap E L (abelianLocalArtinMap K E a (Shrink.ringEquiv E y))
  rw [AlgEquiv.restrictNormal_commutes, ← HasseArf.shrinkAlgebra_apply E L,
    abelianLocalArtinMap_apply_shrink K L, abelianLocalArtinMap_apply_shrink K E,
    ← HasseArf.shrinkAlgebra_apply E L]
  apply congrArg (Shrink.ringEquiv L)
  exact (AlgEquiv.restrictNormal_commutes
    (_root_.LocalClassFieldTheory.abelianLocalArtinMap (Shrink.{0} K) (Shrink.{0} L) a₀)
      (Shrink.{0} E) y).symm.trans
        (congrArg (fun σ : Gal(Shrink.{0} E / Shrink.{0} K) =>
          algebraMap (Shrink.{0} E) (Shrink.{0} L) (σ y)) hsmall)

/-- The specified continuous Artin maps commute with the existing restriction
between intermediate fields of the chosen separable closure. -/
theorem abelianLocalArtinMap_restrict
    (K : Type u) [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F] :
    (intermediateFieldRestrictContinuous K E F hEF).comp
        (abelianLocalArtinMap K F) =
      abelianLocalArtinMap K E := by
  let : Algebra E F :=
    RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  apply ContinuousMonoidHom.ext
  intro a
  change AlgEquiv.restrictNormalHom E (abelianLocalArtinMonoidHom K F a) =
    abelianLocalArtinMonoidHom K E a
  exact DFunLike.congr_fun (abelianLocalArtinMonoidHom_restrict_tower K E F) a

/-- The supplied valuation-extension relation survives the same two small field embeddings. -/
theorem shrink_valuationHasExtension
    (K : Type u) (E : Type v) [Field K] [Field E] [Algebra K E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E)] :
    let : Small.{0} K := smallLocalField K
    let : Small.{0} E := smallLocalField E
    let : Algebra (Shrink.{0} K) (Shrink.{0} E) := HasseArf.shrinkAlgebra K E
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    let : ValuativeRel (Shrink.{0} E) := shrinkLocalFieldValuativeRel E
    Valuation.HasExtension
      (ValuativeRel.valuation (Shrink.{0} K)) (ValuativeRel.valuation (Shrink.{0} E)) := by
  intro sharedSmallK sharedSmallE sharedAlgebra sharedValuationK sharedValuationE
  let wK := shrinkLocalFieldValuation K
  let wE := shrinkLocalFieldValuation E
  let : wK.HasExtension wE := hasExtension_comap_ringEquivs
    (Shrink.ringEquiv K) (Shrink.ringEquiv E) (HasseArf.shrinkAlgebra_apply K E)
      (ValuativeRel.valuation K) (ValuativeRel.valuation E)
  have hK : wK.IsEquiv (ValuativeRel.valuation (Shrink.{0} K)) :=
    let : wK.Compatible := Valuation.Compatible.ofValuation wK
    ValuativeRel.isEquiv _ _
  have hE : wE.IsEquiv (ValuativeRel.valuation (Shrink.{0} E)) :=
    let : wE.Compatible := Valuation.Compatible.ofValuation wE
    ValuativeRel.isEquiv _ _
  exact hasExtension_of_isEquiv wK (ValuativeRel.valuation (Shrink.{0} K))
    wE (ValuativeRel.valuation (Shrink.{0} E)) hK hE

/-- The original field norm commutes with the same continuous unit equivalences. -/
theorem normUnits_shrink
    (K : Type u) (E : Type v) [Field K] [Field E] [Algebra K E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [FiniteDimensional K E] :
    let : Small.{0} K := smallLocalField K
    let : Small.{0} E := smallLocalField E
    let : Algebra (Shrink.{0} K) (Shrink.{0} E) := HasseArf.shrinkAlgebra K E
    let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} E) :=
      HasseArf.shrink_finiteDimensional K E
    ∀ a : Eˣ,
      (shrinkUnitsContinuousMulEquiv K).symm (normUnits K E a) =
        normUnits (Shrink.{0} K) (Shrink.{0} E) ((shrinkUnitsContinuousMulEquiv E).symm a) := by
  intro sharedSmallK sharedSmallE sharedAlgebra sharedFinite a
  exact ClassFieldTheory.fieldNormHom_map_ringEquiv
    (Shrink.ringEquiv K).symm (Shrink.ringEquiv E).symm
      (HasseArf.shrinkAlgebra_commutes K E) a

/-- Norm and actual Galois restriction commute for the specified Artin maps in any universes. -/
theorem abelianLocalArtinMonoidHom_norm_restriction
    (K : Type u) (K' : Type v) (L : Type w) (L' : Type x)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K K'] [Algebra K L] [Algebra K L'] [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation K')]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L'] :
    ((AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)).comp
        (abelianLocalArtinMonoidHom K' L') =
      (abelianLocalArtinMonoidHom K L).comp (normUnits K K') := by
  let : Small.{0} K := smallLocalField K
  let : Small.{0} K' := smallLocalField K'
  let : Small.{0} L := Module.Finite.small K L
  let : Small.{0} L' := Module.Finite.small K' L'
  let : Algebra (Shrink.{0} K) (Shrink.{0} K') := HasseArf.shrinkAlgebra K K'
  let : Algebra (Shrink.{0} K) (Shrink.{0} L) := HasseArf.shrinkAlgebra K L
  let : Algebra (Shrink.{0} K) (Shrink.{0} L') := HasseArf.shrinkAlgebra K L'
  let : Algebra (Shrink.{0} K') (Shrink.{0} L') := HasseArf.shrinkAlgebra K' L'
  let : Algebra (Shrink.{0} L) (Shrink.{0} L') := HasseArf.shrinkAlgebra L L'
  let : IsScalarTower (Shrink.{0} K) (Shrink.{0} K') (Shrink.{0} L') :=
    HasseArf.shrink_isScalarTower K K' L'
  let : IsScalarTower (Shrink.{0} K) (Shrink.{0} L) (Shrink.{0} L') :=
    HasseArf.shrink_isScalarTower K L L'
  let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} K') :=
    HasseArf.shrink_finiteDimensional K K'
  let : Algebra.IsSeparable (Shrink.{0} K) (Shrink.{0} K') :=
    Algebra.IsSeparable.of_equiv_equiv (Shrink.ringEquiv K).symm
      (Shrink.ringEquiv K').symm (HasseArf.shrinkAlgebra_commutes K K')
  let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_finiteDimensional K L
  let : IsAbelianGalois (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_isAbelianGalois K L
  let : FiniteDimensional (Shrink.{0} K') (Shrink.{0} L') :=
    HasseArf.shrink_finiteDimensional K' L'
  let : IsAbelianGalois (Shrink.{0} K') (Shrink.{0} L') :=
    HasseArf.shrink_isAbelianGalois K' L'
  let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
  let : IsNonarchimedeanLocalField (Shrink.{0} K) :=
    shrinkLocalField_isNonarchimedeanLocalField K
  let : ValuativeRel (Shrink.{0} K') := shrinkLocalFieldValuativeRel K'
  let : IsNonarchimedeanLocalField (Shrink.{0} K') :=
    shrinkLocalField_isNonarchimedeanLocalField K'
  let : Valuation.HasExtension
      (ValuativeRel.valuation (Shrink.{0} K)) (ValuativeRel.valuation (Shrink.{0} K')) :=
    shrink_valuationHasExtension K K'
  apply MonoidHom.ext
  intro a
  let a₀ := (shrinkUnitsContinuousMulEquiv K').symm a
  have hsmall := DFunLike.congr_fun
    (_root_.LocalClassFieldTheory.abelianLocalArtinMonoidHom_norm_restriction
      (Shrink.{0} K) (Shrink.{0} K') (Shrink.{0} L) (Shrink.{0} L')) a₀
  rw [← _root_.LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom,
    ← _root_.LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom] at hsmall
  change AlgEquiv.restrictNormalHom (Shrink.{0} L)
    (AlgEquiv.restrictScalarsHom (Shrink.{0} K)
      (_root_.LocalClassFieldTheory.abelianLocalArtinMap (Shrink.{0} K') (Shrink.{0} L') a₀)) =
    _root_.LocalClassFieldTheory.abelianLocalArtinMap (Shrink.{0} K) (Shrink.{0} L)
      (normUnits (Shrink.{0} K) (Shrink.{0} K') a₀) at hsmall
  apply AlgEquiv.ext
  intro z
  obtain ⟨z₀, rfl⟩ := (Shrink.ringEquiv L).surjective z
  apply (algebraMap L L').injective
  change algebraMap L L'
      ((AlgEquiv.restrictScalarsHom K (abelianLocalArtinMap K' L' a)).restrictNormal L
        (Shrink.ringEquiv L z₀)) =
    algebraMap L L' (abelianLocalArtinMap K L (normUnits K K' a) (Shrink.ringEquiv L z₀))
  rw [AlgEquiv.restrictNormal_commutes]
  change abelianLocalArtinMap K' L' a (algebraMap L L' (Shrink.ringEquiv L z₀)) = _
  rw [← HasseArf.shrinkAlgebra_apply L L', abelianLocalArtinMap_apply_shrink K' L',
    abelianLocalArtinMap_apply_shrink K L, ← HasseArf.shrinkAlgebra_apply L L',
    normUnits_shrink K K' a]
  apply congrArg (Shrink.ringEquiv L')
  exact (AlgEquiv.restrictNormal_commutes
    (AlgEquiv.restrictScalarsHom (Shrink.{0} K)
      (_root_.LocalClassFieldTheory.abelianLocalArtinMap (Shrink.{0} K') (Shrink.{0} L') a₀))
        (Shrink.{0} L) z₀).symm.trans
          (congrArg (fun σ : Gal(Shrink.{0} L / Shrink.{0} K) =>
            algebraMap (Shrink.{0} L) (Shrink.{0} L') (σ z₀)) hsmall)

end LocalClassFieldTheory.Universe
