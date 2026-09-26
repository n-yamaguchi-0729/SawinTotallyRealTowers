/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Ramification.HilbertRamification.DecompositionField
import GaloisCohomology.ProP.H2CocycleExtension
import GaloisCohomology.ProP.QuotientRestriction
import GaloisCohomology.ProP.TrivialZModP
import GaloisCohomology.ProP.H2CocycleExtensionPullback
import GaloisCohomology.ProP.H2CocycleExtensionLinearLifts
import GaloisCohomology.ProP.H2CocycleExtensionLiftDifference
import SawinTotallyRealTowers.AbsoluteRealKernelField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
import SawinTotallyRealTowers.RealCharacterInertiaExistence
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteDiscreteRamificationSupport
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.FinitePlaceUnramifiedH2LocalizationVanishing
import ProCGroups.Topologies.QuotientMaps
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-!
# Removing unwanted inertia and real conjugation from cocycle lifts

Local unramified degree-two vanishing constructs the reference lifts. The
actual absolute lift has finite ramification support; its differences from
these reference lifts are genuine local characters. Prime three absorbs the
rational radical obstruction, and a global character corrects all outside
inertia and the real value without changing the projected homomorphism.
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

open ClassFieldTower.Cohomology ClassFieldTower.ProP
open ClassFieldTower.Martinet.Shafarevich ProCGroups

local instance realCentralLiftCanonicalZModAddCommGroup : AddCommGroup (ZMod 2) :=
  (ZMod.instField 2).toDivisionRing.toAddCommGroup

/-- The actual unramified local quotient supplies an inertia-trivial solution
of every cocycle embedding problem whose base map kills inertia. -/
theorem exists_inertia_trivial_local_cocycle_lift
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (v : HeightOneSpectrum (𝓞 F))
    (q : finitePlaceAbsoluteDecompositionGroup F v →ₜ* Q)
    (hI : finitePlaceAbsoluteInertiaSubgroup F v ≤ q.toMonoidHom.ker)
    (z : trivialZModPCocyclesLifted p Q 2) :
    ∃ t : finitePlaceAbsoluteDecompositionGroup F v →ₜ* H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp t = q ∧
      finitePlaceAbsoluteInertiaSubgroup F v ≤ t.toMonoidHom.ker := by
  let : CompactSpace (finitePlaceAbsoluteDecompositionGroup F v) :=
    isCompact_iff_compactSpace.mp
      (HilbertRamification.absoluteValueDecompositionGroup_isClosed
        F (finitePlaceAbsoluteValueExtension F v).1).isCompact
  let qbar := ProCGroups.QuotientGroup.liftₜ
    (finitePlaceAbsoluteInertiaSubgroup F v) q hI
  obtain ⟨t, ht⟩ := H2CocycleExtension.exists_lift_of_restriction_eq_zero qbar z
    (@Subsingleton.elim
      (continuousCohomologyZModPLifted p
        (finitePlaceAbsoluteDecompositionGroup F v ⧸
          finitePlaceAbsoluteInertiaSubgroup F v) 2)
      (finitePlaceUnramifiedQuotientH2_subsingleton F p v) _ _)
  refine ⟨t.comp (quotientProjection (finitePlaceAbsoluteInertiaSubgroup F v)), ?_, ?_⟩
  · ext σ
    exact DFunLike.congr_fun ht
      (quotientProjection (finitePlaceAbsoluteInertiaSubgroup F v) σ)
  · intro σ hσ
    change t (quotientProjection (finitePlaceAbsoluteInertiaSubgroup F v) σ) = 1
    rw [show quotientProjection (finitePlaceAbsoluteInertiaSubgroup F v) σ = 1 from
      (QuotientGroup.eq_one_iff (N := finitePlaceAbsoluteInertiaSubgroup F v) σ).mpr hσ,
      map_one]

private theorem twist_eq_one_at
    {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (z : trivialZModPCocyclesLifted 2 Q 2)
    (s : Field.absoluteGaloisGroup ℚ →ₜ* H2CocycleExtension z)
    (γ : Field.absoluteGaloisGroup ℚ →ₜ* Multiplicative (ZMod 2))
    (σ : Field.absoluteGaloisGroup ℚ)
    (hs : H2CocycleExtension.projection z (s σ) = 1)
    (hγ : γ σ = Multiplicative.ofAdd (s σ).left.down) :
    H2CocycleExtension.twistByCharacter z s γ σ = 1 := by
  apply H2CocycleExtension.ext
  · apply ULift.ext
    change (s σ).left.down - (γ σ).toAdd = 0
    rw [hγ]
    exact sub_self _
  · exact hs

/-- Finite ramification of an actual absolute lift permits a global character
correction killing all prescribed outside inertia and real conjugation. -/
theorem exists_character_corrected_absolute_cocycle_lift
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hThree : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ T)
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (q : Field.absoluteGaloisGroup ℚ →ₜ* Q)
    (z : trivialZModPCocyclesLifted 2 Q 2)
    (s : Field.absoluteGaloisGroup ℚ →ₜ* H2CocycleExtension z)
    (hs : (H2CocycleExtension.projection z).comp s = q)
    (hInertia : ∀ (v : HeightOneSpectrum (𝓞 ℚ)), v ∉ T →
      ∀ σ : finitePlaceAbsoluteInertiaSubgroup ℚ v,
        q (finitePlaceAbsoluteDecompositionInclusion ℚ v σ.1) = 1)
    (hReal : q (absoluteInfinitePlaceArtinNegOne ℚ Rat.infinitePlace) = 1) :
    ∃ γ : Field.absoluteGaloisGroup ℚ →ₜ* Multiplicative (ZMod 2),
      (∀ (v : HeightOneSpectrum (𝓞 ℚ)), v ∉ T →
        ∀ σ : finitePlaceAbsoluteInertiaSubgroup ℚ v,
          H2CocycleExtension.twistByCharacter z s γ
            (finitePlaceAbsoluteDecompositionInclusion ℚ v σ.1) = 1) ∧
      H2CocycleExtension.twistByCharacter z s γ
        (absoluteInfinitePlaceArtinNegOne ℚ Rat.infinitePlace) = 1 := by
  classical
  let : DiscreteTopology (H2CocycleExtension z) :=
    (H2CocycleExtension.toProdHomeomorph z).symm.discreteTopology
  have hFinite := absoluteDiscreteHom_inertia_support_finite ℚ s
  let S := hFinite.toFinset
  have hLocal (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ T) :
      ∃ t : finitePlaceAbsoluteDecompositionGroup ℚ v →ₜ* H2CocycleExtension z,
        (H2CocycleExtension.projection z).comp t =
          q.comp (finitePlaceAbsoluteDecompositionInclusion ℚ v) ∧
        finitePlaceAbsoluteInertiaSubgroup ℚ v ≤ t.toMonoidHom.ker := by
    apply exists_inertia_trivial_local_cocycle_lift ℚ 2 v
      (q.comp (finitePlaceAbsoluteDecompositionInclusion ℚ v)) _ z
    intro σ hσ
    exact hInertia v hv ⟨σ, hσ⟩
  let t (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ T) := (hLocal v hv).choose
  have ht (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ T) :=
    (hLocal v hv).choose_spec
  have hProjection (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ T) :
      (H2CocycleExtension.projection z).comp
        (s.comp (finitePlaceAbsoluteDecompositionInclusion ℚ v)) =
      (H2CocycleExtension.projection z).comp (t v hv) := by
    rw [(ht v hv).1]
    ext σ
    exact DFunLike.congr_fun hs (finitePlaceAbsoluteDecompositionInclusion ℚ v σ)
  let χ (v : ↥S) : finitePlaceAbsoluteDecompositionGroup ℚ v.1 →ₜ*
      Multiplicative (ZMod 2) :=
    if hv : v.1 ∉ T then
      H2CocycleExtension.liftDifference z
        (s.comp (finitePlaceAbsoluteDecompositionInclusion ℚ v.1))
        (t v.1 hv) (hProjection v.1 hv)
    else 1
  let ε := Multiplicative.ofAdd
    (s (absoluteInfinitePlaceArtinNegOne ℚ Rat.infinitePlace)).left.down
  obtain ⟨γ, hγReal, hγInside, hγOutside⟩ :=
    exists_absoluteCharacter_with_prescribed_inertia_and_real_value T hThree S χ ε
  refine ⟨γ, ?_, ?_⟩
  · intro v hv σ
    apply twist_eq_one_at z s γ _
    · exact (DFunLike.congr_fun hs _).trans (hInertia v hv σ)
    · by_cases hS : v ∈ S
      · have hc := hγInside ⟨v, hS⟩ hv σ
        dsimp only [χ] at hc
        rw [dite_eq_left hv] at hc
        change Multiplicative.ofAdd
          ((s (finitePlaceAbsoluteDecompositionInclusion ℚ v σ.1)).left.down -
            (t v hv σ.1).left.down) = _ at hc
        have htσ : t v hv σ.1 = 1 := (ht v hv).2 σ.property
        rw [htσ] at hc
        change Multiplicative.ofAdd
          ((s (finitePlaceAbsoluteDecompositionInclusion ℚ v σ.1)).left.down - 0) = _ at hc
        rw [sub_zero] at hc
        exact hc.symm
      · have hsσ : s (finitePlaceAbsoluteDecompositionInclusion ℚ v σ.1) = 1 := by
          by_contra hh
          exact hS (hFinite.mem_toFinset.mpr ⟨σ, hh⟩)
        rw [hsσ]
        exact hγOutside v hS hv σ
  · apply twist_eq_one_at z s γ _
    · exact (DFunLike.congr_fun hs _).trans hReal
    · exact hγReal Rat.infinitePlace

end ClassFieldTower.Sawin
