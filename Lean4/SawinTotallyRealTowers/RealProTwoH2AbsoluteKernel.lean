import SawinTotallyRealTowers.FiniteKummerContinuousKernel
import SawinTotallyRealTowers.RealProPOpenNormalStage
import SawinTotallyRealTowers.RealProPStageRestriction
import SawinTotallyRealTowers.RealCentralLiftCorrection
import SawinTotallyRealTowers.AbsoluteRealKernelField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
import SawinTotallyRealTowers.AbsoluteRealProPFactor
import SawinTotallyRealTowers.AbsoluteRealProPRestriction
import SawinTotallyRealTowers.AbsoluteRealProPUnramified
import SawinTotallyRealTowers.MaximalRealProPOutside
import GaloisCohomology.ProP.H2CocycleExtension
import GaloisCohomology.ProP.H2CocycleExtensionLinearLifts
import GaloisCohomology.ProP.H2CocycleExtensionPullback
import GaloisCohomology.ProP.H2CentralExtensionClass
import GaloisCohomology.ProP.TrivialZModP
import Mathlib.GroupTheory.PGroup
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Galois.Profinite

set_option autoImplicit false

/-!
# Descending absolute degree-two vanishing to the actual real pro-two group

An actual absolute cocycle lift is corrected at its finite ramification
support and at real conjugation. Its kernel field is an admissible finite
real two-extension, so the corrected lift factors through the constructed
maximal real pro-two compositum. Thus vanishing after absolute inflation
already implies vanishing after inflation into this maximal group.
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

open ClassFieldTower.Cohomology ClassFieldTower.ProP
open ClassFieldTower.Martinet.Shafarevich

/-- Every absolute solution of a finite two-group cocycle embedding problem
comes from an actual solution on the maximal real pro-two group. -/
theorem exists_maximalRealProTwo_cocycle_lift_of_absolute_lift
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hThree : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ T)
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (q : (maximalRealProPOutside 2 T ≃ₐ[ℚ] maximalRealProPOutside 2 T) →ₜ* Q)
    (z : trivialZModPCocyclesLifted 2 Q 2)
    (s : Field.absoluteGaloisGroup ℚ →ₜ* H2CocycleExtension z)
    (hs : (H2CocycleExtension.projection z).comp s =
      q.comp (absoluteToMaximalRealProPOutside 2 T)) :
    ∃ t : (maximalRealProPOutside 2 T ≃ₐ[ℚ] maximalRealProPOutside 2 T) →ₜ*
        H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp t = q := by
  obtain ⟨γ, hInertia, hReal⟩ := exists_character_corrected_absolute_cocycle_lift
    T hThree (q.comp (absoluteToMaximalRealProPOutside 2 T)) z s hs
    (by
      intro v hv σ
      change q (absoluteToMaximalRealProPOutside 2 T
        (finitePlaceAbsoluteDecompositionInclusion ℚ v σ.1)) = 1
      rw [absoluteToMaximalRealProPOutside_inertia 2 T v hv σ, map_one])
    (by
      change q (absoluteToMaximalRealProPOutside 2 T
        (absoluteInfinitePlaceArtinNegOne ℚ Rat.infinitePlace)) = 1
      rw [absoluteToMaximalRealProPOutside_infiniteArtin, map_one])
  obtain ⟨t, ht⟩ :=
    exists_maximalRealProPOutside_factor_of_inertia_and_infiniteArtin_trivial
      2 T (H2CocycleExtension.isPGroup z hQ)
      (H2CocycleExtension.twistByCharacter z s γ) hInertia hReal
  refine ⟨t, ?_⟩
  ext g
  obtain ⟨σ, rfl⟩ := absoluteToMaximalRealProPOutside_surjective 2 T g
  have htσ := DFunLike.congr_fun ht σ
  have hp := DFunLike.congr_fun
    ((H2CocycleExtension.twistByCharacter_projection z s γ).trans hs) σ
  exact (congrArg (H2CocycleExtension.projection z) htσ).trans hp

/-- At every actual finite two-group stage, the kernel of absolute inflation
is contained in the kernel of inflation to the maximal real pro-two group. -/
theorem maximalRealProTwo_H2_eq_zero_of_absolute_inflation_eq_zero
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hThree : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ T)
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (q : (maximalRealProPOutside 2 T ≃ₐ[ℚ] maximalRealProPOutside 2 T) →ₜ* Q)
    (x : continuousCohomologyZModPLifted 2 Q 2)
    (hx : (continuousCohomologyZModPMapLifted 2
      (q.comp (absoluteToMaximalRealProPOutside 2 T)) 2).hom x = 0) :
    (continuousCohomologyZModPMapLifted 2 q 2).hom x = 0 := by
  let : IsGalois ℚ (maximalRealProPOutside 2 T) :=
    maximalRealProPOutside_isGalois 2 T
  let z := degreeTwoCocycleRepresentative x
  obtain ⟨s, hs⟩ := H2CocycleExtension.exists_lift_of_restriction_eq_zero
    (q.comp (absoluteToMaximalRealProPOutside 2 T)) z
    (by simpa only [z, degreeTwoCocycleRepresentative_π] using hx)
  obtain ⟨t, ht⟩ :=
    exists_maximalRealProTwo_cocycle_lift_of_absolute_lift T hThree hQ q z s hs
  have h := H2CocycleExtension.restriction_eq_zero_of_lift q z t ht
  simpa only [z, degreeTwoCocycleRepresentative_π] using h

/-- The finite Kummer kernel dies under actual inflation from every constructed
arithmetic stage to the maximal real pro-two group. -/
theorem finiteKummerContinuousH2Map_ker_le_realProPStageInflation_ker
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hThree : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ T)
    (U : OpenNormalSubgroup
      (maximalRealProPOutside 2 T ≃ₐ[ℚ] maximalRealProPOutside 2 T))
    (hmu : (primitiveRoots 2 ℚ).Nonempty) :
    (finiteKummerContinuousH2Map ℚ (2 : ℕ+) (realProPOpenNormalStage 2 T U).val hmu).ker ≤
      (continuousCohomologyZModPMapLifted 2
        (realProPOpenNormalStageRestriction 2 T U) 2).hom.toLinearMap.toAddMonoidHom.ker := by
  intro x hx
  apply maximalRealProTwo_H2_eq_zero_of_absolute_inflation_eq_zero T hThree
    (realProPOpenNormalStage 2 T U).property.1
    (realProPOpenNormalStageRestriction 2 T U) x
  rw [realProPOpenNormalStageRestriction_comp_absolute]
  exact finiteKummerContinuousH2Map_ker_le_absoluteInflation_ker ℚ (2 : ℕ+)
    (realProPOpenNormalStage 2 T U).val hmu hx

end ClassFieldTower.Sawin
