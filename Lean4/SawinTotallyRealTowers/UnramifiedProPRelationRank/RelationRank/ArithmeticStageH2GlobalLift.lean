/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.CyclotomicAbsoluteH2Vanishing
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2LocalRamificationCharacter
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteDiscreteRamificationSupport

set_option autoImplicit false
/-!
# Actual global lifts and their finite ramification defect

The proved vanishing of absolute inflation supplies an actual continuous
global solution of every finite arithmetic-stage central embedding problem.
Restricting it to decomposition groups and subtracting the constructed
unramified local solution produces local characters. Their inertia parts
are supported on a finite set, by the open-kernel fixed-field argument.

The local difference character, its inertia restriction, and the finite
set are explicit chosen objects with proved projection and support laws.
Only one local compactness proof is introduced; all algebra structures
and finite-stage certificates are inherited from the existing sources.
-/

open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open ClassFieldTower.Cohomology ClassFieldTower.Martinet ClassFieldTower.ProP
open ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))
variable (xU : continuousCohomologyZModPLifted (n : ℕ)
  (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ) ⧸
    (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))) 2)

/-- Actual absolute restriction to the finite open-normal quotient. -/
def arithmeticStageAbsoluteQuotientMap :
    Field.absoluteGaloisGroup F →ₜ*
      (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ) ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))) :=
  (quotientProjection (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))).comp
    (absoluteToMaxEverywhereUnramifiedProP F (n : ℕ))

include hpOdd

/-- Every finite arithmetic-stage cocycle extension has a global solution. -/
theorem arithmeticStageH2_exists_absoluteGlobalLift :
    ∃ s : Field.absoluteGaloisGroup F →ₜ* DegreeTwoCentralExtension xU,
      (H2CocycleExtension.projection (degreeTwoCocycleRepresentative xU)).comp s =
        arithmeticStageAbsoluteQuotientMap F n U := by
  let : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F/F))
  apply H2CocycleExtension.exists_lift_of_restriction_eq_zero
    (arithmeticStageAbsoluteQuotientMap F n U) (degreeTwoCocycleRepresentative xU)
  rw [degreeTwoCocycleRepresentative_π]
  change (continuousCohomologyZModPMapLifted (n : ℕ)
    ((quotientProjection (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))).comp
      (absoluteToMaxEverywhereUnramifiedProP F (n : ℕ))) 2).hom xU = 0
  rw [continuousCohomologyZModPMapLifted_comp]
  exact openNormalQuotient_absoluteH2Inflation_eq_zero_of_odd F n hpOdd U xU

/-- A chosen actual global lift supplied by absolute degree-two vanishing. -/
def arithmeticStageH2AbsoluteGlobalLift :
    Field.absoluteGaloisGroup F →ₜ* DegreeTwoCentralExtension xU :=
  Classical.choose (arithmeticStageH2_exists_absoluteGlobalLift F n hpOdd U xU)

/-- The global lift has the required finite-stage projection. -/
theorem arithmeticStageH2AbsoluteGlobalLift_projection :
    (H2CocycleExtension.projection (degreeTwoCocycleRepresentative xU)).comp
      (arithmeticStageH2AbsoluteGlobalLift F n hpOdd U xU) =
        arithmeticStageAbsoluteQuotientMap F n U :=
  Classical.choose_spec (arithmeticStageH2_exists_absoluteGlobalLift F n hpOdd U xU)

/-- Restriction of the actual global lift to a finite decomposition group. -/
def arithmeticStageH2GlobalLiftAtFinitePlace
    (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceAbsoluteDecompositionGroup F v →ₜ* DegreeTwoCentralExtension xU :=
  (arithmeticStageH2AbsoluteGlobalLift F n hpOdd U xU).comp
    (finitePlaceAbsoluteDecompositionInclusion F v)

/-- The restricted global solution has the prescribed local projection. -/
theorem arithmeticStageH2GlobalLiftAtFinitePlace_projection
    (v : HeightOneSpectrum (𝓞 F)) :
    (H2CocycleExtension.projection (degreeTwoCocycleRepresentative xU)).comp
      (arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U xU v) =
        arithmeticStageFinitePlaceAbsoluteQuotientMap F (n : ℕ) U v := by
  ext sigma
  exact DFunLike.congr_fun
    (arithmeticStageH2AbsoluteGlobalLift_projection F n hpOdd U xU)
    (finitePlaceAbsoluteDecompositionInclusion F v sigma)

/-- The inertia character recording ramification of the chosen global lift. -/
def arithmeticStageH2GlobalRamificationCharacter
    (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceAbsoluteInertiaSubgroup F v →ₜ* Multiplicative (ZMod (n : ℕ)) :=
  arithmeticStageH2LocalRamificationCharacter F (n : ℕ) U xU v
    (arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U xU v)
    (arithmeticStageH2GlobalLiftAtFinitePlace_projection F n hpOdd U xU v)

/-- The actual global lift's inertia defect is supported at finitely many places. -/
theorem arithmeticStageH2GlobalRamificationCharacter_support_finite :
    {v : HeightOneSpectrum (𝓞 F) |
      arithmeticStageH2GlobalRamificationCharacter F n hpOdd U xU v ≠ 1}.Finite := by
  classical
  apply (absoluteDiscreteHom_inertia_support_finite F
    (arithmeticStageH2AbsoluteGlobalLift F n hpOdd U xU)).subset
  intro v hv
  by_contra h
  apply hv
  apply (arithmeticStageH2LocalRamificationCharacter_eq_one_iff F (n : ℕ) U xU v
    (arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U xU v)
    (arithmeticStageH2GlobalLiftAtFinitePlace_projection F n hpOdd U xU v)).2
  intro sigma hsigma
  exact not_not.mp (fun hne => h ⟨⟨sigma, hsigma⟩, hne⟩)

/-- A character on the full decomposition group extending the inertia defect. -/
def arithmeticStageH2GlobalLocalDifferenceCharacter
    (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceAbsoluteDecompositionGroup F v →ₜ* Multiplicative (ZMod (n : ℕ)) :=
  H2CocycleExtension.liftDifference (degreeTwoCocycleRepresentative xU)
    (arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U xU v)
    (arithmeticStageH2AbsoluteLocalLift F (n : ℕ) U xU v)
    ((arithmeticStageH2GlobalLiftAtFinitePlace_projection F n hpOdd U xU v).trans
      (arithmeticStageH2AbsoluteLocalLift_projection F (n : ℕ) U xU v).symm)

/-- Subtracting the unramified local lift gives the actual inertia defect. -/
theorem arithmeticStageH2GlobalLocalDifferenceCharacter_inertia
    (v : HeightOneSpectrum (𝓞 F)) :
    (arithmeticStageH2GlobalLocalDifferenceCharacter F n hpOdd U xU v).comp
      (finitePlaceAbsoluteInertiaInclusion F v) =
        arithmeticStageH2GlobalRamificationCharacter F n hpOdd U xU v := rfl

/-- The finite set of places with nontrivial inertia defect. -/
def arithmeticStageH2GlobalRamifiedPlaces : Finset (HeightOneSpectrum (𝓞 F)) :=
  (arithmeticStageH2GlobalRamificationCharacter_support_finite F n hpOdd U xU).toFinset

/-- Outside the named finite set, the inertia character is trivial. -/
theorem arithmeticStageH2GlobalRamificationCharacter_eq_one_of_not_mem
    (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ arithmeticStageH2GlobalRamifiedPlaces F n hpOdd U xU) :
    arithmeticStageH2GlobalRamificationCharacter F n hpOdd U xU v = 1 := by
  classical
  exact not_not.mp (fun h => hv (Set.Finite.mem_toFinset _ |>.2 h))

/-- The chosen global solution is unramified outside its named finite set. -/
theorem arithmeticStageH2GlobalLiftAtFinitePlace_inertia_le_ker_of_not_mem
    (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ arithmeticStageH2GlobalRamifiedPlaces F n hpOdd U xU) :
    finitePlaceAbsoluteInertiaSubgroup F v ≤
      (arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U xU v).toMonoidHom.ker :=
  (arithmeticStageH2LocalRamificationCharacter_eq_one_iff F (n : ℕ) U xU v
    (arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U xU v)
    (arithmeticStageH2GlobalLiftAtFinitePlace_projection F n hpOdd U xU v)).1
      (arithmeticStageH2GlobalRamificationCharacter_eq_one_of_not_mem F n hpOdd U xU v hv)

end ClassFieldTower.Martinet.Shafarevich
