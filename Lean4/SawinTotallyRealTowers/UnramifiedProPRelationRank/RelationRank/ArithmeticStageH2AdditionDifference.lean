/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2RadicalFunctional
import GaloisCohomology.ProP.H2CocycleExtensionLinearLifts

set_option autoImplicit false
/-!
# The actual global character measuring nonadditivity of chosen lifts

Adding coefficient coordinates solves the embedding problem of the sum
class. Its difference from the chosen solution is a global character, and
all three lifts are unramified outside the fixed stage support. On inertia
this character is exactly the additivity defect of the local characters.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.ProP ClassFieldTower.Martinet ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))

local notation "StageQuotient" => MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ) ⧸
  (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))
variable (x y : continuousCohomologyZModPLifted (n : ℕ)
  (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ) ⧸
    (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))) 2)

include hpOdd x y

/-- A solution for the sum class, constructed by adding the two chosen solutions. -/
def arithmeticStageH2AbsoluteAddLift :
    Field.absoluteGaloisGroup F →ₜ* DegreeTwoCentralExtension (p := (n : ℕ))
      (Q := StageQuotient) (x + y) :=
  degreeTwoAddLift (p := (n : ℕ)) (Q := StageQuotient) x y
    (arithmeticStageH2AbsoluteGlobalLift F n hpOdd U x)
    (arithmeticStageH2AbsoluteGlobalLift F n hpOdd U y)
    ((arithmeticStageH2AbsoluteGlobalLift_projection F n hpOdd U x).trans
      (arithmeticStageH2AbsoluteGlobalLift_projection F n hpOdd U y).symm)

/-- The constructed sum lift has the same actual finite-stage projection. -/
theorem arithmeticStageH2AbsoluteAddLift_projection :
    (H2CocycleExtension.projection (degreeTwoCocycleRepresentative (p := (n : ℕ))
      (Q := StageQuotient) (x + y))).comp
      (arithmeticStageH2AbsoluteAddLift F n hpOdd U x y) =
        arithmeticStageAbsoluteQuotientMap F n U :=
  (degreeTwoAddLift_projection x y _ _ _).trans
    (arithmeticStageH2AbsoluteGlobalLift_projection F n hpOdd U x)

/-- The continuous absolute character measuring the chosen lifts' additivity defect. -/
def arithmeticStageH2AdditionDifference :
    Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod (n : ℕ)) :=
  H2CocycleExtension.liftDifference (degreeTwoCocycleRepresentative (x + y))
    (arithmeticStageH2AbsoluteGlobalLift F n hpOdd U (x + y))
    (arithmeticStageH2AbsoluteAddLift F n hpOdd U x y)
    ((arithmeticStageH2AbsoluteGlobalLift_projection F n hpOdd U (x + y)).trans
      (arithmeticStageH2AbsoluteAddLift_projection F n hpOdd U x y).symm)

/-- No new ramification is introduced outside the common finite support. -/
theorem arithmeticStageH2AdditionDifference_inertia_of_not_mem
    (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ arithmeticStageH2UniformRamifiedPlaces F n hpOdd U)
    (sigma : finitePlaceAbsoluteInertiaSubgroup F v) :
    arithmeticStageH2AdditionDifference F n hpOdd U x y
      (finitePlaceAbsoluteDecompositionInclusion F v sigma.1) = 1 := by
  have hxy := arithmeticStageH2GlobalLiftAtFinitePlace_inertia_le_ker_of_not_mem_uniform
    F n hpOdd U (x + y) v hv sigma.2
  have hx := arithmeticStageH2GlobalLiftAtFinitePlace_inertia_le_ker_of_not_mem_uniform
    F n hpOdd U x v hv sigma.2
  have hy := arithmeticStageH2GlobalLiftAtFinitePlace_inertia_le_ker_of_not_mem_uniform
    F n hpOdd U y v hv sigma.2
  change arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U (x + y) v sigma.1 = 1 at hxy
  change arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U x v sigma.1 = 1 at hx
  change arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U y v sigma.1 = 1 at hy
  change Multiplicative.ofAdd
    ((arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U (x + y) v sigma.1).left.down -
      ((arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U x v sigma.1).left.down +
        (arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U y v sigma.1).left.down)) = 1
  rw [hxy, hx, hy]
  change (0 : ZMod (n : ℕ)) - (0 + 0) = 0
  simp only [add_zero, sub_self]

/-- On inertia, the local additivity defect is the restriction of the actual global defect. -/
theorem arithmeticStageH2AdditionDifference_inertia
    (v : HeightOneSpectrum (𝓞 F)) (sigma : finitePlaceAbsoluteInertiaSubgroup F v) :
    (arithmeticStageH2GlobalLocalDifferenceCharacter F n hpOdd U (x + y) v sigma.1).toAdd -
      ((arithmeticStageH2GlobalLocalDifferenceCharacter F n hpOdd U x v sigma.1).toAdd +
        (arithmeticStageH2GlobalLocalDifferenceCharacter F n hpOdd U y v sigma.1).toAdd) =
      (arithmeticStageH2AdditionDifference F n hpOdd U x y
        (finitePlaceAbsoluteDecompositionInclusion F v sigma.1)).toAdd := by
  change
    ((arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U (x + y) v sigma.1).left.down -
      (arithmeticStageH2AbsoluteLocalLift F (n : ℕ) U (x + y) v sigma.1).left.down) -
    (((arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U x v sigma.1).left.down -
      (arithmeticStageH2AbsoluteLocalLift F (n : ℕ) U x v sigma.1).left.down) +
    ((arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U y v sigma.1).left.down -
      (arithmeticStageH2AbsoluteLocalLift F (n : ℕ) U y v sigma.1).left.down)) = _
  rw [arithmeticStageH2AbsoluteLocalLift_inertia F (n : ℕ) U (x + y) v sigma,
    arithmeticStageH2AbsoluteLocalLift_inertia F (n : ℕ) U x v sigma,
    arithmeticStageH2AbsoluteLocalLift_inertia F (n : ℕ) U y v sigma]
  change (_ - 0) - ((_ - 0) + (_ - 0)) = _
  simp only [sub_zero]
  rfl

end ClassFieldTower.Martinet.Shafarevich
