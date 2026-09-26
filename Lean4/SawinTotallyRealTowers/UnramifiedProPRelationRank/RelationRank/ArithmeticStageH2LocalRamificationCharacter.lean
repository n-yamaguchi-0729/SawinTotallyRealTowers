/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2CocycleExtensionLiftDifference
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2UnramifiedLocalLift
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
/-!
# The inertia character of an arithmetic-stage local lift

Compare a local solution with the unramified solution constructed from the
vanishing of unramified local `H²`.  Their difference is a continuous
`ZMod p`-valued character on the absolute decomposition group.  Its restriction
to inertia records the given solution's ramification, independently of the
chosen unramified reference solution.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.Martinet ClassFieldTower.ProP
open ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))
variable (xU : continuousCohomologyZModPLifted p
  (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
    (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
variable (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
variable (s : finitePlaceAbsoluteDecompositionGroup F v →ₜ* DegreeTwoCentralExtension xU)
variable (hs : (H2CocycleExtension.projection (degreeTwoCocycleRepresentative xU)).comp s =
  arithmeticStageFinitePlaceAbsoluteQuotientMap F p U v)

local instance arithmeticStageH2LocalRamificationCanonicalZModAddCommGroup :
    AddCommGroup (ZMod p) :=
  (ZMod.instField p).toDivisionRing.toAddCommGroup

/-- The ramification character of a local solution, obtained by subtracting
the constructed unramified solution and restricting to absolute inertia. -/
def arithmeticStageH2LocalRamificationCharacter :
    finitePlaceAbsoluteInertiaSubgroup F v →ₜ* Multiplicative (ZMod p) :=
  (H2CocycleExtension.liftDifference (degreeTwoCocycleRepresentative xU)
    s (arithmeticStageH2AbsoluteLocalLift F p U xU v)
    (hs.trans (arithmeticStageH2AbsoluteLocalLift_projection F p U xU v).symm)).comp
      (subgroupInclusion (finitePlaceAbsoluteInertiaSubgroup F v))

/-- On inertia, the character is just the given lift's coefficient coordinate;
the unramified reference contributes zero. -/
@[simp]
theorem arithmeticStageH2LocalRamificationCharacter_apply
    (sigma : finitePlaceAbsoluteInertiaSubgroup F v) :
    arithmeticStageH2LocalRamificationCharacter F p U xU v s hs sigma =
      Multiplicative.ofAdd (s sigma.1).left.down := by
  change Multiplicative.ofAdd ((s sigma.1).left.down -
      (arithmeticStageH2AbsoluteLocalLift F p U xU v sigma.1).left.down) = _
  rw [arithmeticStageH2AbsoluteLocalLift_inertia F p U xU v sigma]
  change Multiplicative.ofAdd ((s sigma.1).left.down - 0) = _
  rw [sub_zero]

/-- The local solution is unramified precisely when its inertia character
is trivial. -/
theorem arithmeticStageH2LocalRamificationCharacter_eq_one_iff :
    arithmeticStageH2LocalRamificationCharacter F p U xU v s hs = 1 ↔
      finitePlaceAbsoluteInertiaSubgroup F v ≤ s.toMonoidHom.ker := by
  exact H2CocycleExtension.liftDifference_restrict_eq_one_iff
    (degreeTwoCocycleRepresentative xU) s (arithmeticStageH2AbsoluteLocalLift F p U xU v)
    (hs.trans (arithmeticStageH2AbsoluteLocalLift_projection F p U xU v).symm)
    (finitePlaceAbsoluteInertiaSubgroup F v)
    (arithmeticStageH2AbsoluteLocalLift_inertia_le_ker F p U xU v)

/-- The ramification character extends to the absolute decomposition group,
with an explicit extension supplied by the difference of the two local lifts. -/
theorem arithmeticStageH2LocalRamificationCharacter_extends :
    ∃ chi : finitePlaceAbsoluteDecompositionGroup F v →ₜ* Multiplicative (ZMod p),
      chi.comp (subgroupInclusion (finitePlaceAbsoluteInertiaSubgroup F v)) =
        arithmeticStageH2LocalRamificationCharacter F p U xU v s hs := by
  exact ⟨H2CocycleExtension.liftDifference (degreeTwoCocycleRepresentative xU)
    s (arithmeticStageH2AbsoluteLocalLift F p U xU v)
    (hs.trans (arithmeticStageH2AbsoluteLocalLift_projection F p U xU v).symm), rfl⟩

end ClassFieldTower.Martinet.Shafarevich
