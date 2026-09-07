import GaloisCohomology.Kummer.Concrete.AbsoluteKummerH1
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalSelmer

set_option autoImplicit false
/-!
# Ideal-power radical classes as absolute Kummer characters

For a number field containing a primitive `n`-th root of unity, this file
embeds the empty-support Selmer group, and hence the ideal-power radical
quotient, into the continuous mod-`n` characters of the absolute Galois
group.  The image subgroup records exactly the Kummer characters satisfying
the empty finite-valuation condition.
-/

open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K] [NumberField K]

local instance idealRadicalCharacterTopology (n : ℕ) :
    TopologicalSpace (Multiplicative (ZMod n)) := ⊥

local instance idealRadicalCharacterDiscreteTopology (n : ℕ) :
    DiscreteTopology (Multiplicative (ZMod n)) :=
  discreteTopology_bot _

/-- The inclusion of the empty-support Selmer group into the full group of
power classes. -/
def emptySupportSelmerToAbsolutePowerClass (n : ℕ+) :
    EmptySupportSelmerGroup K n →*
      Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range where
  toFun x := x.1
  map_one' := rfl
  map_mul' _ _ := rfl

theorem emptySupportSelmerToAbsolutePowerClass_injective (n : ℕ+) :
    Function.Injective (emptySupportSelmerToAbsolutePowerClass K n) :=
  Subtype.val_injective

/-- Empty-support Selmer classes as continuous absolute Kummer characters. -/
noncomputable def emptySupportSelmerToAbsoluteKummerCharacter
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    EmptySupportSelmerGroup K n →*
      (Field.absoluteGaloisGroup K →ₜ*
        Multiplicative (ZMod (n : ℕ))) :=
  (absoluteKummerContinuousZModCharacterEquiv K n hmu).toMonoidHom.comp
    (emptySupportSelmerToAbsolutePowerClass K n)

@[simp]
theorem emptySupportSelmerToAbsoluteKummerCharacter_apply
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (x : EmptySupportSelmerGroup K n) :
    emptySupportSelmerToAbsoluteKummerCharacter K n hmu x =
      absoluteKummerContinuousZModCharacterEquiv K n hmu x.1 :=
  rfl

theorem emptySupportSelmerToAbsoluteKummerCharacter_injective
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Function.Injective
      (emptySupportSelmerToAbsoluteKummerCharacter K n hmu) := by
  intro x y hxy
  apply emptySupportSelmerToAbsolutePowerClass_injective K n
  apply (absoluteKummerContinuousZModCharacterEquiv K n hmu).injective
  exact hxy

/-- Ideal-power radical classes as continuous absolute Kummer characters. -/
noncomputable def idealNthPowerRadicalQuotientToAbsoluteKummerCharacter
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    IdealNthPowerRadicalQuotient K n →*
      (Field.absoluteGaloisGroup K →ₜ*
        Multiplicative (ZMod (n : ℕ))) :=
  (emptySupportSelmerToAbsoluteKummerCharacter K n hmu).comp
    (idealNthPowerRadicalQuotientEquivEmptySelmer K n).toMonoidHom

@[simp]
theorem idealNthPowerRadicalQuotientToAbsoluteKummerCharacter_apply
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (x : IdealNthPowerRadicalQuotient K n) :
    idealNthPowerRadicalQuotientToAbsoluteKummerCharacter K n hmu x =
      emptySupportSelmerToAbsoluteKummerCharacter K n hmu
        (idealNthPowerRadicalQuotientEquivEmptySelmer K n x) :=
  rfl

@[simp]
theorem idealNthPowerRadicalQuotientToAbsoluteKummerCharacter_mk
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : (idealNthPowerRadicalKummerSubgroup K n).1) :
    idealNthPowerRadicalQuotientToAbsoluteKummerCharacter K n hmu
        (restrictedRadicalQuotientMk n
          (idealNthPowerRadicalKummerSubgroup K n) a) =
      absoluteKummerContinuousZModCharacterEquiv K n hmu
        (QuotientGroup.mk'
          (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a.1) := by
  change
    absoluteKummerContinuousZModCharacterEquiv K n hmu
        ((idealNthPowerRadicalQuotientEquivEmptySelmer K n
          (restrictedRadicalQuotientMk n
            (idealNthPowerRadicalKummerSubgroup K n) a)).1) =
      absoluteKummerContinuousZModCharacterEquiv K n hmu
        (QuotientGroup.mk'
          (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a.1)
  congr 1

theorem idealNthPowerRadicalQuotientToAbsoluteKummerCharacter_injective
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Function.Injective
      (idealNthPowerRadicalQuotientToAbsoluteKummerCharacter K n hmu) := by
  intro x y hxy
  apply (idealNthPowerRadicalQuotientEquivEmptySelmer K n).injective
  apply emptySupportSelmerToAbsoluteKummerCharacter_injective K n hmu
  exact hxy

/-- The subgroup of absolute Kummer characters cut out by the empty-support
Selmer condition. -/
noncomputable def idealPowerRadicalAbsoluteKummerCharacterSubgroup
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Subgroup
      (Field.absoluteGaloisGroup K →ₜ*
        Multiplicative (ZMod (n : ℕ))) :=
  (emptySupportSelmerToAbsoluteKummerCharacter K n hmu).range

/-- The empty-support Selmer group is equivalent to its subgroup of absolute
Kummer characters. -/
noncomputable def emptySupportSelmerEquivAbsoluteKummerCharacterSubgroup
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    EmptySupportSelmerGroup K n ≃*
      idealPowerRadicalAbsoluteKummerCharacterSubgroup K n hmu :=
  MonoidHom.ofInjective
    (emptySupportSelmerToAbsoluteKummerCharacter_injective K n hmu)

@[simp]
theorem emptySupportSelmerEquivAbsoluteKummerCharacterSubgroup_apply_coe
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (x : EmptySupportSelmerGroup K n) :
    (emptySupportSelmerEquivAbsoluteKummerCharacterSubgroup K n hmu x :
        Field.absoluteGaloisGroup K →ₜ*
          Multiplicative (ZMod (n : ℕ))) =
      emptySupportSelmerToAbsoluteKummerCharacter K n hmu x :=
  rfl

/-- The ideal-power radical quotient is equivalent to the same subgroup of
absolute Kummer characters. -/
noncomputable def idealNthPowerRadicalQuotientEquivAbsoluteKummerCharacterSubgroup
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    IdealNthPowerRadicalQuotient K n ≃*
      idealPowerRadicalAbsoluteKummerCharacterSubgroup K n hmu :=
  (idealNthPowerRadicalQuotientEquivEmptySelmer K n).trans
    (emptySupportSelmerEquivAbsoluteKummerCharacterSubgroup K n hmu)

@[simp]
theorem idealNthPowerRadicalQuotientEquivAbsoluteKummerCharacterSubgroup_apply_coe
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (x : IdealNthPowerRadicalQuotient K n) :
    (idealNthPowerRadicalQuotientEquivAbsoluteKummerCharacterSubgroup
        K n hmu x :
      Field.absoluteGaloisGroup K →ₜ*
        Multiplicative (ZMod (n : ℕ))) =
      idealNthPowerRadicalQuotientToAbsoluteKummerCharacter K n hmu x :=
  rfl

end ClassFieldTower.Martinet.Shafarevich
