import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteKummerH1Linear
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalAbsoluteKummer
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalModule

set_option autoImplicit false
/-!
# Linear ideal-power radical Kummer characters

For a number field containing the `p`-th roots of unity, the ideal-power radical embeds
canonically into the continuous absolute mod-`p` character module. Dualizing this inclusion
gives the corresponding surjective restriction map on linear duals.
-/

open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime]

local instance idealPowerRadicalLinearCharacterTopology :
    TopologicalSpace (Multiplicative (ZMod p)) := ⊥

local instance idealPowerRadicalLinearCharacterDiscreteTopology :
    DiscreteTopology (Multiplicative (ZMod p)) :=
  discreteTopology_bot _

/-- The inclusion of ideal-power radical classes into all absolute power classes, linearized
over `ZMod p`. -/
noncomputable def idealPowerRadicalToAbsolutePowerClassLinearMap :
    idealPowerRadicalModP K p →ₗ[ZMod p]
      absolutePowerClassModP K p := by
  letI : Module (ZMod p)
      (Additive (IdealNthPowerRadicalQuotient K
        (p.toPNat (Fact.out : p.Prime).pos))) :=
    idealPowerRadicalModPModule K p
  letI : Module (ZMod p)
      (Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)) :=
    additiveZModModuleOfPowEqOne p
      (absolutePowerClassQuotient_pow_eq_one K p)
  let g :=
    (emptySupportSelmerToAbsolutePowerClass K
        (p.toPNat (Fact.out : p.Prime).pos)).comp
      (idealNthPowerRadicalQuotientEquivEmptySelmer K
        (p.toPNat (Fact.out : p.Prime).pos)).toMonoidHom
  let f :
      Additive (IdealNthPowerRadicalQuotient K
          (p.toPNat (Fact.out : p.Prime).pos)) →+
        Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) :=
  {
    toFun x := Additive.ofMul (g (Additive.toMul x))
    map_zero' := by
      apply Additive.toMul.injective
      exact g.map_one
    map_add' x y := by
      apply Additive.toMul.injective
      exact g.map_mul (Additive.toMul x) (Additive.toMul y)
  }
  exact f.toZModLinearMap p

@[simp]
theorem idealPowerRadicalToAbsolutePowerClassLinearMap_apply
    (x : idealPowerRadicalModP K p) :
    idealPowerRadicalToAbsolutePowerClassLinearMap K p x =
      Additive.ofMul
        (emptySupportSelmerToAbsolutePowerClass K
          (p.toPNat (Fact.out : p.Prime).pos)
          (idealNthPowerRadicalQuotientEquivEmptySelmer K
            (p.toPNat (Fact.out : p.Prime).pos) (Additive.toMul x))) :=
  rfl

/-- The ideal-power radical inclusion into all absolute power classes is injective. -/
theorem idealPowerRadicalToAbsolutePowerClassLinearMap_injective :
    Function.Injective
      (idealPowerRadicalToAbsolutePowerClassLinearMap K p) := by
  intro x y hxy
  change
    Additive.ofMul
        (emptySupportSelmerToAbsolutePowerClass K
          (p.toPNat (Fact.out : p.Prime).pos)
          (idealNthPowerRadicalQuotientEquivEmptySelmer K
            (p.toPNat (Fact.out : p.Prime).pos) (Additive.toMul x))) =
      Additive.ofMul
        (emptySupportSelmerToAbsolutePowerClass K
          (p.toPNat (Fact.out : p.Prime).pos)
          (idealNthPowerRadicalQuotientEquivEmptySelmer K
            (p.toPNat (Fact.out : p.Prime).pos) (Additive.toMul y))) at hxy
  apply Additive.toMul.injective
  apply (idealNthPowerRadicalQuotientEquivEmptySelmer K
    (p.toPNat (Fact.out : p.Prime).pos)).injective
  apply emptySupportSelmerToAbsolutePowerClass_injective K
    (p.toPNat (Fact.out : p.Prime).pos)
  apply Additive.ofMul.injective
  exact hxy

/-- The ideal-power radical as a linear subspace of continuous absolute mod-`p` characters. -/
noncomputable def idealPowerRadicalToAbsoluteKummerLinearMap
    (hmu : (primitiveRoots p K).Nonempty) :
    idealPowerRadicalModP K p →ₗ[ZMod p]
      absoluteContinuousZModCharacterModP K p :=
  (absoluteKummerContinuousZModCharacterLinearEquiv K p hmu).toLinearMap.comp
    (idealPowerRadicalToAbsolutePowerClassLinearMap K p)

@[simp]
theorem idealPowerRadicalToAbsoluteKummerLinearMap_apply
    (hmu : (primitiveRoots p K).Nonempty)
    (x : idealPowerRadicalModP K p) :
    Additive.toMul (idealPowerRadicalToAbsoluteKummerLinearMap K p hmu x) =
      idealNthPowerRadicalQuotientToAbsoluteKummerCharacter K
        (p.toPNat (Fact.out : p.Prime).pos) hmu (Additive.toMul x) :=
  rfl

/-- The linearized absolute Kummer map on the ideal-power radical is injective. -/
theorem idealPowerRadicalToAbsoluteKummerLinearMap_injective
    (hmu : (primitiveRoots p K).Nonempty) :
    Function.Injective
      (idealPowerRadicalToAbsoluteKummerLinearMap K p hmu) := by
  exact (absoluteKummerContinuousZModCharacterLinearEquiv K p hmu).injective.comp
    (idealPowerRadicalToAbsolutePowerClassLinearMap_injective K p)

/-- Restriction of linear functionals along the ideal-radical Kummer inclusion. -/
noncomputable def absoluteKummerDualRestriction
    (hmu : (primitiveRoots p K).Nonempty) :
    Module.Dual (ZMod p) (absoluteContinuousZModCharacterModP K p) →ₗ[ZMod p]
      Module.Dual (ZMod p) (idealPowerRadicalModP K p) :=
  (idealPowerRadicalToAbsoluteKummerLinearMap K p hmu).dualMap

/-- Every functional on the ideal-power radical extends to the absolute character module. -/
theorem absoluteKummerDualRestriction_surjective
    (hmu : (primitiveRoots p K).Nonempty) :
    Function.Surjective (absoluteKummerDualRestriction K p hmu) :=
  LinearMap.dualMap_surjective_of_injective
    (idealPowerRadicalToAbsoluteKummerLinearMap_injective K p hmu)

end ClassFieldTower.Martinet.Shafarevich
