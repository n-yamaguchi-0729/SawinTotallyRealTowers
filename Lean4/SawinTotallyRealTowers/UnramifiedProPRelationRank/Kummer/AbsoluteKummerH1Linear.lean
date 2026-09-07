import GaloisCohomology.Kummer.Concrete.AbsoluteKummerH1
import GaloisCohomology.Kummer.Concrete.SUnitPreparation.PrimePowerKernelCoordinates

set_option autoImplicit false
/-!
# Linear absolute Kummer characters

For a prime `p`, the absolute Kummer equivalence is linear after giving both power classes and
continuous mod-`p` characters their canonical exponent-`p` `ZMod p`-module structures.
-/

open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K]
variable (p : ℕ) [Fact p.Prime]

local instance absoluteKummerLinearCharacterTopology :
    TopologicalSpace (Multiplicative (ZMod p)) := ⊥
local instance absoluteKummerLinearCharacterDiscreteTopology :
    DiscreteTopology (Multiplicative (ZMod p)) :=
  discreteTopology_bot _

omit [Fact p.Prime] in
/-- Every absolute power class modulo `p`-th powers has exponent dividing `p`. -/
theorem absolutePowerClassQuotient_pow_eq_one
    (x : Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) :
    x ^ p = 1 := by
  refine QuotientGroup.induction_on x fun a ↦ ?_
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨a, by simp⟩

/-- Every continuous absolute mod-`p` character has exponent dividing `p`. -/
theorem absoluteContinuousZModCharacter_pow_eq_one
    (x : Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod p)) :
    x ^ p = 1 := by
  apply ContinuousMonoidHom.ext
  intro σ
  rw [ContinuousMonoidHom.pow_apply,
    ContinuousMonoidHom.one_toFun]
  apply Multiplicative.ofAdd.injective
  change p • (x σ).toAdd = 0
  simp

/-- The power-class group as its canonical `ZMod p`-module object. -/
noncomputable def absolutePowerClassModP : ModuleCat (ZMod p) := by
  letI : Module (ZMod p)
      (Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)) :=
    additiveZModModuleOfPowEqOne p
      (absolutePowerClassQuotient_pow_eq_one K p)
  exact ModuleCat.of (ZMod p)
    (Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range))

/-- Continuous absolute mod-`p` characters as their canonical `ZMod p`-module object. -/
noncomputable def absoluteContinuousZModCharacterModP : ModuleCat (ZMod p) := by
  letI : Module (ZMod p)
      (Additive
        (Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod p))) :=
    additiveZModModuleOfPowEqOne p
      (absoluteContinuousZModCharacter_pow_eq_one K p)
  exact ModuleCat.of (ZMod p)
    (Additive
      (Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod p)))

/-- The absolute Kummer equivalence, upgraded to a `ZMod p`-linear equivalence. -/
noncomputable def absoluteKummerContinuousZModCharacterLinearEquiv
    [CharZero K]
    (hmu : (primitiveRoots p K).Nonempty) :
    absolutePowerClassModP K p ≃ₗ[ZMod p]
      absoluteContinuousZModCharacterModP K p := by
  letI : Module (ZMod p)
      (Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)) :=
    additiveZModModuleOfPowEqOne p
      (absolutePowerClassQuotient_pow_eq_one K p)
  letI : Module (ZMod p)
      (Additive
        (Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod p))) :=
    additiveZModModuleOfPowEqOne p
      (absoluteContinuousZModCharacter_pow_eq_one K p)
  let e := absoluteKummerContinuousZModCharacterEquiv K
    (p.toPNat (Fact.out : p.Prime).pos) hmu
  let f :
      Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →+
        Additive
          (Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod p)) :=
  {
    toFun x := Additive.ofMul (e (Additive.toMul x))
    map_zero' := by
      apply Additive.toMul.injective
      exact e.map_one
    map_add' x y := by
      apply Additive.toMul.injective
      exact e.map_mul (Additive.toMul x) (Additive.toMul y)
  }
  refine LinearEquiv.ofBijective (f.toZModLinearMap p) ?_
  constructor
  · intro x y hxy
    apply Additive.toMul.injective
    apply e.injective
    exact congrArg Additive.toMul hxy
  · intro y
    refine ⟨Additive.ofMul (e.symm (Additive.toMul y)), ?_⟩
    apply Additive.toMul.injective
    exact e.apply_symm_apply (Additive.toMul y)

end ClassFieldTower.Martinet.Shafarevich
