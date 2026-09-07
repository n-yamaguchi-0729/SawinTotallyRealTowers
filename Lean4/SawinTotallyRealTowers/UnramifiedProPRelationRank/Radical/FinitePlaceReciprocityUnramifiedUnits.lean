import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalReciprocityUnramifiedUnits
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceValuationDiagonal

set_option autoImplicit false
/-!
# Adic integral units detect unramified reciprocity characters

Compatibility of the intrinsic normalized valuation with the distinguished
adic valuation identifies its zero kernel with the actual completion's
integral-unit subgroup. The roots-of-unity-free local reciprocity criterion
therefore applies directly to finite-place idele factors.
-/

open scoped NumberField ValuativeRel WithZero Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open IsDedekindDomain ClassFieldTower.ProP LocalClassFieldTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact ((n : ℕ).Prime)]
variable (v : HeightOneSpectrum (𝓞 F))

local instance finitePlaceReciprocityUnitsValuativeRel :
    ValuativeRel (v.adicCompletion F) := finitePlaceAdicCompletionValuativeRel F v
local instance finitePlaceReciprocityUnitsLocalField :
    IsNonarchimedeanLocalField (v.adicCompletion F) :=
  finitePlaceAdicCompletionIsNonarchimedeanLocalField F v
local instance finitePlaceReciprocityUnitsTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance finitePlaceReciprocityUnitsDiscrete : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _
local instance finitePlaceReciprocityUnitsH1Module :
    Module (ZMod (n : ℕ))
      (ContinuousH1ZMod (p := (n : ℕ))
        (G := Field.absoluteGaloisGroup (v.adicCompletion F))) :=
  continuousH1ZModModule

/-- Valuation zero is exactly membership in the actual adic integer-unit subgroup. -/
theorem finitePlaceValuationMap_eq_zero_iff_integralUnit (a : (v.adicCompletion F)ˣ) :
    valuationMap (v.adicCompletion F) (Additive.ofMul a) = 0 ↔
      a ∈ (v.adicCompletionIntegers F).units := by
  rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  have h :
      WithZero.exp (valuationMap (v.adicCompletion F) (Additive.ofMul a)) =
        (Valued.v (a : v.adicCompletion F) : ℤᵐ⁰) := by
    rw [valuationMap_apply, v_apply]
    simp only [WithZero.exp, ofAdd_toAdd, WithZero.coe_unzero]
    change localIntegerValuation (v.adicCompletion F) a = _
    rw [finitePlaceLocalIntegerValuation_eq]
  rw [← WithZero.exp_inj, h]
  rfl

/-- An Artin character kills actual adic integral units exactly when its
continuous H¹ class is intrinsically unramified. -/
theorem finitePlaceLocalReciprocityUnitCharacter_integralUnits_iff_unramified
    (chi : ContinuousH1ZMod (p := (n : ℕ))
      (G := Field.absoluteGaloisGroup (v.adicCompletion F))) :
    (∀ a : (v.adicCompletion F)ˣ, a ∈ (v.adicCompletionIntegers F).units →
      localReciprocityUnitCharacter (v.adicCompletion F) (n : ℕ) chi a = 1) ↔
      chi ∈ localStandardUnramifiedH1 (v.adicCompletion F) n := by
  rw [← localReciprocityUnitCharacter_valuationZero_iff_unramified
    (v.adicCompletion F) n chi]
  simp_rw [finitePlaceValuationMap_eq_zero_iff_integralUnit]

end ClassFieldTower.Martinet.Shafarevich
