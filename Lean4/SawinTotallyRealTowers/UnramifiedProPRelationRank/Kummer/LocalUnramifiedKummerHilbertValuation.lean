import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalHilbertKummerDual
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF

set_option autoImplicit false
/-!
# Unramified Kummer Hilbert characters and valuation

For a chosen simple Kummer extension which is unramified, its Hilbert
character is a Frobenius scalar times normalized valuation.  The argument
uses the full unramified local Artin formula and therefore also applies at
places above the Kummer exponent.
-/

open scoped ValuativeRel

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory LocalClassFieldTheory LocalClassFieldTheory.Kummer
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [CharZero K]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The chosen simple Kummer extension, with its canonical spectral
valuation, is unramified. -/
def IsUnramifiedChosenSimpleKummer
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (a : Kˣ) : Prop := by
  let E := chosenSimpleKummerExtension K n hnK a
  let _ : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK a
  letI : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  letI : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  letI : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  letI : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  letI : Module.Finite
      (ValuativeRel.valuation K).integer
      (ValuativeRel.valuation E).integer :=
    localCompleteDVF_integerRing_moduleFinite K E
  exact IsUnramifiedValuedExtension K E

/-- Frobenius acts on the chosen Kummer root through this base-field root
of unity. -/
noncomputable def unramifiedChosenSimpleKummerFrobeniusRoot
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ)
    (ha : IsUnramifiedChosenSimpleKummer K n hnK a) :
    nthRootsSubgroup K (n : ℕ) := by
  let E := chosenSimpleKummerExtension K n hnK a
  let _ : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK a
  let _ : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
  let _ : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  let _ : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let _ : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let _ : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let _ : Module.Finite
      (ValuativeRel.valuation K).integer
      (ValuativeRel.valuation E).integer :=
    localCompleteDVF_integerRing_moduleFinite K E
  let _ : IsUnramifiedValuedExtension K E := ha
  exact
    (nthRootsSubgroupEquivOfPrimitiveRoots K E n hmu).symm
      (chosenSimpleKummerRootCharacter K n hnK hmu a
        (arithmeticFrobeniusOfUnramifiedValuation K E))

omit [CharZero K] in
/-- For any unramified chosen simple Kummer extension, the Hilbert character
of its radical is a Frobenius scalar times normalized valuation.  No tame
residue-characteristic hypothesis is used. -/
theorem localHilbertSymbol_eq_unramifiedFrobenius_zpow
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) (ha : IsUnramifiedChosenSimpleKummer K n hnK a) :
    localHilbertSymbol K n hnK hmu a b =
      (unramifiedChosenSimpleKummerFrobeniusRoot K n hnK hmu a ha) ^
        (-valuationMap K (Additive.ofMul b)) := by
  let E := chosenSimpleKummerExtension K n hnK a
  let _ : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK a
  let _ : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
  let _ : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  let _ : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let _ : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let _ : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let _ : Module.Finite
      (ValuativeRel.valuation K).integer
      (ValuativeRel.valuation E).integer :=
    localCompleteDVF_integerRing_moduleFinite K E
  let _ : IsUnramifiedValuedExtension K E := ha
  rw [localHilbertSymbol_skew]
  change
    ((nthRootsSubgroupEquivOfPrimitiveRoots K E n hmu).symm
      (chosenSimpleKummerRootCharacter K n hnK hmu a
        (abelianLocalArtinMonoidHom K E b)))⁻¹ = _
  rw [abelianLocalArtinMonoidHom_eq_frobenius_zpow]
  rw [map_zpow, map_zpow]
  rw [← zpow_neg]
  rfl

end ClassFieldTower.Martinet.Shafarevich
