import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.EmptySupportKummerCokernel
import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology

set_option autoImplicit false
/-!
# Finite-place valuation defects and local Kummer duality

At a finite place of a number field, normalized valuation modulo `p` descends to a
surjective linear map from local `p`-power classes to `ZMod p`.  Its dual embeds the
one-dimensional valuation-defect space into the dual of the local power-class module.

The resulting dual map is the local object that must eventually be compared with the
coordinate maps in `finiteValuationLocalizationDual` and, through local Hilbert duality, with
local Kummer classes.
-/

open scoped NumberField ValuativeRel

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open IsDedekindDomain KummerTheory

variable (K : Type*) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime]

/-- The valuation relation induced by the distinguished integer-valued valuation on an adic
completion. -/
@[reducible]
noncomputable def finitePlaceAdicCompletionValuativeRel
    (v : HeightOneSpectrum (𝓞 K)) : ValuativeRel (v.adicCompletion K) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))

/-- A number-field completion, equipped with its distinguished adic valuation, is a
nonarchimedean local field. -/
theorem finitePlaceAdicCompletionIsNonarchimedeanLocalField
    (v : HeightOneSpectrum (𝓞 K)) :
    @IsNonarchimedeanLocalField (v.adicCompletion K) inferInstance
      (finitePlaceAdicCompletionValuativeRel K v) inferInstance := by
  let L := v.adicCompletion K
  let ν : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v
  let _ : Valuation.IsNontrivial ν := inferInstance
  let _ : ValuativeRel L := finitePlaceAdicCompletionValuativeRel K v
  let _ : ν.Compatible := Valuation.Compatible.ofValuation ν
  let _ : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial ν).2 inferInstance
  let _ : IsValuativeTopology L :=
    LocalFieldTheory.isValuativeTopology_of_valued_ofValuation
      L (WithZero (Multiplicative ℤ))
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

/-- Local `p`-power classes at the finite place `v`, with their canonical `ZMod p`-module
structure. -/
abbrev FinitePlaceLocalPowerClassModP
    (v : HeightOneSpectrum (𝓞 K)) : ModuleCat (ZMod p) :=
  absolutePowerClassModP (v.adicCompletion K) p

/-- Normalized valuation modulo `p`, descended to local `p`-power classes. -/
noncomputable def finitePlaceLocalPowerClassValuationMonoidHom
    (v : HeightOneSpectrum (𝓞 K)) :
    ((v.adicCompletion K)ˣ ⧸
        (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) →*
      Multiplicative (ZMod p) := by
  let L := v.adicCompletion K
  let _ : ValuativeRel L := finitePlaceAdicCompletionValuativeRel K v
  let _ : IsNonarchimedeanLocalField L :=
    finitePlaceAdicCompletionIsNonarchimedeanLocalField K v
  exact QuotientGroup.lift
    (powMonoidHom p : Lˣ →* Lˣ).range
    (LocalClassFieldTheory.valuationModDegreeMulHom L p)
    (by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
      apply Multiplicative.ofAdd.injective
      change p •
          (LocalClassFieldTheory.valuationModDegreeMulHom L p x).toAdd = 0
      simp)

/-- The finite-place local valuation on power classes is surjective. -/
theorem finitePlaceLocalPowerClassValuationMonoidHom_surjective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective
      (finitePlaceLocalPowerClassValuationMonoidHom K p v) := by
  let L := v.adicCompletion K
  let _ : ValuativeRel L := finitePlaceAdicCompletionValuativeRel K v
  let _ : IsNonarchimedeanLocalField L :=
    finitePlaceAdicCompletionIsNonarchimedeanLocalField K v
  intro z
  obtain ⟨x, hx⟩ :=
    LocalClassFieldTheory.valuationModDegreeMulHom_surjective L p z
  refine ⟨QuotientGroup.mk' (powMonoidHom p : Lˣ →* Lˣ).range x, ?_⟩
  change LocalClassFieldTheory.valuationModDegreeMulHom L p x = z
  exact hx

/-- Normalized valuation modulo `p` as a linear map on local power classes. -/
noncomputable def finitePlaceLocalPowerClassValuation
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceLocalPowerClassModP K p v →ₗ[ZMod p] ZMod p := by
  letI : Module (ZMod p)
      (Additive
        ((v.adicCompletion K)ˣ ⧸
          (powMonoidHom p :
            (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)) :=
    additiveZModModuleOfPowEqOne p
      (absolutePowerClassQuotient_pow_eq_one (v.adicCompletion K) p)
  let f :
      Additive
          ((v.adicCompletion K)ˣ ⧸
            (powMonoidHom p :
              (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) →+
        ZMod p :=
    { toFun := fun x ↦
        (finitePlaceLocalPowerClassValuationMonoidHom K p v
          (Additive.toMul x)).toAdd
      map_zero' := by
        change
          (finitePlaceLocalPowerClassValuationMonoidHom K p v 1).toAdd = 0
        rw [map_one]
        rfl
      map_add' := by
        intro x y
        change
          (finitePlaceLocalPowerClassValuationMonoidHom K p v
            (Additive.toMul x * Additive.toMul y)).toAdd = _
        rw [map_mul]
        rfl }
  exact f.toZModLinearMap p

@[simp]
theorem finitePlaceLocalPowerClassValuation_apply
    (v : HeightOneSpectrum (𝓞 K))
    (x : FinitePlaceLocalPowerClassModP K p v) :
    Multiplicative.ofAdd (finitePlaceLocalPowerClassValuation K p v x) =
      finitePlaceLocalPowerClassValuationMonoidHom K p v (Additive.toMul x) :=
  rfl

/-- The linear local valuation on power classes is surjective. -/
theorem finitePlaceLocalPowerClassValuation_surjective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (finitePlaceLocalPowerClassValuation K p v) := by
  intro z
  obtain ⟨x, hx⟩ :=
    finitePlaceLocalPowerClassValuationMonoidHom_surjective K p v
      (Multiplicative.ofAdd z)
  refine ⟨Additive.ofMul x, ?_⟩
  apply Multiplicative.ofAdd.injective
  exact hx

/-- The one-dimensional valuation-defect space inside the dual of local power classes. -/
noncomputable def finitePlaceValuationDefectDualEmbedding
    (v : HeightOneSpectrum (𝓞 K)) :
    ZMod p →ₗ[ZMod p]
      Module.Dual (ZMod p) (FinitePlaceLocalPowerClassModP K p v) :=
  (finitePlaceLocalPowerClassValuation K p v).dualMap.comp
    (LinearMap.lsmul (ZMod p) (ZMod p))

@[simp]
theorem finitePlaceValuationDefectDualEmbedding_apply
    (v : HeightOneSpectrum (𝓞 K))
    (a : ZMod p) (x : FinitePlaceLocalPowerClassModP K p v) :
    finitePlaceValuationDefectDualEmbedding K p v a x =
      a * finitePlaceLocalPowerClassValuation K p v x :=
  rfl

/-- The dualized valuation-defect map is injective. -/
theorem finitePlaceValuationDefectDualEmbedding_injective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (finitePlaceValuationDefectDualEmbedding K p v) := by
  apply Function.Injective.comp
    (LinearMap.dualMap_injective_of_surjective
      (finitePlaceLocalPowerClassValuation_surjective K p v))
  intro a b hab
  have h := LinearMap.congr_fun hab 1
  simpa using h

end ClassFieldTower.Martinet.Shafarevich
