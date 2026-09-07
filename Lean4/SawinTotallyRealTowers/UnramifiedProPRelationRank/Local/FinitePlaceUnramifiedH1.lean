import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import ProCGroups.ProP.ContinuousH1
import ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
import ValuedFieldTheory.Ramification.HilbertRamification.LocalizationRamificationGroups

set_option autoImplicit false
/-!
# Unramified degree-one characters at a finite place

The valuation-subring inertia group is pulled back to the chosen absolute decomposition group.
Restriction to this inertia subgroup defines the unramified continuous `H¹` subspace.
-/

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open AlgebraicNumberTheory.Valuations
open ClassFieldTower.Cohomology
open ClassFieldTower.ProP

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ)

local instance finitePlaceUnramifiedH1Module
    {q : ℕ} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := H)) :=
  continuousH1ZModModule

/-- The chosen absolute-value extension at a finite place is nonarchimedean. -/
theorem finitePlaceAbsoluteValueExtension_nonarchimedean
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (finitePlaceAbsoluteValueExtension F v).1 :=
  finitePlaceExtension_nonarchimedean v (finitePlaceAbsoluteValueExtension F v)

/-- The valuation subring of the algebraic closure selected by the chosen finite place. -/
noncomputable abbrev finitePlaceAbsoluteValuationSubring
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ValuationSubring (AlgebraicClosure F) :=
  absoluteValueValuationSubring
    (finitePlaceAbsoluteValueExtension F v).1
    (finitePlaceAbsoluteValueExtension_nonarchimedean F v)

/-- The canonical comparison from the absolute decomposition group to its valuation-subring
form. -/
noncomputable def finitePlaceAbsoluteDecompositionValuationEquiv
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteDecompositionGroup F v ≃*
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup F
        (finitePlaceAbsoluteValuationSubring F v) :=
  HilbertRamification.localizationRamificationGroups_absoluteValueDecompositionGroupEquiv
    (NumberField.HeightOneSpectrum.adicAbv F v)
    (RayClass.adicAbv_isNontrivial v)
    (finitePlaceAbsoluteValueExtension F v)
    (finitePlaceAbsoluteValueExtension_nonarchimedean F v)

/-- Absolute inertia inside the chosen absolute decomposition group. -/
noncomputable abbrev finitePlaceAbsoluteInertiaSubgroup
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Subgroup (finitePlaceAbsoluteDecompositionGroup F v) :=
  (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup F
      (finitePlaceAbsoluteValuationSubring F v)).comap
    (finitePlaceAbsoluteDecompositionValuationEquiv F v).toMonoidHom

/-- The continuous inclusion of absolute inertia into absolute decomposition. -/
def finitePlaceAbsoluteInertiaInclusion
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteInertiaSubgroup F v →ₜ*
      finitePlaceAbsoluteDecompositionGroup F v :=
  subgroupInclusion (finitePlaceAbsoluteInertiaSubgroup F v)

@[simp]
theorem finitePlaceAbsoluteInertiaInclusion_apply
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteInertiaSubgroup F v) :
    finitePlaceAbsoluteInertiaInclusion F v sigma = sigma.1 :=
  rfl

/-- Restriction of continuous mod-`p` characters from decomposition to inertia. -/
def finitePlaceH1InertiaRestrictionAddHom
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) →+
      ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteInertiaSubgroup F v) where
  toFun chi :=
    { toFun := fun sigma ↦ chi (Additive.ofMul sigma.toMul.1)
      map_zero' := chi.map_zero
      map_add' := fun sigma tau ↦ chi.map_add
        (Additive.ofMul sigma.toMul.1) (Additive.ofMul tau.toMul.1)
      continuous_toFun := chi.continuous_toFun.comp continuous_subtype_val }
  map_zero' := by
    ext sigma
    rfl
  map_add' := by
    intro chi psi
    ext sigma
    rfl

/-- Linear restriction of continuous mod-`p` characters from decomposition to inertia. -/
noncomputable def finitePlaceH1InertiaRestriction
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) →ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteInertiaSubgroup F v) :=
  (finitePlaceH1InertiaRestrictionAddHom F p v).toZModLinearMap p

@[simp]
theorem finitePlaceH1InertiaRestriction_apply
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v))
    (sigma : finitePlaceAbsoluteInertiaSubgroup F v) :
    finitePlaceH1InertiaRestriction F p v chi (Additive.ofMul sigma) =
      chi (Additive.ofMul sigma.1) :=
  rfl

/-- Continuous degree-one characters unramified at `v`: those trivial on absolute inertia. -/
noncomputable abbrev finitePlaceUnramifiedH1
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Submodule (ZMod p)
      (ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v)) :=
  LinearMap.ker (finitePlaceH1InertiaRestriction F p v)

theorem mem_finitePlaceUnramifiedH1_iff
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v)) :
    chi ∈ finitePlaceUnramifiedH1 F p v ↔
      ∀ sigma : finitePlaceAbsoluteInertiaSubgroup F v,
        chi (Additive.ofMul sigma.1) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h sigma
    have hvalue := DFunLike.congr_fun h (Additive.ofMul sigma)
    exact hvalue
  · intro h
    ext sigma
    exact h sigma.toMul

end ClassFieldTower.Martinet.Shafarevich
