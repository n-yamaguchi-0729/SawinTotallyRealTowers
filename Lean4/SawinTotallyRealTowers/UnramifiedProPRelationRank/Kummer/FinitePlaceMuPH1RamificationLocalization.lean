/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FinitePlaceMuPH1Localization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
/-!
# Finite-place ramification of natural `mu_p` Kummer classes

The natural `mu_p` representation on a chosen finite-place decomposition
group restricts further to absolute inertia.  This file packages the induced
map on continuous `H¹`, its unramified kernel, and the family of inertia
restrictions of natural-coefficient Kummer classes over all finite places.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory TopRep

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- The natural `mu_p` representation restricted from decomposition to
absolute inertia at `v`. -/
abbrev finitePlaceAbsoluteInertiaMuPTopRep
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    TopRep (ZMod p) (finitePlaceAbsoluteInertiaSubgroup F v) :=
  TopRep.res
    (finitePlaceAbsoluteInertiaInclusion F v :
      finitePlaceAbsoluteInertiaSubgroup F v →*
        finitePlaceAbsoluteDecompositionGroup F v)
    (finitePlaceAbsoluteMuPTopRep F p v)

/-- The identity coefficient morphism from the literal inertia restriction. -/
abbrev finitePlaceAbsoluteMuPInertiaRestrictionHom
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    TopRep.res
        (finitePlaceAbsoluteInertiaInclusion F v :
          finitePlaceAbsoluteInertiaSubgroup F v →*
            finitePlaceAbsoluteDecompositionGroup F v)
        (finitePlaceAbsoluteMuPTopRep F p v) ⟶
      finitePlaceAbsoluteInertiaMuPTopRep F p v :=
  𝟙 _

/-- Restriction of natural-coefficient degree-one cocycles from decomposition
to inertia. -/
noncomputable abbrev finitePlaceAbsoluteMuPInertiaCocyclesMap
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ContinuousCohomology.cocycles (finitePlaceAbsoluteMuPTopRep F p v) 1 ⟶
      ContinuousCohomology.cocycles
        (finitePlaceAbsoluteInertiaMuPTopRep F p v) 1 :=
  ContinuousCohomology.cocyclesMap
    (finitePlaceAbsoluteInertiaInclusion F v)
    (finitePlaceAbsoluteMuPInertiaRestrictionHom F p v) 1

/-- The categorical restriction on natural-coefficient continuous `H¹`. -/
noncomputable abbrev finitePlaceAbsoluteMuPH1InertiaRestrictionHom
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    continuousCohomology 1 (finitePlaceAbsoluteMuPTopRep F p v) ⟶
      continuousCohomology 1
        (finitePlaceAbsoluteInertiaMuPTopRep F p v) :=
  ContinuousCohomology.map
    (finitePlaceAbsoluteInertiaInclusion F v)
    (finitePlaceAbsoluteMuPInertiaRestrictionHom F p v) 1

/-- Restriction from decomposition to inertia as a `ZMod p`-linear map. -/
noncomputable def finitePlaceAbsoluteMuPH1InertiaRestriction
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    continuousCohomology 1 (finitePlaceAbsoluteMuPTopRep F p v) →ₗ[ZMod p]
      continuousCohomology 1
        (finitePlaceAbsoluteInertiaMuPTopRep F p v) :=
  (finitePlaceAbsoluteMuPH1InertiaRestrictionHom F p v).hom.toLinearMap

/-- Inertia restriction sends a cocycle class to the class of its restricted
cocycle. -/
theorem finitePlaceAbsoluteMuPH1InertiaRestriction_quotientMap
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (z : ContinuousCohomology.cocycles
      (finitePlaceAbsoluteMuPTopRep F p v) 1) :
    finitePlaceAbsoluteMuPH1InertiaRestriction F p v
        (ContinuousCohomology.π
          (finitePlaceAbsoluteMuPTopRep F p v) 1 z) =
      ContinuousCohomology.π
        (finitePlaceAbsoluteInertiaMuPTopRep F p v) 1
        (finitePlaceAbsoluteMuPInertiaCocyclesMap F p v z) := by
  exact ConcreteCategory.congr_hom
    (ContinuousCohomology.π_map
      (finitePlaceAbsoluteInertiaInclusion F v)
      (finitePlaceAbsoluteMuPInertiaRestrictionHom F p v) 1) z

/-- Natural-coefficient classes on decomposition that are unramified at
`v`: those whose inertia restriction vanishes. -/
noncomputable abbrev finitePlaceAbsoluteMuPUnramifiedH1
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Submodule (ZMod p)
      (continuousCohomology 1 (finitePlaceAbsoluteMuPTopRep F p v)) :=
  LinearMap.ker (finitePlaceAbsoluteMuPH1InertiaRestriction F p v)

theorem mem_finitePlaceAbsoluteMuPUnramifiedH1_iff
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (x : continuousCohomology 1 (finitePlaceAbsoluteMuPTopRep F p v)) :
    x ∈ finitePlaceAbsoluteMuPUnramifiedH1 F p v ↔
      finitePlaceAbsoluteMuPH1InertiaRestriction F p v x = 0 :=
  LinearMap.mem_ker

/-- The localized absolute Kummer cocycle restricted further to inertia. -/
noncomputable abbrev finitePlaceAbsoluteKummerMuPInertiaHomogeneousOneCocycle
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : Fˣ) :
    ContinuousCohomology.cocycles
      (finitePlaceAbsoluteInertiaMuPTopRep F p v) 1 :=
  finitePlaceAbsoluteMuPInertiaCocyclesMap F p v
    (finitePlaceAbsoluteKummerMuPHomogeneousOneCocycle F p v a)

/-- The inertia-localized natural-coefficient Kummer `H¹` class. -/
noncomputable def finitePlaceAbsoluteKummerMuPInertiaH1Class
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : Fˣ) :
    continuousCohomology 1
      (finitePlaceAbsoluteInertiaMuPTopRep F p v) :=
  ContinuousCohomology.π
    (finitePlaceAbsoluteInertiaMuPTopRep F p v) 1
    (finitePlaceAbsoluteKummerMuPInertiaHomogeneousOneCocycle F p v a)

/-- Inertia restriction of a localized Kummer class is represented by the
restricted Kummer cocycle. -/
theorem finitePlaceAbsoluteMuPH1InertiaRestriction_kummerClass
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : Fˣ) :
    finitePlaceAbsoluteMuPH1InertiaRestriction F p v
        (finitePlaceAbsoluteKummerMuPH1Class F p v a) =
      finitePlaceAbsoluteKummerMuPInertiaH1Class F p v a :=
  finitePlaceAbsoluteMuPH1InertiaRestriction_quotientMap F p v
    (finitePlaceAbsoluteKummerMuPHomogeneousOneCocycle F p v a)

/-- The ramification component of the natural Kummer map at `v`. -/
noncomputable def finitePlaceAbsoluteKummerMuPH1RamificationLinearMap
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    absolutePowerClassModP F p →ₗ[ZMod p]
      continuousCohomology 1
        (finitePlaceAbsoluteInertiaMuPTopRep F p v) :=
  (finitePlaceAbsoluteMuPH1InertiaRestriction F p v).comp
    (finitePlaceAbsoluteKummerMuPH1LinearMap F p v)

/-- Evaluation on a represented power class is its inertia-localized Kummer
class. -/
@[simp]
theorem finitePlaceAbsoluteKummerMuPH1RamificationLinearMap_mk
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : Fˣ) :
    finitePlaceAbsoluteKummerMuPH1RamificationLinearMap F p v
        (Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom p : Fˣ →* Fˣ).range a)) =
      finitePlaceAbsoluteKummerMuPInertiaH1Class F p v a := by
  change finitePlaceAbsoluteMuPH1InertiaRestriction F p v
      (finitePlaceAbsoluteKummerMuPH1LinearMap F p v
        (Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom p : Fˣ →* Fˣ).range a))) = _
  rw [finitePlaceAbsoluteKummerMuPH1LinearMap_mk,
    finitePlaceAbsoluteMuPH1InertiaRestriction_kummerClass]

/-- The dependent product of natural-coefficient inertia `H¹` spaces. -/
abbrev FinitePlaceMuPH1RamificationLocalizationTarget :=
  (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) →
    continuousCohomology 1
      (finitePlaceAbsoluteInertiaMuPTopRep F p v)

/-- All finite-place inertia components of the natural Kummer map. -/
noncomputable def finitePlaceAbsoluteKummerMuPH1RamificationFamily :
    absolutePowerClassModP F p →ₗ[ZMod p]
      FinitePlaceMuPH1RamificationLocalizationTarget F p :=
  LinearMap.pi fun v ↦
    finitePlaceAbsoluteKummerMuPH1RamificationLinearMap F p v

/-- Each component of the family is the ramification map at that place. -/
@[simp]
theorem finitePlaceAbsoluteKummerMuPH1RamificationFamily_apply
    (x : absolutePowerClassModP F p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteKummerMuPH1RamificationFamily F p x v =
      finitePlaceAbsoluteKummerMuPH1RamificationLinearMap F p v x :=
  rfl

/-- On a represented global power class, the family consists of its
inertia-localized Kummer classes. -/
@[simp]
theorem finitePlaceAbsoluteKummerMuPH1RamificationFamily_mk
    (a : Fˣ) :
    finitePlaceAbsoluteKummerMuPH1RamificationFamily F p
        (Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom p : Fˣ →* Fˣ).range a)) =
      fun v ↦ finitePlaceAbsoluteKummerMuPInertiaH1Class F p v a := by
  funext v
  change finitePlaceAbsoluteKummerMuPH1RamificationLinearMap F p v
      (Additive.ofMul
        (QuotientGroup.mk'
          (powMonoidHom p : Fˣ →* Fˣ).range a)) = _
  rw [finitePlaceAbsoluteKummerMuPH1RamificationLinearMap_mk]

/-- Global power classes whose natural Kummer class is unramified at every
finite place. -/
noncomputable abbrev finitePlaceAbsoluteKummerMuPEverywhereUnramifiedPowerClasses :
    Submodule (ZMod p) (absolutePowerClassModP F p) :=
  LinearMap.ker (finitePlaceAbsoluteKummerMuPH1RamificationFamily F p)

theorem mem_finitePlaceAbsoluteKummerMuPEverywhereUnramifiedPowerClasses_iff
    (x : absolutePowerClassModP F p) :
    x ∈ finitePlaceAbsoluteKummerMuPEverywhereUnramifiedPowerClasses F p ↔
      ∀ v, finitePlaceAbsoluteKummerMuPH1RamificationLinearMap F p v x = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx v
    have hv := congrFun hx v
    exact hv
  · intro hx
    funext v
    exact hx v

end ClassFieldTower.Martinet.Shafarevich
