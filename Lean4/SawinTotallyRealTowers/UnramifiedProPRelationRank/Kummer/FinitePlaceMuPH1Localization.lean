/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPKummerLinear
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

set_option autoImplicit false
/-!
# Finite-place restriction of natural `mu_p` Kummer classes

The natural `mu_p` representation of the absolute Galois group restricts to each chosen
finite-place decomposition subgroup.  This file packages the induced map on continuous `H¹`
and composes it with the linear Kummer map from global power classes.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory TopRep

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- The natural `mu_p` representation restricted to the chosen decomposition subgroup at `v`. -/
abbrev finitePlaceAbsoluteMuPTopRep
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    TopRep (ZMod p) (finitePlaceAbsoluteDecompositionGroup F v) :=
  TopRep.res
    (finitePlaceAbsoluteDecompositionInclusion F v :
      finitePlaceAbsoluteDecompositionGroup F v →*
        Field.absoluteGaloisGroup F)
    (absoluteMuPTopRep F p)

/-- The identity coefficient morphism from the literal restricted representation. -/
abbrev finitePlaceAbsoluteMuPRestrictionHom
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    TopRep.res
        (finitePlaceAbsoluteDecompositionInclusion F v :
          finitePlaceAbsoluteDecompositionGroup F v →*
            Field.absoluteGaloisGroup F)
        (absoluteMuPTopRep F p) ⟶
      finitePlaceAbsoluteMuPTopRep F p v :=
  𝟙 _

/-- Restriction of natural-coefficient degree-one cocycles. -/
noncomputable abbrev finitePlaceAbsoluteMuPCocyclesMap
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ContinuousCohomology.cocycles (absoluteMuPTopRep F p) 1 ⟶
      ContinuousCohomology.cocycles (finitePlaceAbsoluteMuPTopRep F p v) 1 :=
  ContinuousCohomology.cocyclesMap
    (finitePlaceAbsoluteDecompositionInclusion F v)
    (finitePlaceAbsoluteMuPRestrictionHom F p v) 1

/-- Restriction of natural-coefficient continuous `H¹` to the decomposition subgroup. -/
noncomputable abbrev finitePlaceAbsoluteMuPH1RestrictionHom
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    continuousCohomology 1 (absoluteMuPTopRep F p) ⟶
      continuousCohomology 1 (finitePlaceAbsoluteMuPTopRep F p v) :=
  ContinuousCohomology.map
    (finitePlaceAbsoluteDecompositionInclusion F v)
    (finitePlaceAbsoluteMuPRestrictionHom F p v) 1

/-- Restriction of natural-coefficient continuous `H¹`, viewed as a `ZMod p`-linear map. -/
noncomputable def finitePlaceAbsoluteMuPH1Restriction
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    continuousCohomology 1 (absoluteMuPTopRep F p) →ₗ[ZMod p]
      continuousCohomology 1 (finitePlaceAbsoluteMuPTopRep F p v) :=
  (finitePlaceAbsoluteMuPH1RestrictionHom F p v).hom.toLinearMap

/-- Restriction sends a cocycle class to the class of its restricted cocycle. -/
theorem finitePlaceAbsoluteMuPH1Restriction_quotientMap
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (z : ContinuousCohomology.cocycles (absoluteMuPTopRep F p) 1) :
    finitePlaceAbsoluteMuPH1Restriction F p v
        (ContinuousCohomology.π (absoluteMuPTopRep F p) 1 z) =
      ContinuousCohomology.π (finitePlaceAbsoluteMuPTopRep F p v) 1
        (finitePlaceAbsoluteMuPCocyclesMap F p v z) := by
  exact ConcreteCategory.congr_hom
    (ContinuousCohomology.π_map
      (finitePlaceAbsoluteDecompositionInclusion F v)
      (finitePlaceAbsoluteMuPRestrictionHom F p v) 1) z

/-- The absolute Kummer cocycle restricted to the decomposition subgroup at `v`. -/
noncomputable abbrev finitePlaceAbsoluteKummerMuPHomogeneousOneCocycle
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : Fˣ) :
    ContinuousCohomology.cocycles (finitePlaceAbsoluteMuPTopRep F p v) 1 :=
  finitePlaceAbsoluteMuPCocyclesMap F p v
    (absoluteKummerMuPHomogeneousOneCocycle F p a)

/-- The natural-coefficient Kummer `H¹` class localized at the decomposition subgroup. -/
noncomputable def finitePlaceAbsoluteKummerMuPH1Class
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : Fˣ) :
    continuousCohomology 1 (finitePlaceAbsoluteMuPTopRep F p v) :=
  ContinuousCohomology.π (finitePlaceAbsoluteMuPTopRep F p v) 1
    (finitePlaceAbsoluteKummerMuPHomogeneousOneCocycle F p v a)

/-- Localization of the absolute Kummer class is its restricted cocycle class. -/
theorem finitePlaceAbsoluteMuPH1Restriction_absoluteKummerMuPH1Class
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : Fˣ) :
    finitePlaceAbsoluteMuPH1Restriction F p v
        (absoluteKummerMuPH1Class F p a) =
      finitePlaceAbsoluteKummerMuPH1Class F p v a :=
  finitePlaceAbsoluteMuPH1Restriction_quotientMap F p v
    (absoluteKummerMuPHomogeneousOneCocycle F p a)

/-- Natural-coefficient Kummer localization as a linear map from global power classes. -/
noncomputable def finitePlaceAbsoluteKummerMuPH1LinearMap
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    absolutePowerClassModP F p →ₗ[ZMod p]
      continuousCohomology 1 (finitePlaceAbsoluteMuPTopRep F p v) :=
  (finitePlaceAbsoluteMuPH1Restriction F p v).comp
    (absoluteKummerMuPH1LinearMap F p)

/-- Evaluation on a represented power class is the localized natural Kummer class. -/
@[simp]
theorem finitePlaceAbsoluteKummerMuPH1LinearMap_mk
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : Fˣ) :
    finitePlaceAbsoluteKummerMuPH1LinearMap F p v
        (Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom p : Fˣ →* Fˣ).range a)) =
      finitePlaceAbsoluteKummerMuPH1Class F p v a := by
  change finitePlaceAbsoluteMuPH1Restriction F p v
      (absoluteKummerMuPH1LinearMap F p
        (Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom p : Fˣ →* Fˣ).range a))) = _
  rw [absoluteKummerMuPH1LinearMap_mk,
    finitePlaceAbsoluteMuPH1Restriction_absoluteKummerMuPH1Class]

end ClassFieldTower.Martinet.Shafarevich
