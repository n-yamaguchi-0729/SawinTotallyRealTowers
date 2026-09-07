import GaloisCohomology.ProP.QuotientRestriction
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
import ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup
import ValuedFieldTheory.Valuation.Completion.ExtensionFactorClassification
import Mathlib.FieldTheory.AbsoluteGaloisGroup

set_option autoImplicit false
/-!
# Degree-two localization at a finite place

For a number field and a finite place, the chosen extension of the adic absolute value to the
algebraic closure defines an absolute decomposition subgroup.  Its continuous inclusion in the
absolute Galois group induces the actual restriction map on degree-two continuous cohomology.

This file deliberately stops at the decomposition-group target.  Identifying that target with the
absolute Galois group of the completed field requires a topological local--global Galois comparison
which is not presently available in the imported libraries.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open AlgebraicNumberTheory.Valuations
open ClassFieldTower.Cohomology

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ)

/-- The chosen extension of the finite-place absolute value to the algebraic closure. -/
noncomputable def finitePlaceAbsoluteValueExtension
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) (AlgebraicClosure F) :=
  pullbackAbsoluteValueExtension
    (NumberField.HeightOneSpectrum.adicAbv F v)
    (RayClass.adicAbv_isNontrivial v) IsAlgClosed.lift

/-- The decomposition subgroup of the absolute Galois group selected by a finite place. -/
abbrev finitePlaceAbsoluteDecompositionGroup
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :=
  HilbertRamification.absoluteValueDecompositionGroup F
    (finitePlaceAbsoluteValueExtension F v).1

/-- The continuous inclusion of the selected decomposition subgroup in the absolute Galois group. -/
def finitePlaceAbsoluteDecompositionInclusion
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteDecompositionGroup F v →ₜ* Field.absoluteGaloisGroup F :=
  subgroupInclusion
    (HilbertRamification.absoluteValueDecompositionGroup F
      (finitePlaceAbsoluteValueExtension F v).1)

@[simp]
theorem finitePlaceAbsoluteDecompositionInclusion_apply
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    finitePlaceAbsoluteDecompositionInclusion F v sigma = sigma.1 :=
  rfl

/-- Restriction of degree-two continuous cohomology from the absolute Galois group to the
decomposition subgroup at `v`. -/
noncomputable def finitePlaceH2Localization
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    continuousCohomologyZModPLifted p (Field.absoluteGaloisGroup F) 2 →ₗ[ZMod p]
      continuousCohomologyZModPLifted p
        (finitePlaceAbsoluteDecompositionGroup F v) 2 :=
  (continuousCohomologyZModPMapLifted p
    (finitePlaceAbsoluteDecompositionInclusion F v) 2).hom.toLinearMap

/-- Localization sends a cocycle class to the class of its restriction to the decomposition
subgroup. -/
theorem finitePlaceH2Localization_quotientMap
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (z : trivialZModPCocyclesLifted p (Field.absoluteGaloisGroup F) 2) :
    finitePlaceH2Localization F p v
        (ContinuousCohomology.π (trivialZModPLifted p (Field.absoluteGaloisGroup F)) 2 z) =
      ContinuousCohomology.π
        (trivialZModPLifted p (finitePlaceAbsoluteDecompositionGroup F v)) 2
        (trivialZModPCocyclesMapLifted p
          (finitePlaceAbsoluteDecompositionInclusion F v) 2 z) := by
  exact ConcreteCategory.congr_hom
    (trivialZModPLifted_π_naturality p
      (finitePlaceAbsoluteDecompositionInclusion F v) 2) z

end ClassFieldTower.Martinet.Shafarevich
