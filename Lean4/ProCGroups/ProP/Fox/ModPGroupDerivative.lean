import ProCGroups.ProP.Fox.CoefficientReductionCompatibility
import ProCGroups.ProP.Fox.Derivative

set_option autoImplicit false
/-!
# Mod-p Fox derivatives on finite pro-p presentation groups

Reducing every coordinate of the integral completed Fox derivative modulo `p`
gives a continuous crossed homomorphism into the mod-`p` completed group
algebra coordinates.  Its coefficient is the completed group-like element of
the presentation quotient.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open FoxDifferential
open ProCGroups

noncomputable section

universe u

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Mod-`p` completed Fox-coordinate vectors for the chosen finite basis. -/
abbrev PresentationModPFoxCoordinates :=
  ULift.{u} (Fin d) → ModPCompletedGroupAlgebra p G

/-- The mod-`p` group-like coefficient attached to the presentation quotient. -/
def presentationModPFoxCoefficient
    (P : FiniteProPPresentation p d r sourceData G) :
    sourceData.carrier →* ModPCompletedGroupAlgebra p G :=
  (modPCoefficientReduction p G).toMonoidHom.comp
    (zcCompletedGroupAlgebraScalar
      (FiniteGroupClass.pGroup p) P.quotient.toMonoidHom)

/-- The mod-`p` coefficient is the completed group-like element of the
presentation quotient. -/
@[simp]
theorem presentationModPFoxCoefficient_apply
    (P : FiniteProPPresentation p d r sourceData G)
    (f : sourceData.carrier) :
    presentationModPFoxCoefficient P f =
      completedGroupAlgebraOfInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G (P.quotient f) := by
  change modPCoefficientReduction p G
      (zcCompletedGroupAlgebraScalar
        (FiniteGroupClass.pGroup p) P.quotient.toMonoidHom f) = _
  rw [zcCompletedGroupAlgebraScalar_apply,
    modPCoefficientReduction_groupLike]
  rfl

/-- The presentation Fox derivative with every coordinate reduced modulo
`p`, bundled with its crossed-product law. -/
def presentationModPFoxDerivative
    (P : FiniteProPPresentation p d r sourceData G) :
    ScalarCrossedHom
      (presentationModPFoxCoefficient P)
      (PresentationModPFoxCoordinates (p := p) (d := d) (G := G)) where
  toFun f i :=
    modPCoefficientReduction p G (presentationFoxDerivative P f i)
  map_mul' f g := by
    funext i
    change modPCoefficientReduction p G
        (presentationFoxDerivative P (f * g) i) =
      modPCoefficientReduction p G (presentationFoxDerivative P f i) +
        presentationModPFoxCoefficient P f *
          modPCoefficientReduction p G (presentationFoxDerivative P g i)
    rw [ScalarCrossedHom.map_mul]
    simp only [Pi.add_apply, Pi.smul_apply, map_add, map_mul, smul_eq_mul]
    rfl

/-- Evaluation of a mod-`p` Fox coordinate is coefficient reduction of the
corresponding integral coordinate. -/
@[simp]
theorem presentationModPFoxDerivative_apply
    (P : FiniteProPPresentation p d r sourceData G)
    (f : sourceData.carrier) (i : ULift.{u} (Fin d)) :
    presentationModPFoxDerivative P f i =
      modPCoefficientReduction p G (presentationFoxDerivative P f i) :=
  rfl

/-- The coordinatewise mod-`p` presentation Fox derivative is continuous. -/
theorem continuous_presentationModPFoxDerivative
    (P : FiniteProPPresentation p d r sourceData G) :
    Continuous (presentationModPFoxDerivative P) := by
  apply continuous_pi
  intro i
  exact (continuous_modPCoefficientReduction p G).comp
    ((continuous_apply i).comp (continuous_presentationFoxDerivative P))

/-- The crossed-product law written with the presentation quotient's mod-`p`
group-like coefficient. -/
theorem presentationModPFoxDerivative_mul
    (P : FiniteProPPresentation p d r sourceData G)
    (f g : sourceData.carrier) :
    presentationModPFoxDerivative P (f * g) =
      presentationModPFoxDerivative P f +
        completedGroupAlgebraOfInClass
            (FiniteGroupClass.pGroup p) (ZMod p) G (P.quotient f) •
          presentationModPFoxDerivative P g := by
  rw [ScalarCrossedHom.map_mul,
    presentationModPFoxCoefficient_apply]

end

end ClassFieldTower.ProP
