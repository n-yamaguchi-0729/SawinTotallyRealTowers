import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceInertiaTransport
import GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore
import ProCGroups.Generation.Basic

set_option autoImplicit false

/-!
# Arithmetic Frobenius in an absolute decomposition group

The existing local residue comparison identifies the quotient by inertia
with the profinite integers. The class of arithmetic Frobenius is the
inverse image of additive one, and a representative is chosen in the
actual absolute decomposition group.
-/

open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich ClassFormation
open AlgebraicNumberTheory.Valuations ProCGroups.Generation

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

/-- The unramified absolute decomposition quotient has its actual residue degree. -/
def finitePlaceUnramifiedDegreeEquiv :
    (finitePlaceAbsoluteDecompositionGroup F v ⧸
      finitePlaceAbsoluteInertiaSubgroup F v) ≃ₜ* ZHatMul := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  letI : Valued vF.Completion NNReal := finitePlaceCompletionValued vF hvFna
  letI : ValuativeRel vF.Completion := finitePlaceCompletionValuativeRel vF hvFna
  letI : IsNonarchimedeanLocalField vF.Completion :=
    finitePlaceNormCompletionIsNonarchimedeanLocalField F v
  exact (finitePlaceUnramifiedQuotientContinuousMulEquiv F v).trans
    (localUnramifiedQuotientContinuousMulEquiv vF.Completion)

/-- The residue-degree-one class of arithmetic Frobenius. -/
def finitePlaceArithmeticFrobeniusClass :
    finitePlaceAbsoluteDecompositionGroup F v ⧸ finitePlaceAbsoluteInertiaSubgroup F v :=
  (finitePlaceUnramifiedDegreeEquiv F v).symm (Multiplicative.ofAdd (1 : ZHat))

/-- An actual absolute decomposition element representing arithmetic Frobenius. -/
def finitePlaceArithmeticFrobeniusLift : finitePlaceAbsoluteDecompositionGroup F v :=
  Classical.choose ((QuotientGroup.mk'_surjective (finitePlaceAbsoluteInertiaSubgroup F v))
    (finitePlaceArithmeticFrobeniusClass F v))

@[simp]
theorem finitePlaceArithmeticFrobeniusLift_mk :
    QuotientGroup.mk' (finitePlaceAbsoluteInertiaSubgroup F v)
        (finitePlaceArithmeticFrobeniusLift F v) =
      finitePlaceArithmeticFrobeniusClass F v :=
  Classical.choose_spec ((QuotientGroup.mk'_surjective (finitePlaceAbsoluteInertiaSubgroup F v))
    (finitePlaceArithmeticFrobeniusClass F v))

@[simp]
theorem finitePlaceArithmeticFrobeniusLift_degree :
    finitePlaceUnramifiedDegreeEquiv F v
      (QuotientGroup.mk' (finitePlaceAbsoluteInertiaSubgroup F v)
        (finitePlaceArithmeticFrobeniusLift F v)) = Multiplicative.ofAdd (1 : ZHat) := by
  rw [finitePlaceArithmeticFrobeniusLift_mk]
  exact (finitePlaceUnramifiedDegreeEquiv F v).apply_symm_apply _

/-- The chosen Frobenius class generates the whole unramified decomposition quotient. -/
theorem finitePlaceArithmeticFrobeniusClass_topologicallyGenerates :
    ProCGroups.Generation.TopologicallyGenerates
      ({finitePlaceArithmeticFrobeniusClass F v} :
        Set (finitePlaceAbsoluteDecompositionGroup F v ⧸
          finitePlaceAbsoluteInertiaSubgroup F v)) := by
  let e := finitePlaceUnramifiedDegreeEquiv F v
  let f : ZHatMul →ₜ* (finitePlaceAbsoluteDecompositionGroup F v ⧸
      finitePlaceAbsoluteInertiaSubgroup F v) :=
    { toFun := fun z ↦ e.symm z
      map_one' := e.symm.map_one
      map_mul' := e.symm.map_mul
      continuous_toFun := e.symm.continuous }
  have h := ProCGroups.Generation.topologicallyGenerates_image_of_continuousMonoidHom_surjective
    f e.symm.surjective zHatOne_topologicallyGenerates
  rw [Set.image_singleton] at h
  exact h

end ClassFieldTower.Sawin
