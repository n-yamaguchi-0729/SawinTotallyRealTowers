import SawinTotallyRealTowers.FinitePlaceFrobenius
import SawinTotallyRealTowers.AbsoluteRealProPUnramified
import ProCGroups.Topologies.QuotientMaps
import ProCGroups.Generation.Basic
import ProCGroups.Topologies.ContinuousMonoidHom
import Mathlib.Algebra.Group.Subgroup.Lattice

set_option autoImplicit false

/-!
# Frobenius in the actual maximal real pro-p extension

Outside the allowed support inertia acts trivially. Consequently the
actual decomposition map factors through its residue-degree quotient;
killing arithmetic Frobenius kills its entire decomposition image.
-/

open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich

variable (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- The actual image of an absolute decomposition element in the maximal real group. -/
def maximalRealProPDecompositionMap :
    finitePlaceAbsoluteDecompositionGroup ℚ v →ₜ*
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) :=
  (absoluteToMaximalRealProPOutside p T).comp
    (finitePlaceAbsoluteDecompositionInclusion ℚ v)

/-- The chosen arithmetic Frobenius as an element of the actual arithmetic group. -/
def maximalRealProPArithmeticFrobenius :
    maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T :=
  maximalRealProPDecompositionMap p T v (finitePlaceArithmeticFrobeniusLift ℚ v)

/-- Outside T the actual decomposition map kills absolute inertia. -/
theorem maximalRealProPDecompositionMap_inertia_ker (hv : v ∉ T) :
    finitePlaceAbsoluteInertiaSubgroup ℚ v ≤
      (maximalRealProPDecompositionMap p T v).toMonoidHom.ker := by
  intro sigma hsigma
  exact absoluteToMaximalRealProPOutside_inertia p T v hv ⟨sigma, hsigma⟩

/-- The actual decomposition map on the quotient by inertia. -/
def maximalRealProPUnramifiedDecompositionMap (hv : v ∉ T) :
    (finitePlaceAbsoluteDecompositionGroup ℚ v ⧸
      finitePlaceAbsoluteInertiaSubgroup ℚ v) →ₜ*
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) :=
  ProCGroups.QuotientGroup.liftₜ (finitePlaceAbsoluteInertiaSubgroup ℚ v)
    (maximalRealProPDecompositionMap p T v)
    (maximalRealProPDecompositionMap_inertia_ker p T v hv)

@[simp]
theorem maximalRealProPUnramifiedDecompositionMap_mk (hv : v ∉ T)
    (sigma : finitePlaceAbsoluteDecompositionGroup ℚ v) :
    maximalRealProPUnramifiedDecompositionMap p T v hv
        (QuotientGroup.mk' (finitePlaceAbsoluteInertiaSubgroup ℚ v) sigma) =
      maximalRealProPDecompositionMap p T v sigma := rfl

/-- The unramified class maps to the same actual arithmetic Frobenius. -/
theorem maximalRealProPFrobenius_eq_classMap (hv : v ∉ T) :
    maximalRealProPArithmeticFrobenius p T v =
      maximalRealProPUnramifiedDecompositionMap p T v hv
        (finitePlaceArithmeticFrobeniusClass ℚ v) := by
  rw [← finitePlaceArithmeticFrobeniusLift_mk ℚ v]
  rfl

/-- Killing Frobenius in any Hausdorff continuous quotient kills the
whole decomposition image, since inertia already acts trivially. -/
theorem maximalRealProPDecomposition_killed_of_frobenius
    (hv : v ∉ T) {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H]
    (q : (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) →ₜ* H)
    (hq : q (maximalRealProPArithmeticFrobenius p T v) = 1)
    (sigma : finitePlaceAbsoluteDecompositionGroup ℚ v) :
    q (maximalRealProPDecompositionMap p T v sigma) = 1 := by
  let f := q.comp (maximalRealProPUnramifiedDecompositionMap p T v hv)
  have hc : finitePlaceArithmeticFrobeniusClass ℚ v ∈ f.toMonoidHom.ker := by
    change q (maximalRealProPUnramifiedDecompositionMap p T v hv
      (finitePlaceArithmeticFrobeniusClass ℚ v)) = 1
    rw [← maximalRealProPFrobenius_eq_classMap p T v hv]
    exact hq
  have hcl : Subgroup.closure {finitePlaceArithmeticFrobeniusClass ℚ v} ≤
      f.toMonoidHom.ker := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    exact (Set.mem_singleton_iff.mp hx) ▸ hc
  have hall : (Subgroup.closure {finitePlaceArithmeticFrobeniusClass ℚ v}).topologicalClosure ≤
      f.toMonoidHom.ker :=
    Subgroup.topologicalClosure_minimal _ hcl (ProCGroups.ContinuousMonoidHom.isClosed_ker f)
  have hgen := finitePlaceArithmeticFrobeniusClass_topologicallyGenerates ℚ v
  change (Subgroup.closure {finitePlaceArithmeticFrobeniusClass ℚ v}).topologicalClosure = ⊤ at hgen
  rw [hgen] at hall
  exact hall (Subgroup.mem_top (QuotientGroup.mk'
    (finitePlaceAbsoluteInertiaSubgroup ℚ v) sigma))

end ClassFieldTower.Sawin
