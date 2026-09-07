import ProCGroups.ProP.Zassenhaus.AugmentationFiltration
import Mathlib.Tactic.Abel

set_option autoImplicit false
/-!
# Group-like differences in the mod-`p` completed group algebra

The element `[g] - 1` translates multiplication, inversion, commutators, and
`p`-th powers in a group into augmentation-filtration identities.  Keeping
these calculations in one leaf prevents later filtration proofs from
re-elaborating large noncommutative ring expressions.
-/

open scoped Topology commutatorElement

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra

noncomputable section

universe u

variable (p : ℕ) [Fact p.Prime]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The standard completed group-like difference `[g] - 1`. -/
def groupLikeDifference (g : G) : ModPCompletedGroupAlgebra p G :=
  completedGroupAlgebraOfInClass
    (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g - 1

/-- Every group-like difference lies in the augmentation ideal. -/
theorem groupLikeDifference_mem_augmentationIdeal (g : G) :
    groupLikeDifference p G g ∈ modPAugmentationIdeal p G := by
  rw [CompletedGroupAlgebra.mem_completedGroupAlgebraCanonicalAugmentationIdealInClass_iff]
  simp [groupLikeDifference]

@[simp] theorem groupLikeDifference_one : groupLikeDifference p G 1 = 0 := by
  simp [groupLikeDifference]

/-- The group-like-difference map is continuous. -/
theorem continuous_groupLikeDifference : Continuous (groupLikeDifference p G) := by
  exact (CompletedGroupAlgebra.continuous_completedGroupAlgebraOfInClass
    (R := ZMod p) (G := G)
    (ProCGroups.FiniteGroupClass.pGroup p)).sub continuous_const

/-- First-order multiplication formula for group-like differences. -/
theorem groupLikeDifference_mul (g h : G) :
    groupLikeDifference p G (g * h) =
      groupLikeDifference p G g + groupLikeDifference p G h +
        groupLikeDifference p G g * groupLikeDifference p G h := by
  simp only [groupLikeDifference, completedGroupAlgebraOfInClass_mul]
  simp only [sub_mul, mul_sub, mul_one, one_mul]
  abel

/-- Inversion formula for a group-like difference. -/
theorem groupLikeDifference_inv (g : G) :
    groupLikeDifference p G g⁻¹ =
      -completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g⁻¹ *
        groupLikeDifference p G g := by
  simp only [groupLikeDifference]
  have hu :
      completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g⁻¹ *
          completedGroupAlgebraOfInClass
            (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g = 1 := by
    rw [← completedGroupAlgebraOfInClass_mul]
    simp
  calc
    completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g⁻¹ - 1 =
        completedGroupAlgebraOfInClass
            (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g⁻¹ -
          completedGroupAlgebraOfInClass
              (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g⁻¹ *
            completedGroupAlgebraOfInClass
              (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g := by rw [hu]
    _ = -completedGroupAlgebraOfInClass
            (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g⁻¹ *
          (completedGroupAlgebraOfInClass
              (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g - 1) := by
      rw [mul_sub, neg_mul, neg_mul, mul_one, hu]
      abel

/-- A ring identity underlying the commutator filtration calculation. -/
theorem commutatorDifference_identity
    {R : Type*} [Ring R] (a b ai bi : R)
    (hai : a * ai = 1) (hbi : b * bi = 1) :
    a * b * ai * bi - 1 =
      ((a - 1) * (b - 1) - (b - 1) * (a - 1)) * ai * bi := by
  have hdiff : (a - 1) * (b - 1) - (b - 1) * (a - 1) = a * b - b * a := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]
    abel
  rw [hdiff]
  simp only [sub_mul]
  rw [mul_assoc b a ai, hai, mul_one, hbi]

/-- A group commutator becomes a difference of quadratic augmentation terms,
up to multiplication by group-like units. -/
theorem groupLikeDifference_commutator (g h : G) :
    groupLikeDifference p G ⁅g, h⁆ =
      (groupLikeDifference p G g * groupLikeDifference p G h -
        groupLikeDifference p G h * groupLikeDifference p G g) *
        completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g⁻¹ *
        completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G h⁻¹ := by
  have hgInv :
      completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g *
          completedGroupAlgebraOfInClass
            (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g⁻¹ = 1 := by
    rw [← completedGroupAlgebraOfInClass_mul]
    simp
  have hhInv :
      completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G h *
          completedGroupAlgebraOfInClass
            (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G h⁻¹ = 1 := by
    rw [← completedGroupAlgebraOfInClass_mul]
    simp
  simpa only [groupLikeDifference, commutatorElement_def,
    completedGroupAlgebraOfInClass_mul] using
      commutatorDifference_identity
        (completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g)
        (completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G h)
        (completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g⁻¹)
        (completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G h⁻¹)
        hgInv hhInv

/-- Completed group-like elements preserve natural powers. -/
theorem completedGroupAlgebraOfInClass_pow (g : G) (n : ℕ) :
    completedGroupAlgebraOfInClass
        (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G (g ^ n) =
      completedGroupAlgebraOfInClass
        (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, completedGroupAlgebraOfInClass_mul, ih]

/-- In characteristic `p`, the difference of a `p`-th power is the `p`-th
power of the difference. -/
theorem groupLikeDifference_pow_prime (g : G) :
    groupLikeDifference p G (g ^ p) = groupLikeDifference p G g ^ p := by
  let _ : CharP (ModPCompletedGroupAlgebra p G) p :=
    modPCompletedGroupAlgebraCharP p G
  change
    completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G (g ^ p) - 1 =
      (completedGroupAlgebraOfInClass
          (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g - 1) ^ p
  rw [completedGroupAlgebraOfInClass_pow]
  simpa only [one_pow] using
    (sub_pow_char_of_commute p (Commute.one_right
      (completedGroupAlgebraOfInClass
        (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G g))).symm

end

end ClassFieldTower.ProP
