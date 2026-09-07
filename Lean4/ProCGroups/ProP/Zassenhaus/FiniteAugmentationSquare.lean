import ProCGroups.ProP.FrattiniPowers
import ProCGroups.ProP.Zassenhaus.FiniteLinearization
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.Abel

set_option autoImplicit false
/-!
# The augmentation-square subgroup at a finite stage

This file packages the ordinary group elements for which `[q]-1` belongs to
the square of the mod-`p` augmentation ideal.  Direct group-algebra identities
show that this subgroup contains all `p`-th powers and commutators.
-/

open scoped commutatorElement

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra

noncomputable section

universe u

variable (p : ℕ)
variable (Q : Type u) [Group Q]

/-- Multiplication formula for ordinary augmentation generators. -/
theorem groupAlgebraAugmentationGenerator_mul (a b : Q) :
    groupAlgebraAugmentationGenerator (ZMod p) Q (a * b) =
      groupAlgebraAugmentationGenerator (ZMod p) Q a +
        groupAlgebraAugmentationGenerator (ZMod p) Q b +
          groupAlgebraAugmentationGenerator (ZMod p) Q a *
            groupAlgebraAugmentationGenerator (ZMod p) Q b := by
  simp only [groupAlgebraAugmentationGenerator, map_mul]
  simp only [sub_mul, mul_sub, mul_one, one_mul]
  abel

/-- Inversion formula for ordinary augmentation generators. -/
theorem groupAlgebraAugmentationGenerator_inv (a : Q) :
    groupAlgebraAugmentationGenerator (ZMod p) Q a⁻¹ =
      -MonoidAlgebra.of (ZMod p) Q a⁻¹ *
        groupAlgebraAugmentationGenerator (ZMod p) Q a := by
  simp only [groupAlgebraAugmentationGenerator]
  have hu :
      MonoidAlgebra.of (ZMod p) Q a⁻¹ * MonoidAlgebra.of (ZMod p) Q a = 1 := by
    rw [← map_mul, inv_mul_cancel]
    exact MonoidAlgebra.one_def.symm
  calc
    MonoidAlgebra.of (ZMod p) Q a⁻¹ - 1 =
        MonoidAlgebra.of (ZMod p) Q a⁻¹ -
          MonoidAlgebra.of (ZMod p) Q a⁻¹ * MonoidAlgebra.of (ZMod p) Q a := by
            rw [hu]
    _ = -MonoidAlgebra.of (ZMod p) Q a⁻¹ *
          (MonoidAlgebra.of (ZMod p) Q a - 1) := by
      rw [mul_sub, neg_mul, neg_mul, mul_one, hu]
      abel

/-- Ordinary group-like elements preserve natural powers. -/
theorem groupAlgebraOf_pow (a : Q) (n : ℕ) :
    MonoidAlgebra.of (ZMod p) Q (a ^ n) = MonoidAlgebra.of (ZMod p) Q a ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonoidAlgebra.of_apply, ← MonoidAlgebra.one_def]
  | succ n ih => rw [pow_succ, pow_succ, map_mul, ih]

/-- In characteristic `p`, the augmentation generator of `a^p` is the `p`-th
power of the augmentation generator of `a`. -/
theorem groupAlgebraAugmentationGenerator_pow_prime [Fact p.Prime] (a : Q) :
    groupAlgebraAugmentationGenerator (ZMod p) Q (a ^ p) =
      groupAlgebraAugmentationGenerator (ZMod p) Q a ^ p := by
  let _ : CharP (MonoidAlgebra (ZMod p) Q) p :=
    charP_of_injective_algebraMap
      (R := ZMod p) (A := MonoidAlgebra (ZMod p) Q) (by
        intro r s hrs
        have h := congrArg (groupAlgebraAugmentation (ZMod p) Q) hrs
        simpa only [groupAlgebraAugmentation_algebraMap] using h) p
  change MonoidAlgebra.of (ZMod p) Q (a ^ p) - 1 =
    (MonoidAlgebra.of (ZMod p) Q a - 1) ^ p
  rw [groupAlgebraOf_pow]
  simpa only [one_pow] using
    (sub_pow_char_of_commute p
      (Commute.one_right (MonoidAlgebra.of (ZMod p) Q a))).symm

section AugmentationSquare

local instance : (groupAlgebraAugmentationIdeal (ZMod p) Q).IsTwoSided := by
  change (RingHom.ker (groupAlgebraAugmentation (ZMod p) Q)).IsTwoSided
  infer_instance

private theorem augmentationGenerator_mul_mem_sq (a b : Q) :
    groupAlgebraAugmentationGenerator (ZMod p) Q a *
        groupAlgebraAugmentationGenerator (ZMod p) Q b ∈
      (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2 := by
  have hmul :
      groupAlgebraAugmentationGenerator (ZMod p) Q a *
          groupAlgebraAugmentationGenerator (ZMod p) Q b ∈
        groupAlgebraAugmentationIdeal (ZMod p) Q *
          groupAlgebraAugmentationIdeal (ZMod p) Q :=
    Ideal.mul_mem_mul
      (groupAlgebraAugmentationGenerator_mem_augmentationIdeal (ZMod p) Q a)
      (groupAlgebraAugmentationGenerator_mem_augmentationIdeal (ZMod p) Q b)
  rw [show (2 : ℕ) = 1 + 1 by rfl, Ideal.IsTwoSided.pow_add,
    Submodule.pow_one]
  exact hmul

/-- Group elements whose standard augmentation generator lies in `I²`. -/
def augmentationSquareSubgroup : Subgroup Q where
  carrier := {q | groupAlgebraAugmentationGenerator (ZMod p) Q q ∈
    (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2}
  one_mem' := by
    change groupAlgebraAugmentationGenerator (ZMod p) Q 1 ∈
      (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2
    simp only [groupAlgebraAugmentationGenerator, MonoidAlgebra.of_apply,
      ← MonoidAlgebra.one_def, sub_self]
    exact ((groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2).zero_mem
  mul_mem' := by
    intro a b ha hb
    change groupAlgebraAugmentationGenerator (ZMod p) Q a ∈
      (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2 at ha
    change groupAlgebraAugmentationGenerator (ZMod p) Q b ∈
      (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2 at hb
    change groupAlgebraAugmentationGenerator (ZMod p) Q (a * b) ∈
      (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2
    rw [groupAlgebraAugmentationGenerator_mul]
    exact ((groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2).add_mem
      (((groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2).add_mem ha hb)
      (augmentationGenerator_mul_mem_sq p Q a b)
  inv_mem' := by
    intro a ha
    change groupAlgebraAugmentationGenerator (ZMod p) Q a ∈
      (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2 at ha
    change groupAlgebraAugmentationGenerator (ZMod p) Q a⁻¹ ∈
      (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2
    rw [groupAlgebraAugmentationGenerator_inv]
    exact ((groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2).mul_mem_left _ ha

/-- The subgroup generated by `p`-th powers lies in the augmentation-square subgroup. -/
theorem powerSubgroup_le_augmentationSquareSubgroup [Fact p.Prime] :
    powerSubgroup p Q ≤ augmentationSquareSubgroup p Q := by
  rw [powerSubgroup, Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  change groupAlgebraAugmentationGenerator (ZMod p) Q (a ^ p) ∈
    (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2
  rw [groupAlgebraAugmentationGenerator_pow_prime]
  exact Ideal.pow_le_pow_right ((Fact.out : Nat.Prime p).two_le)
    (Ideal.pow_mem_pow
      (groupAlgebraAugmentationGenerator_mem_augmentationIdeal (ZMod p) Q a) p)

private theorem groupAlgebraCommutatorDifference_identity
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

/-- A group commutator has augmentation generator in the square ideal. -/
theorem groupAlgebraAugmentationGenerator_commutator (a b : Q) :
    groupAlgebraAugmentationGenerator (ZMod p) Q ⁅a, b⁆ =
      (groupAlgebraAugmentationGenerator (ZMod p) Q a *
          groupAlgebraAugmentationGenerator (ZMod p) Q b -
        groupAlgebraAugmentationGenerator (ZMod p) Q b *
          groupAlgebraAugmentationGenerator (ZMod p) Q a) *
        MonoidAlgebra.of (ZMod p) Q a⁻¹ * MonoidAlgebra.of (ZMod p) Q b⁻¹ := by
  have haInv : MonoidAlgebra.of (ZMod p) Q a *
      MonoidAlgebra.of (ZMod p) Q a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel]
    exact MonoidAlgebra.one_def.symm
  have hbInv : MonoidAlgebra.of (ZMod p) Q b *
      MonoidAlgebra.of (ZMod p) Q b⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel]
    exact MonoidAlgebra.one_def.symm
  simpa only [groupAlgebraAugmentationGenerator, commutatorElement_def, map_mul] using
    groupAlgebraCommutatorDifference_identity
      (MonoidAlgebra.of (ZMod p) Q a) (MonoidAlgebra.of (ZMod p) Q b)
      (MonoidAlgebra.of (ZMod p) Q a⁻¹) (MonoidAlgebra.of (ZMod p) Q b⁻¹)
      haInv hbInv

/-- The commutator subgroup lies in the augmentation-square subgroup. -/
theorem commutator_le_augmentationSquareSubgroup :
    commutator Q ≤ augmentationSquareSubgroup p Q := by
  change ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ augmentationSquareSubgroup p Q
  rw [Subgroup.commutator_le]
  intro a _ b _
  change groupAlgebraAugmentationGenerator (ZMod p) Q ⁅a, b⁆ ∈
    (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2
  rw [groupAlgebraAugmentationGenerator_commutator]
  have hab := augmentationGenerator_mul_mem_sq p Q a b
  have hba := augmentationGenerator_mul_mem_sq p Q b a
  have hsub := ((groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2).sub_mem hab hba
  exact ((groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2).mul_mem_right _
    (((groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2).mul_mem_right _ hsub)

end AugmentationSquare

end


end ClassFieldTower.ProP
