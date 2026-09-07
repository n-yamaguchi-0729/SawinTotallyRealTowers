import Mathlib.Algebra.TrivSqZeroExt.Basic
import ProCGroups.CompletedGroupAlgebra.ProfiniteModules.FiniteGroupAlgebra.Augmentation.Abstract

set_option autoImplicit false
/-!
# First-order characters of an ordinary group algebra

An additive `ZMod p` character defines a group-algebra map into the dual
numbers.  Its square-zero coordinate detects degree one, so the square of the
augmentation ideal is annihilated.  This is the separation mechanism used in
the reverse degree-two Zassenhaus inclusion.
-/

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra

noncomputable section

universe u

variable (p : ℕ)
variable (Q : Type u) [Group Q]

/-- An additive character as the square-zero coordinate of a multiplicative unit. -/
def characterLinearizationMonoidHom (χ : Additive Q →+ ZMod p) :
    Q →* TrivSqZeroExt (ZMod p) (ZMod p) where
  toFun q :=
    TrivSqZeroExt.inl (M := ZMod p) 1 +
      TrivSqZeroExt.inr (R := ZMod p) (χ (Additive.ofMul q))
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp
  map_mul' := by
    intro a b
    apply TrivSqZeroExt.ext
    · simp
    · simp [add_comm]

/-- The group-algebra map recording augmentation and a character to first order. -/
def characterLinearization (χ : Additive Q →+ ZMod p) :
    MonoidAlgebra (ZMod p) Q →ₐ[ZMod p]
      TrivSqZeroExt (ZMod p) (ZMod p) :=
  (MonoidAlgebra.lift (ZMod p)
    (TrivSqZeroExt (ZMod p) (ZMod p)) Q)
    (characterLinearizationMonoidHom p Q χ)

/-- The first coordinate of character linearization is augmentation. -/
theorem characterLinearization_fst (χ : Additive Q →+ ZMod p)
    (x : MonoidAlgebra (ZMod p) Q) :
    (characterLinearization p Q χ x).fst =
      groupAlgebraAugmentation (ZMod p) Q x := by
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      (characterLinearization p Q χ x).fst =
        groupAlgebraAugmentation (ZMod p) Q x) x ?_ ?_ ?_
  · intro q
    rw [characterLinearization, MonoidAlgebra.lift_of,
      groupAlgebraAugmentation_of]
    change
      (TrivSqZeroExt.inl (M := ZMod p) 1 +
        TrivSqZeroExt.inr (R := ZMod p) (χ (Additive.ofMul q))).fst = 1
    simp only [TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
  · intro a b ha hb
    simp [ha, hb]
  · intro r a ha
    rw [map_smul]
    change r • (characterLinearization p Q χ a).fst =
      groupAlgebraAugmentation (ZMod p) Q (r • a)
    rw [ha]
    exact (map_smul (groupAlgebraAugmentationLinearMap (ZMod p) Q) r a).symm

/-- On the augmentation ideal, character linearization has only its
square-zero coordinate. -/
theorem characterLinearization_eq_inr_of_mem_augmentationIdeal
    (χ : Additive Q →+ ZMod p) {x : MonoidAlgebra (ZMod p) Q}
    (hx : x ∈ groupAlgebraAugmentationIdeal (ZMod p) Q) :
    characterLinearization p Q χ x =
      TrivSqZeroExt.inr (characterLinearization p Q χ x).snd := by
  apply TrivSqZeroExt.ext
  · rw [characterLinearization_fst]
    exact hx
  · rfl

/-- The product of two augmentation-ideal elements is killed by character
linearization. -/
theorem characterLinearization_mul_eq_zero_of_mem_augmentationIdeal
    (χ : Additive Q →+ ZMod p) {x y : MonoidAlgebra (ZMod p) Q}
    (hx : x ∈ groupAlgebraAugmentationIdeal (ZMod p) Q)
    (hy : y ∈ groupAlgebraAugmentationIdeal (ZMod p) Q) :
    characterLinearization p Q χ (x * y) = 0 := by
  rw [map_mul,
    characterLinearization_eq_inr_of_mem_augmentationIdeal p Q χ hx,
    characterLinearization_eq_inr_of_mem_augmentationIdeal p Q χ hy,
    TrivSqZeroExt.inr_mul_inr]

/-- Character linearization annihilates the square of the augmentation ideal. -/
theorem characterLinearization_eq_zero_of_mem_augmentationIdeal_sq
    (χ : Additive Q →+ ZMod p) {x : MonoidAlgebra (ZMod p) Q}
    (hx : x ∈ (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2) :
    characterLinearization p Q χ x = 0 := by
  let : (groupAlgebraAugmentationIdeal (ZMod p) Q).IsTwoSided := by
    change (RingHom.ker (groupAlgebraAugmentation (ZMod p) Q)).IsTwoSided
    infer_instance
  have hxmul : x ∈ groupAlgebraAugmentationIdeal (ZMod p) Q *
      groupAlgebraAugmentationIdeal (ZMod p) Q := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, Ideal.IsTwoSided.pow_add,
      Submodule.pow_one] at hx
    exact hx
  refine Submodule.mul_induction_on hxmul ?_ ?_
  · intro a ha b hb
    exact characterLinearization_mul_eq_zero_of_mem_augmentationIdeal p Q χ ha hb
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

/-- If `[q]-1` lies in the augmentation square, every additive character
vanishes on `q`. -/
theorem character_eq_zero_of_generator_mem_augmentationIdeal_sq
    (χ : Additive Q →+ ZMod p) (q : Q)
    (hq : groupAlgebraAugmentationGenerator (ZMod p) Q q ∈
      (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2) :
    χ (Additive.ofMul q) = 0 := by
  have hzero := characterLinearization_eq_zero_of_mem_augmentationIdeal_sq p Q χ hq
  have hsnd := congrArg TrivSqZeroExt.snd hzero
  rw [groupAlgebraAugmentationGenerator, map_sub, map_one,
    TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_one, sub_zero,
    characterLinearization, MonoidAlgebra.lift_of] at hsnd
  change
    (TrivSqZeroExt.inl (M := ZMod p) 1 +
      TrivSqZeroExt.inr (R := ZMod p) (χ (Additive.ofMul q))).snd =
        (0 : TrivSqZeroExt (ZMod p) (ZMod p)).snd at hsnd
  simpa only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero, zero_add] using hsnd

end


end ClassFieldTower.ProP
