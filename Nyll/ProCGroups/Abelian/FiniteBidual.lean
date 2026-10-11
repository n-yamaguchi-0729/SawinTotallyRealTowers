/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Duality
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# The actual evaluation map into the Pontryagin double dual

Evaluation is continuous for compact groups. For finite discrete abelian
groups it is an isomorphism: finite character separation gives injectivity,
and the finite dual cardinality theorem gives surjectivity.
-/

noncomputable section

namespace ProCGroups.Duality

universe u

variable (G : Type u) [CommGroup G] [TopologicalSpace G] [CompactSpace G]

/-- Evaluation of actual circle-valued continuous characters. -/
def bidualEvaluation : G →ₜ* PontryaginDual (PontryaginDual G) where
  toFun g :=
    { toFun := fun χ => χ g
      map_one' := rfl
      map_mul' _ _ := rfl
      continuous_toFun := continuous_of_discreteTopology }
  map_one' := PontryaginDual.ext fun χ => map_one χ
  map_mul' g h := PontryaginDual.ext fun χ => map_mul χ g h
  continuous_toFun := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact (continuous_eval : Continuous
      (fun p : (G →ₜ* Circle) × G => p.1 p.2)).comp continuous_swap

/-- Evaluation on a character is its value at the original group element. -/
theorem bidualEvaluation_apply (g : G) (χ : PontryaginDual G) :
    bidualEvaluation G g χ = χ g := rfl

variable [Finite G] [DiscreteTopology G]

omit [CompactSpace G] in
/-- Finite circle-valued characters separate group elements. -/
theorem finite_characters_separate {x y : G}
    (h : ∀ χ : PontryaginDual G, χ x = χ y) : x = y := by
  have hzero : (Additive.ofMul (x / y) : Additive G) = 0 := by
    apply AddChar.forall_apply_eq_zero.mp
    intro ψ
    let ψc : AddChar (Additive G) Circle := AddChar.circleEquivComplex.symm ψ
    let χ : PontryaginDual G := (dualGroupEquivAddCharCircle G).symm ψc
    have hv : χ (x / y) = 1 := by
      rw [map_div, h χ]
      exact div_self' (χ y)
    have hc : ψc (Additive.ofMul (x / y)) = 1 := hv
    exact (congrArg (fun θ : AddChar (Additive G) ℂ => θ (Additive.ofMul (x / y)))
      (AddChar.circleEquivComplex.apply_symm_apply ψ)).symm.trans
        (congrArg (fun z : Circle => (z : ℂ)) hc)
  exact div_eq_one.mp (congrArg Additive.toMul hzero)

/-- The actual evaluation map for a finite discrete abelian group is bijective. -/
theorem finite_bidualEvaluation_bijective : Function.Bijective (bidualEvaluation G) := by
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · intro x y h
    apply finite_characters_separate G
    intro χ
    exact congrArg (fun η : PontryaginDual (PontryaginDual G) => η χ) h
  · exact ((card_dualGroup_eq_card_of_finite_discrete (PontryaginDual G)).trans
      (card_dualGroup_eq_card_of_finite_discrete G)).symm

/-- A finite discrete abelian group is canonically its actual Pontryagin double dual. -/
def finiteBidualEquiv : G ≃ₜ* PontryaginDual (PontryaginDual G) where
  toMulEquiv := MulEquiv.ofBijective (bidualEvaluation G).toMonoidHom
    (finite_bidualEvaluation_bijective G)
  continuous_toFun := (bidualEvaluation G).continuous
  continuous_invFun := continuous_of_discreteTopology

end ProCGroups.Duality
