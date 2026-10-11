/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Source

/-!
# Fox differential: completed — finite stage — stage — kernel ideal

The principal declarations in this module are:

- `foxAlgebraicStageSourceGeneratorSubOne_mem_sourceAugmentationIdeal`
  The finite-stage source generator \([x_i]-1\) belongs to the source augmentation ideal.
- `foxAlgebraicStageGroupAlgebraMapKernel_mem_mulAugmentation_of_derivatives_eq_zero`
  Finite-stage Fox kernel input: the target derivative equations place the source coefficients in
  K_j, while the source generator boundaries lie in I_j.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

omit [DecidableEq X] [N.Normal] in
/-- The finite-stage source generator \([x_i]-1\) belongs to the source augmentation ideal. -/
theorem foxAlgebraicStageSourceGeneratorSubOne_mem_sourceAugmentationIdeal
    (i : X) :
    MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
          (FreeGroup.of i)) - 1 ∈
      foxAlgebraicStageSourceAugmentationIdeal (X := X) N n := by
  rw [mem_foxAlgebraicStageSourceAugmentationIdeal]
  rw [map_sub,
    foxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient,
    map_one, sub_self]

/--
Finite-stage Fox kernel input: the target derivative equations place the source coefficients in
K_j, while the source generator boundaries lie in I_j.
-/
theorem foxAlgebraicStageGroupAlgebraMapKernel_mem_mulAugmentation_of_derivatives_eq_zero
    [Finite X]
    {x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n}
    (hderivative :
      ∀ i : X, foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x = 0)
    (haugmentation :
      foxCommutatorPowerSourceGroupAlgebraAugmentation
        (F := FreeGroup X) N n x = 0) :
    x ∈ foxAlgebraicStageGroupAlgebraMapKernelMulAugmentationIdeal (X := X) N n := by
  classical
  let := Fintype.ofFinite X
  have hcoeff_mem
      (i : X) :
      foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i x ∈
        foxAlgebraicStageGroupAlgebraMapKernelIdeal (X := X) N n := by
    rw [mem_foxAlgebraicStageGroupAlgebraMapKernelIdeal]
    rw [foxAlgebraicStageSourceGroupAlgebraDerivative_map]
    exact hderivative i
  have hformula :=
    foxAlgebraicStageSourceGroupAlgebraDerivative_groupAlgebra_fundamental_formula
      (X := X) (N := N) (n := n) x
  have hx_sum :
      x =
        ∑ i : X,
          foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i x *
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (QuotientGroup.mk'
                (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (FreeGroup.of i)) - 1) := by
    calc
      x =
          x -
            algebraMap (ModNCompletedCoeff n)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N n) 0 := by
            rw [map_zero, sub_zero]
      _ =
          x -
            algebraMap (ModNCompletedCoeff n)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
              (foxCommutatorPowerSourceGroupAlgebraAugmentation
                (F := FreeGroup X) N n x) := by
            rw [haugmentation]
      _ =
          ∑ i : X,
            foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i x *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := hformula
  rw [hx_sum]
  exact
    (foxAlgebraicStageGroupAlgebraMapKernelMulAugmentationIdeal (X := X) N n).sum_mem
      (fun i _ =>
        Ideal.mul_mem_mul (hcoeff_mem i)
          (foxAlgebraicStageSourceGeneratorSubOne_mem_sourceAugmentationIdeal
            (X := X) N n i))



end

end FoxDifferential
