/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.KernelBoundary.Homology

/-!
# Fox differential: discrete — kernel boundary — magnus kernel

The principal declarations in this module are:

- `kernelAbelianizationBoundaryLinearOfSurjective_injective`
  The surjective-case linear kernel-boundary map is injective in the Magnus-kernel comparison.
- `mem_commutator_ker_of_d_eq_zero_of_surjective`
  Discrete Magnus-kernel form of the injectivity theorem: for a surjective \(\psi\), if the
  Crowell/Fox differential of a kernel element vanishes, then that element already lies in the
  ordinary commutator subgroup of \(\ker \psi\).
-/

namespace FoxDifferential

noncomputable section

namespace KernelAugmentation

variable {H G : Type} [Group H] [DecidableEq H] [Group G] [DecidableEq G]
variable {ψ : G →* H}

omit [DecidableEq H] in
omit [DecidableEq H] [DecidableEq G] in
/-- The surjective-case linear kernel-boundary map is injective in the Magnus-kernel comparison. -/
theorem kernelAbelianizationBoundaryLinearOfSurjective_injective
    (hψ : Function.Surjective ψ) :
    letI := kernelAbelianizationModuleOfSurjective ψ hψ
    Function.Injective (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ) := by
  let := kernelAbelianizationModuleOfSurjective ψ hψ
  let := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
  intro x y hxy
  have hcoinv :
      kernelAbelianizationToCoinvariantsLinear (ψ := ψ) x =
        kernelAbelianizationToCoinvariantsLinear (ψ := ψ) y := by
    calc
      kernelAbelianizationToCoinvariantsLinear (ψ := ψ) x =
          differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective (ψ := ψ) hψ
            (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ x) := by
              symm
              exact differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective_boundary
                (ψ := ψ) hψ x
      _ =
          differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective (ψ := ψ) hψ
            (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ y) := by
              simp only [hxy, kernelAbelianizationBoundaryLinearOfSurjective_apply]
      _ = kernelAbelianizationToCoinvariantsLinear (ψ := ψ) y := by
            exact differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective_boundary
              (ψ := ψ) hψ y
  exact (kernelAbelianizationToCoinvariantsLinear_injective (H := H) (ψ := ψ) hψ) hcoinv

omit [DecidableEq H] [DecidableEq G] in
/--
Discrete Magnus-kernel form of the injectivity theorem: for a surjective \(\psi\), if the
Crowell/Fox differential of a kernel element vanishes, then that element already lies in the
ordinary commutator subgroup of \(\ker \psi\).
-/
theorem mem_commutator_ker_of_d_eq_zero_of_surjective
    (hψ : Function.Surjective ψ) (n : ψ.ker) (hn : universalDifferential ψ n.1 = 0) :
    n ∈ commutator ψ.ker := by
  let := kernelAbelianizationModuleOfSurjective ψ hψ
  have hboundary_zero :
      kernelAbelianizationBoundaryLinearOfSurjective ψ hψ
          (Additive.ofMul (Abelianization.of n)) =
        kernelAbelianizationBoundaryLinearOfSurjective ψ hψ 0 := by
    rw [kernelAbelianizationBoundaryLinearOfSurjective_of, hn]
    simp only [map_zero]
  have hclass_zero :
      (Additive.ofMul (Abelianization.of n) : KernelAbelianizationAdd ψ) = 0 :=
    (FoxDifferential.KernelAugmentation.kernelAbelianizationBoundaryLinearOfSurjective_injective
      (H := H) (ψ := ψ) hψ) hboundary_zero
  have hclass_one : Abelianization.of n = 1 := by
    simpa using congrArg Additive.toMul hclass_zero
  exact (QuotientGroup.eq_one_iff (N := commutator ψ.ker) n).1 hclass_one

end KernelAugmentation

export KernelAugmentation
  (kernelAbelianizationBoundaryLinearOfSurjective_injective
    mem_commutator_ker_of_d_eq_zero_of_surjective)

end

end FoxDifferential
