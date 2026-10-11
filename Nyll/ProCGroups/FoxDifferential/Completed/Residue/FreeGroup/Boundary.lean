/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Common.FoxBoundary
import Nyll.ProCGroups.FoxDifferential.Completed.Residue.FreeGroup.Basic

/-!
# Fox differential: completed — residue — free group — boundary

The principal declarations in this module are:

- `residueFreeGroupFoxBoundary`
  The residue Fox boundary/Euler map \(v \mapsto \sum_i v_i * ([\psi(x_i)]-1)\).
- `residueFreeGroupFoxBoundary_apply`
  The residue free-group Fox boundary is evaluated on the canonical generators and then extended
  linearly to the residue coordinate module.
- `residueFreeGroupFoxBoundary_single`
  The residue Fox boundary sends a coordinate basis vector to the corresponding augmentation
  generator.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v


variable {X : Type u} {H : Type v} [Group H] [DecidableEq X]

section FiniteBasis

variable [Fintype X]

/-- The residue Fox boundary/Euler map \(v \mapsto \sum_i v_i * ([\psi(x_i)]-1)\). -/
def residueFreeGroupFoxBoundary (n : ℕ) (ψ : FreeGroup X →* H) :
    ResidueFreeFoxCoordinates n H X →ₗ[ResidueGroupRing n H] ResidueGroupRing n H where
  toFun v :=
    ∑ i : X,
      v i *
        (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1)
  map_add' := by
    intro v w
    simp only [Pi.add_apply, MonoidAlgebra.of_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    simp only [Pi.smul_apply, smul_eq_mul, MonoidAlgebra.of_apply, mul_assoc, RingHom.id_apply,
        Finset.mul_sum]

omit [DecidableEq X] in
/--
The residue free-group Fox boundary is evaluated on the canonical generators and then extended
linearly to the residue coordinate module.
-/
theorem residueFreeGroupFoxBoundary_apply
    (n : ℕ) (ψ : FreeGroup X →* H) (v : ResidueFreeFoxCoordinates n H X) :
    residueFreeGroupFoxBoundary n ψ v =
      ∑ i : X,
        v i *
          (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1) :=
  rfl

/--
The residue Fox boundary sends a coordinate basis vector to the corresponding augmentation
generator.
-/
@[simp]
theorem residueFreeGroupFoxBoundary_single (n : ℕ) (ψ : FreeGroup X →* H) (i : X) :
    residueFreeGroupFoxBoundary n ψ
        (Pi.single i (1 : ResidueGroupRing n H)) =
      residueGroupRingBoundary n ψ (FreeGroup.of i) := by
  rw [residueFreeGroupFoxBoundary_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, MonoidAlgebra.of_apply, one_mul, residueGroupRingBoundary]
    rfl
  · intro j _ hji
    simp only [Pi.single_eq_of_ne hji, MonoidAlgebra.of_apply, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, MonoidAlgebra.of_apply,
      one_mul,
  IsEmpty.forall_iff]

end FiniteBasis


end

end FoxDifferential
