/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.KernelBoundary.MagnusKernel
import Nyll.ProCGroups.FoxDifferential.Discrete.FoxCalculus.Boundary

/-!
# Fox Differential / Discrete / Kernel Boundary / Magnus Comparison

This module compares the relative free Fox derivative with the universal differential and
deduces the discrete Magnus-kernel criterion in relative Fox coordinates.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential

variable {X : Type} {H : Type}
variable [Group H] [Finite X]

local instance : Fintype X := Fintype.ofFinite X
local instance : DecidableEq X := Classical.decEq X

/--
If the FoxDifferential relative free Fox derivative of a word vanishes, then the Crowell
universal differential of the same word vanishes.
-/
theorem d_eq_zero_of_foxDifferential_relativeFreeGroupFoxDerivative_eq_zero
    (ψ : FreeGroup X →* H) (w : FreeGroup X)
    (hw :
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative
        (H := H) X ψ w = 0) :
    universalDifferential ψ w = 0 := by
  have h :=
    FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearMap_derivative
      (H := H) X ψ w
  rw [hw, map_zero] at h
  exact h.symm

/--
Discrete Magnus-kernel theorem with the zero condition formulated using the FoxDifferential
relative free Fox derivative.
-/
theorem mem_commutator_ker_of_relFreeFoxDeriv_eq_zero_of_surj
    (ψ : FreeGroup X →* H) (hψ : Function.Surjective ψ) (n : ψ.ker)
    (hn :
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative
        (H := H) X ψ n.1 = 0) :
    n ∈ commutator ψ.ker :=
  mem_commutator_ker_of_d_eq_zero_of_surjective (ψ := ψ) hψ n
    (d_eq_zero_of_foxDifferential_relativeFreeGroupFoxDerivative_eq_zero
      (X := X) (H := H) ψ n.1 hn)

end

end CrowellExactSequence
