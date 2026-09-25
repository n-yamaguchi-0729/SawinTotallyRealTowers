/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

set_option autoImplicit false

/-!
# Unit cohomology under surjective scalar restriction

When F → E is surjective, restricting an E-automorphism of N to F
is a group isomorphism. Its action on Nˣ is unchanged.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

/-- Restricting scalars along a surjective base-field map preserves unit
cohomology, with identity coefficients in the unchanged top field. -/
noncomputable def unitsCohomologyRestrictScalarsIso
    (F E N : Type) [Field F] [Field E] [Field N]
    [Algebra F E] [Algebra E N] [Algebra F N] [IsScalarTower F E N]
    (h : Function.Surjective (algebraMap F E)) (n : ℕ) :
    groupCohomology (Rep.ofAlgebraAutOnUnits E N) n ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits F N) n :=
  groupCohomology.mapIso
    (AlgEquiv.extendScalarsHomOfSurjective (A := N) h).symm
    (LinearEquiv.refl ℤ (Additive Nˣ)) (fun _ ↦ rfl) n

end ClassFieldTower.Cohomology
