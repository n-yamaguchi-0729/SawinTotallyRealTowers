/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence

set_option autoImplicit false
/-!
# The closure equivalence underlying finite-extension absolute restriction

For an actual finite intermediate field, the canonical algebraic-closure
equivalence is exactly the choice used by the existing absolute Galois
inclusion. This evaluation identity lets finite base changes use the same
closure without an additional comparison hypothesis.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open RamificationTheory.Field.absoluteGaloisGroup

variable (F : Type) [Field F]
variable (C : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F C]

/-- The algebraic-closure equivalence used in the actual finite-extension
absolute Galois inclusion. Both added instances are proposition-valued. -/
def finiteIntermediateAbsoluteClosureEquiv :
    AlgebraicClosure C ≃ₐ[C] AlgebraicClosure F := by
  letI : Algebra.IsAlgebraic C (AlgebraicClosure F) :=
    Algebra.IsAlgebraic.tower_top (K := F) (L := C) (A := AlgebraicClosure F)
  letI : IsAlgClosure C (AlgebraicClosure F) :=
    { isAlgClosed := inferInstance, isAlgebraic := inferInstance }
  exact IsAlgClosure.equiv C (AlgebraicClosure C) (AlgebraicClosure F)

/-- Actual absolute restriction acts by conjugation with this same closure
equivalence; the compatibility is definitional. -/
theorem finiteIntermediateAbsoluteGaloisInclusion_apply
    (sigma : Field.absoluteGaloisGroup C) (x : AlgebraicClosure F) :
    (show Gal(AlgebraicClosure F/F) from
      ofFiniteExtensionAbsoluteContinuous F C.val sigma) x =
      finiteIntermediateAbsoluteClosureEquiv F C
        ((absoluteGaloisGroupContinuousMulEquiv C sigma)
          ((finiteIntermediateAbsoluteClosureEquiv F C).symm x)) := by
  rfl

end ClassFieldTower.Martinet.Shafarevich
