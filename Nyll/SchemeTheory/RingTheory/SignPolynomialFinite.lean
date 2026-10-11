/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.SignPolynomialInvariants
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! # Finiteness of the simultaneous sign quotient

The polynomial ring is finite over its concrete quadratic subalgebra. The
invariant-ring input is the proved calculation for simultaneous sign change,
with the action explicitly selected. These statements allow zero variables.
-/

noncomputable section

namespace SchemeTheory.SignPolynomial

open MvPolynomial

variable (k : Type*) [Field k] (n : ℕ)

/-- The actual quadratic subalgebra has finite type over the coefficient field. -/
theorem quadratic_finiteType : Algebra.FiniteType k (quadraticSubalgebra k n) := by
  exact Algebra.FiniteType.adjoin_of_finite (Set.finite_range
    (fun ij : Fin n × Fin n => (X ij.1 : MvPolynomial (Fin n) k) * X ij.2))

/-- The polynomial algebra has finite type over the quadratic subalgebra. -/
theorem polynomial_finiteType_quadratic :
    Algebra.FiniteType (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) :=
  Algebra.FiniteType.of_restrictScalars_finiteType k
    (quadraticSubalgebra k n) (MvPolynomial (Fin n) k)

/-- Invariance uses the simultaneous sign action, rather than integer scalar multiplication. -/
theorem quadratic_isInvariant (htwo : (2 : k) ≠ 0) :
    let _action : MulSemiringAction ℤˣ (MvPolynomial (Fin n) k) := signAction k n
    Algebra.IsInvariant (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) ℤˣ := by
  intro _action
  constructor
  intro p hp
  exact ⟨⟨p, (forall_signAction_iff_mem_quadraticSubalgebra k n htwo p).mp hp⟩, rfl⟩

/-- Every polynomial is integral over the concrete quadratic subalgebra. -/
theorem polynomial_isIntegral_quadratic (htwo : (2 : k) ≠ 0) :
    Algebra.IsIntegral (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) := by
  let action : MulSemiringAction ℤˣ (MvPolynomial (Fin n) k) := signAction k n
  have hinvariant :
      Algebra.IsInvariant (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) ℤˣ :=
    quadratic_isInvariant k n htwo
  exact Algebra.IsInvariant.isIntegral (quadraticSubalgebra k n)
    (MvPolynomial (Fin n) k) ℤˣ

/-- The actual polynomial ring is a finite module over its quadratic subalgebra. -/
theorem polynomial_finite_quadratic (htwo : (2 : k) ≠ 0) :
    Module.Finite (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) := by
  have hfiniteType :
      Algebra.FiniteType (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) :=
    polynomial_finiteType_quadratic k n
  have hintegral :
      Algebra.IsIntegral (quadraticSubalgebra k n) (MvPolynomial (Fin n) k) :=
    polynomial_isIntegral_quadratic k n htwo
  exact Algebra.IsIntegral.finite

end SchemeTheory.SignPolynomial
