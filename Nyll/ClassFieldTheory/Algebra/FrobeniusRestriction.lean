/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Arithmetic Frobenius and normal restriction

The arithmetic Frobenius of an algebraic extension of a finite field restricts
to the same Frobenius on a normal subextension, finite or infinite.
-/

@[expose] public section

namespace FiniteField

universe u v w

/-- Normal restriction preserves arithmetic Frobenius throughout an algebraic
tower over a finite field. The three fields have independent universes. -/
theorem restrictNormalHom_frobeniusAlgEquivOfAlgebraic
    (k : Type u) (E : Type v) (F : Type w)
    [Field k] [Fintype k] [Field E] [Field F]
    [Algebra k E] [Algebra k F] [Algebra E F] [IsScalarTower k E F]
    [Normal k E] [Algebra.IsAlgebraic k F] :
    AlgEquiv.restrictNormalHom E (frobeniusAlgEquivOfAlgebraic k F) =
      frobeniusAlgEquivOfAlgebraic k E := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E F).injective
  calc
    algebraMap E F ((AlgEquiv.restrictNormalHom E
        (frobeniusAlgEquivOfAlgebraic k F)) x) =
        frobeniusAlgEquivOfAlgebraic k F (algebraMap E F x) :=
      AlgEquiv.restrictNormal_commutes (frobeniusAlgEquivOfAlgebraic k F) E x
    _ = algebraMap E F (frobeniusAlgEquivOfAlgebraic k E x) := by
      simp only [coe_frobeniusAlgEquivOfAlgebraic]
      exact (map_pow (algebraMap E F) x (Fintype.card k)).symm

end FiniteField
