/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Finite abelian extensions of an arbitrary field

The common carrier is an intermediate field of the chosen separable closure,
with its finite-dimensional and abelian Galois properties. Local, global, and
function-field class field theory use this same carrier and its instances.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u

/-- A finite abelian extension inside the chosen separable closure, ordered
by inclusion of intermediate fields. -/
abbrev FiniteAbelianExtension (K : Type u) [Field K] :=
  { E : IntermediateField K (SeparableClosure K) //
      FiniteDimensional K E ∧ IsAbelianGalois K E }

namespace FiniteAbelianExtension

instance {K : Type u} [Field K] :
    CoeSort (FiniteAbelianExtension K) (Type u) where
  coe E := E.1

instance {K : Type u} [Field K]
    (E : FiniteAbelianExtension K) : Field E :=
  inferInstance

instance {K : Type u} [Field K]
    (E : FiniteAbelianExtension K) : FiniteDimensional K E :=
  E.2.1

instance {K : Type u} [Field K]
    (E : FiniteAbelianExtension K) : Algebra K E :=
  inferInstance

instance {K : Type u} [Field K]
    (E : FiniteAbelianExtension K) : IsAbelianGalois K E :=
  E.2.2

end FiniteAbelianExtension

end ClassFieldTheory
