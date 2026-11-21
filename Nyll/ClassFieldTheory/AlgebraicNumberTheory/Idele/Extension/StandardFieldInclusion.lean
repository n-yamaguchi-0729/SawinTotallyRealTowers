/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleClassBaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FieldInclusion

/-!
# Functoriality of standard idele-class inclusion

The existing completion calculations prove identity and tower composition for
the same standard inclusion. Relative scalar descent proves its injectivity,
which is needed for the finite-level directed system.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace NumberField.IdeleClassGroup

universe u v w

variable (K : Type u) (L : Type v)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Scalar inclusion along the identity extension is the identity. -/
theorem fieldInclusion_self :
    fieldInclusion K K = MonoidHom.id (IdeleClassGroup (𝓞 K) K) :=
  ideleClassExtension_self K

/-- Scalar inclusion is functorial for arbitrary towers of number fields. -/
theorem fieldInclusion_comp (M : Type w) [Field M] [NumberField M]
    [Algebra K M] [Algebra M L] [IsScalarTower K M L] :
    (fieldInclusion M L).comp (fieldInclusion K M) = fieldInclusion K L :=
  ideleClassExtension_comp K L M

/-- Scalar descent makes the standard idele-class inclusion injective. -/
theorem fieldInclusion_injective : Function.Injective (fieldInclusion K L) := by
  intro c d h
  apply RelativeIdeleGroup.classInclusion_injective K L
  apply (relativeIdeleClassBaseChangeMulEquiv (K := K) (L := L)).injective
  rw [relativeIdeleClassBaseChangeMulEquiv_classInclusion,
    relativeIdeleClassBaseChangeMulEquiv_classInclusion]
  exact h

end NumberField.IdeleClassGroup
