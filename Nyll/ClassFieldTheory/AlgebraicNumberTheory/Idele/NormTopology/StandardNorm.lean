/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FieldNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.Continuity
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Continuous bundles for the standard field norms

The continuity proof uses the existing restricted-product topology. Both
continuous bundles retain exactly the algebraic maps from `Idele.FieldNorm`.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace NumberField

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup

/-- Continuity of the standard idele norm in the topology of adele units. -/
theorem norm_continuous : Continuous (norm K L) :=
  _root_.IdeleGroup.norm_continuous K L

/-- The algebraic idele norm bundled with its continuity proof. -/
def normContinuousMonoidHom : IdeleGroup (𝓞 L) L →ₜ* IdeleGroup (𝓞 K) K where
  __ := norm K L
  continuous_toFun := norm_continuous K L

/-- The continuous bundle has the canonical algebraic norm as its underlying map. -/
theorem normContinuousMonoidHom_toMonoidHom :
    (normContinuousMonoidHom K L).toMonoidHom = norm K L := rfl

end IdeleGroup

namespace IdeleClassGroup

/-- Continuity descends from the standard idele norm through the principal quotient. -/
theorem norm_continuous : Continuous (norm K L) := by
  apply (QuotientGroup.isQuotientMap_mk
    (G := IdeleGroup (𝓞 L) L)
    (N := IdeleGroup.principalSubgroup (𝓞 L) L)).continuous_iff.mpr
  exact QuotientGroup.continuous_mk.comp (IdeleGroup.norm_continuous K L)

/-- The standard quotient norm, bundled downstream with quotient continuity. -/
def normContinuousMonoidHom : IdeleClassGroup (𝓞 L) L →ₜ*
    IdeleClassGroup (𝓞 K) K where
  __ := norm K L
  continuous_toFun := norm_continuous K L

/-- The continuous quotient norm retains exactly the algebraic norm. -/
theorem normContinuousMonoidHom_toMonoidHom :
    (normContinuousMonoidHom K L).toMonoidHom = norm K L := rfl

end IdeleClassGroup

end NumberField
