/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.FieldInclusion
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FieldNorm

/-!
# Inclusion of standard ideles and idele classes

The units functor and the principal quotient induce both maps from the same
adelic ring inclusion. Norm after inclusion is the extension-degree power.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace NumberField

universe u v

variable (K : Type u) (L : Type v)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup

/-- The scalar inclusion on the standard units of the adele ring. -/
def fieldInclusion : IdeleGroup (𝓞 K) K →* IdeleGroup (𝓞 L) L :=
  Units.map (AdeleRing.fieldInclusion K L).toMonoidHom

/-- The underlying adelic value uses the same scalar inclusion. -/
theorem coe_fieldInclusion (a : IdeleGroup (𝓞 K) K) :
    (fieldInclusion K L a : AdeleRing (𝓞 L) L) =
      AdeleRing.fieldInclusion K L (a : AdeleRing (𝓞 K) K) := rfl

/-- Scalar inclusion on standard ideles is injective. -/
theorem fieldInclusion_injective : Function.Injective (fieldInclusion K L) :=
  Units.map_injective (AdeleRing.fieldInclusion_injective K L)

/-- Diagonal units are preserved by the actual field inclusion. -/
theorem fieldInclusion_unitEmbedding (x : Kˣ) :
    fieldInclusion K L (unitEmbedding (𝓞 K) K x) =
      unitEmbedding (𝓞 L) L (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Units.ext
  exact AdeleRing.fieldInclusion_algebraMap K L (x : K)

/-- Norm after inclusion on standard ideles is the extension-degree power. -/
theorem norm_fieldInclusion (a : IdeleGroup (𝓞 K) K) :
    norm K L (fieldInclusion K L a) = a ^ Module.finrank K L := by
  apply Units.ext
  exact AdeleRing.fieldNorm_fieldInclusion K L (a : AdeleRing (𝓞 K) K)

end IdeleGroup

namespace IdeleClassGroup

/-- Inclusion on the standard quotient by diagonal units. -/
def fieldInclusion : IdeleClassGroup (𝓞 K) K →* IdeleClassGroup (𝓞 L) L :=
  QuotientGroup.map
    (IdeleGroup.principalSubgroup (𝓞 K) K)
    (IdeleGroup.principalSubgroup (𝓞 L) L)
    (IdeleGroup.fieldInclusion K L)
    (by
      rintro _ ⟨x, rfl⟩
      exact ⟨Units.map (algebraMap K L).toMonoidHom x,
        (IdeleGroup.fieldInclusion_unitEmbedding K L x).symm⟩)

/-- Inclusion on the quotient is evaluated on its original idele representative. -/
theorem fieldInclusion_mk (a : IdeleGroup (𝓞 K) K) :
    fieldInclusion K L (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) a) =
      QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 L) L)
        (IdeleGroup.fieldInclusion K L a) := rfl

/-- Norm after inclusion on the standard principal quotient is the degree power. -/
theorem norm_fieldInclusion (c : IdeleClassGroup (𝓞 K) K) :
    norm K L (fieldInclusion K L c) = c ^ Module.finrank K L := by
  refine QuotientGroup.induction_on c ?_
  intro a
  let qK := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  let qL := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 L) L)
  change norm K L (fieldInclusion K L (qK a)) = qK a ^ Module.finrank K L
  calc
    _ = norm K L (qL (IdeleGroup.fieldInclusion K L a)) :=
      congrArg (norm K L) (fieldInclusion_mk K L a)
    _ = qK (IdeleGroup.norm K L (IdeleGroup.fieldInclusion K L a)) := norm_mk K L _
    _ = qK (a ^ Module.finrank K L) := congrArg qK (IdeleGroup.norm_fieldInclusion K L a)
    _ = _ := map_pow qK a _

end IdeleClassGroup

end NumberField
