/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Equiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FieldInclusion
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.FieldInclusion

/-!
# Naturality of standard field inclusion under compatible field equivalences

Tensor coherence supplies the adelic square. Units and the principal quotient
then supply the same square without any normality assumption.
-/

@[expose] public section

open scoped NumberField TensorProduct

noncomputable section

namespace NumberField

universe u v w x

variable {E : Type u} {E' : Type v} {F : Type w} {F' : Type x}
  [Field E] [NumberField E] [Field E'] [NumberField E']
  [Field F] [NumberField F] [Field F'] [NumberField F']
  [Algebra E F] [Algebra E' F']

namespace AdeleRing

/-- The standard adelic field inclusion is natural for a commuting field square. -/
theorem congr_fieldInclusion (f : E ≃ₐ[ℚ] E') (g : F ≃ₐ[ℚ] F')
    (h : ∀ a : E, g (algebraMap E F a) = algebraMap E' F' (f a))
    (a : AdeleRing (𝓞 E) E) :
    adeleCongr g (fieldInclusion E F a) = fieldInclusion E' F' (adeleCongr f a) := by
  rw [fieldInclusion_apply, fieldInclusion_apply,
    ← relativeAdeleBaseChangeRingEquiv_congrOfAlgEquiv f g h,
    relativeAdeleCongrOfAlgEquiv_tmul, map_one]

end AdeleRing

namespace IdeleGroup

/-- The standard idele field inclusion is natural for a commuting field square. -/
theorem congr_fieldInclusion (f : E ≃ₐ[ℚ] E') (g : F ≃ₐ[ℚ] F')
    (h : ∀ a : E, g (algebraMap E F a) = algebraMap E' F' (f a))
    (a : IdeleGroup (𝓞 E) E) :
    congr g (fieldInclusion E F a) = fieldInclusion E' F' (congr f a) := by
  apply Units.ext
  exact AdeleRing.congr_fieldInclusion f g h (a : AdeleRing (𝓞 E) E)

end IdeleGroup

namespace IdeleClassGroup

/-- The standard class inclusion is natural for a commuting field square. -/
theorem congr_fieldInclusion (f : E ≃ₐ[ℚ] E') (g : F ≃ₐ[ℚ] F')
    (h : ∀ a : E, g (algebraMap E F a) = algebraMap E' F' (f a))
    (c : IdeleClassGroup (𝓞 E) E) :
    congr g (fieldInclusion E F c) = fieldInclusion E' F' (congr f c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  let qE := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 E) E)
  let qE' := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 E') E')
  let qF := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  let qF' := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F') F')
  change congr g (fieldInclusion E F (qE a)) = fieldInclusion E' F' (congr f (qE a))
  calc
    _ = congr g (qF (IdeleGroup.fieldInclusion E F a)) :=
      congrArg (congr g) (fieldInclusion_mk E F a)
    _ = qF' (IdeleGroup.congr g (IdeleGroup.fieldInclusion E F a)) :=
      congr_mk g (IdeleGroup.fieldInclusion E F a)
    _ = qF' (IdeleGroup.fieldInclusion E' F' (IdeleGroup.congr f a)) :=
      congrArg qF' (IdeleGroup.congr_fieldInclusion f g h a)
    _ = fieldInclusion E' F' (qE' (IdeleGroup.congr f a)) :=
      (fieldInclusion_mk E' F' (IdeleGroup.congr f a)).symm
    _ = _ := congrArg (fieldInclusion E' F') (congr_mk f a).symm

end IdeleClassGroup

end NumberField
