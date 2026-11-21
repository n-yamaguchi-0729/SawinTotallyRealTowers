/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.ArchimedeanNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.Continuity
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.StandardNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FieldNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdealClass

/-!
# The ordinary norm on idele classes

The ordinary idele-class norm preserves the absolute norm and restricts to
the norm-one idele-class subgroups.
-/



@[expose] public section

open scoped NumberField
open NumberField

noncomputable section

namespace NumberField.IdeleClassGroup

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- The standard quotient norm preserves the absolute norm of idele classes. -/
theorem absoluteNorm_norm (c : IdeleClassGroup (𝓞 L) L) :
    absoluteNorm (norm K L c) = absoluteNorm c := by
  refine QuotientGroup.induction_on c (fun a => ?_)
  change absoluteNorm (norm K L (QuotientGroup.mk'
    (IdeleGroup.principalSubgroup (𝓞 L) L) a)) =
      absoluteNorm (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 L) L) a)
  rw [norm_mk, absoluteNorm_mk, absoluteNorm_mk, IdeleGroup.absoluteNorm_norm]

/-- The field norm restricts to a map of the standard norm-one class subgroups. -/
def normOneNorm : normOneSubgroup (K := L) →* normOneSubgroup (K := K) :=
  ((norm K L).comp (normOneSubgroup (K := L)).subtype).codRestrict
    (normOneSubgroup (K := K)) (fun c =>
      show absoluteNorm (norm K L c.1) = 1 from
        (absoluteNorm_norm K L c.1).trans c.2)

/-- The map on norm-one classes is the ordinary norm on the underlying classes. -/
@[simp]
theorem normOneNorm_apply (c : normOneSubgroup (K := L)) :
    (normOneNorm K L c : IdeleClassGroup (𝓞 K) K) = norm K L c.1 := rfl

/-- The restricted norm on standard classes is continuous for the subgroup topology. -/
theorem normOneNorm_continuous : Continuous (normOneNorm K L) :=
  ((norm_continuous K L).comp continuous_subtype_val).subtype_mk _

end NumberField.IdeleClassGroup

end
