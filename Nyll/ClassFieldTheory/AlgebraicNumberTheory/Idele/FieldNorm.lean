/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.Norm
public import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Field norms on the standard idele and idele-class groups

The idele norm is the units functor applied to the adelic field norm. Its
principal-idele calculation defines the norm on Mathlib's principal quotient.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace NumberField

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup

/-- The standard idele norm, induced by the adelic determinant norm. -/
def norm : IdeleGroup (𝓞 L) L →* IdeleGroup (𝓞 K) K :=
  Units.map (AdeleRing.fieldNorm K L)

/-- The value of the idele norm is the adelic field norm. -/
theorem coe_norm (a : IdeleGroup (𝓞 L) L) :
    (norm K L a : AdeleRing (𝓞 K) K) =
      AdeleRing.fieldNorm K L (a : AdeleRing (𝓞 L) L) := rfl

/-- The norm preserves diagonal units through the field norm. -/
theorem norm_unitEmbedding (x : Lˣ) :
    norm K L (unitEmbedding (𝓞 L) L x) =
      unitEmbedding (𝓞 K) K (Units.map (Algebra.norm K) x) := by
  apply Units.ext
  exact AdeleRing.fieldNorm_algebraMap K L (x : L)

end IdeleGroup

namespace IdeleClassGroup

/-- The norm on the standard quotient by principal ideles. -/
def norm : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K :=
  QuotientGroup.map
    (IdeleGroup.principalSubgroup (𝓞 L) L)
    (IdeleGroup.principalSubgroup (𝓞 K) K)
    (IdeleGroup.norm K L)
    (by
      rintro _ ⟨x, rfl⟩
      exact ⟨Units.map (Algebra.norm K) x,
        (IdeleGroup.norm_unitEmbedding K L x).symm⟩)

/-- The quotient norm is evaluated on an ordinary idele representative. -/
theorem norm_mk (a : IdeleGroup (𝓞 L) L) :
    norm K L (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 L) L) a) =
      QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
        (IdeleGroup.norm K L a) := rfl

end IdeleClassGroup

end NumberField
