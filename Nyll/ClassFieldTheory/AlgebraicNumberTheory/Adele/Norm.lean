/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RelativeNorm

/-!
# The field norm on ordinary adeles

The determinant norm is transported through the scalar-extension ring
isomorphism. This map is multiplicative; it is not a ring homomorphism.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace NumberField.AdeleRing

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The adelic field norm, with values owned by the determinant norm. -/
def fieldNorm : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 K) K :=
  (Algebra.norm (AdeleRing (𝓞 K) K)).comp
    (relativeAdeleBaseChangeRingEquiv (K := K) (L := L)).symm.toMonoidHom

/-- Evaluating the ordinary norm in the relative adele algebra. -/
theorem fieldNorm_baseChange (a : RelativeAdeleRing K L) :
    fieldNorm K L (relativeAdeleBaseChangeRingEquiv (K := K) (L := L) a) =
      Algebra.norm (AdeleRing (𝓞 K) K) a := by
  change Algebra.norm (AdeleRing (𝓞 K) K)
    ((relativeAdeleBaseChangeRingEquiv (K := K) (L := L)).symm
      (relativeAdeleBaseChangeRingEquiv (K := K) (L := L) a)) = _
  rw [RingEquiv.symm_apply_apply]

/-- The adelic norm carries a diagonal element to its field norm. -/
theorem fieldNorm_algebraMap (x : L) :
    fieldNorm K L (algebraMap L (AdeleRing (𝓞 L) L) x) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K x) := by
  rw [← relativeAdeleBaseChangeRingEquiv_fieldInclusion (K := K) (L := L) x,
    fieldNorm_baseChange]
  exact RelativeIdeleGroup.norm_fieldInclusion K L x

end NumberField.AdeleRing
