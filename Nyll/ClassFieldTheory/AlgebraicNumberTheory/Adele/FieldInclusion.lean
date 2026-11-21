/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.Norm

/-!
# Inclusion of ordinary adeles under a field extension

The map is the scalar inclusion into the relative adele algebra followed by
the existing ring base-change equivalence. Its component and diagonal values
are inherited from that equivalence.
-/

@[expose] public section

noncomputable section

open scoped NumberField TensorProduct
open AlgebraicNumberTheory.Valuations IsDedekindDomain

namespace NumberField.AdeleRing

universe u v

variable (K : Type u) (L : Type v)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The scalar inclusion of the standard adele rings. -/
def fieldInclusion : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  (relativeAdeleBaseChangeRingEquiv (K := K) (L := L)).toRingHom.comp
    (algebraMap (AdeleRing (𝓞 K) K) (RelativeAdeleRing K L))

/-- Inclusion is evaluated by the same relative tensor and base-change map. -/
theorem fieldInclusion_apply (a : AdeleRing (𝓞 K) K) :
    fieldInclusion K L a =
      relativeAdeleBaseChangeRingEquiv (K := K) (L := L) (a ⊗ₜ[K] (1 : L)) := rfl

/-- The inclusion of ordinary adeles is injective. -/
theorem fieldInclusion_injective : Function.Injective (fieldInclusion K L) :=
  (relativeAdeleBaseChangeRingEquiv (K := K) (L := L)).injective.comp
    (Algebra.TensorProduct.includeLeft_injective
      (R := K) (S := K) (A := AdeleRing (𝓞 K) K) (B := L)
      (FaithfulSMul.algebraMap_injective K L))

/-- Scalar inclusion preserves the diagonal copy of the base field. -/
theorem fieldInclusion_algebraMap (x : K) :
    fieldInclusion K L (algebraMap K (AdeleRing (𝓞 K) K) x) =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x) := by
  rw [fieldInclusion_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul,
    relativeAdeleBaseChangeRingEquiv_fieldInclusion]

/-- At a finite place, scalar inclusion is the actual completion map. -/
theorem fieldInclusion_finite (a : AdeleRing (𝓞 K) K)
    (W : HeightOneSpectrum (𝓞 L)) :
    (fieldInclusion K L a).2 W =
      finitePlaceAdicCompletionMap K L (finitePlaceBelow (K := K) W)
        ⟨W, rfl⟩ (a.2 (finitePlaceBelow (K := K) W)) := by
  rw [fieldInclusion_apply, relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul,
    map_one, mul_one]

/-- At an infinite place, scalar inclusion is the actual archimedean completion map. -/
theorem fieldInclusion_infinite (a : AdeleRing (𝓞 K) K) (W : InfinitePlace L) :
    let v := infinitePlaceBelow (K := K) W
    let : W.1.LiesOver v.1 := ⟨rfl⟩
    (fieldInclusion K L a).1 W =
      AbsoluteValue.Completion.map v.1 W.1 (a.1 v) := by
  intro v sharedOwner
  rw [fieldInclusion_apply, relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul,
    map_one, mul_one]

/-- Norm after scalar inclusion raises an adele to the extension degree. -/
theorem fieldNorm_fieldInclusion (a : AdeleRing (𝓞 K) K) :
    fieldNorm K L (fieldInclusion K L a) = a ^ Module.finrank K L := by
  rw [fieldInclusion_apply, fieldNorm_baseChange]
  change Algebra.norm (AdeleRing (𝓞 K) K)
    (algebraMap (AdeleRing (𝓞 K) K) (RelativeAdeleRing K L) a) = _
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange]

end NumberField.AdeleRing
