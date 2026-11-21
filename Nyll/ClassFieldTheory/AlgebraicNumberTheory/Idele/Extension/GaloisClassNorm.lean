/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisNorm

/-!
# The Galois product formula on relative idele classes

The determinant product formula descends through the actual principal quotient.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace RelativeIdeleGroup

universe u v

variable {K : Type u} {L : Type v}
  [Field K] [NumberField K] [Field L] [Algebra K L] [FiniteDimensional K L]

local instance :
    MulDistribMulAction (L ≃ₐ[K] L) (RelativeIdeleGroup.ClassGroup K L) :=
  Cohomology.ideleClassMulDistribMulAction K L

/-- The Galois product formula after descent to relative idele classes. -/
theorem classInclusion_ideleClassNorm_eq_prod_conjugates
    [IsGalois K L]
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classInclusion K L
        (RelativeIdeleGroup.classNorm K L c) =
      ∏ σ : L ≃ₐ[K] L, σ • c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  rw [← QuotientGroup.mk'_apply (RelativeIdeleGroup.principalSubgroup K L) a,
    RelativeIdeleGroup.classNorm_mk, RelativeIdeleGroup.classInclusion_mk]
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        (RelativeIdeleGroup.inclusion K L
          (RelativeIdeleGroup.norm K L a)) =
      ∏ σ : L ≃ₐ[K] L,
        QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (σ • a)
  rw [RelativeIdeleGroup.inclusion_norm_eq_prod_conjugates]
  exact map_prod
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L))
    (fun σ : L ≃ₐ[K] L => σ • a)
    Finset.univ

end RelativeIdeleGroup
