/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.StandardIdeal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.AbsoluteNormCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Components
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.DivisorAbsoluteNorm
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# The product formula for principal ideles

This file proves that the absolute idele norm is trivial on the diagonal
copy of `Kˣ`, and hence descends to the idele class group.
-/



@[expose] public section

open scoped NumberField RestrictedProduct NNReal WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace NumberField.IdeleGroup

private theorem absoluteNorm_infinitePart_unitEmbedding (x : Kˣ) :
    (InfiniteAdeleRing.absoluteNorm (infinitePart (unitEmbedding (𝓞 K) K x)) : ℝ≥0) =
      ⟨|((Algebra.norm ℚ) (x : K) : ℝ)|, abs_nonneg _⟩ := by
  rw [InfiniteAdeleRing.absoluteNorm_apply]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val,
    nnnormUnitHom_val]
  apply NNReal.eq
  simp only [NNReal.coe_prod, NNReal.coe_pow, coe_nnNorm]
  change (∏ w : InfinitePlace K, ‖(algebraMap K (InfiniteAdeleRing K) (x : K)) w‖ ^ w.mult) = _
  rw [← InfiniteAdeleRing.norm_def]
  change ‖(algebraMap K (InfiniteAdeleRing K)) (x : K)‖ = |((Algebra.norm ℚ) (x : K) : ℝ)|
  exact (InfiniteAdeleRing.coe_norm_eq_abs_norm (x : K)).trans
    (Rat.cast_abs (K := ℝ) ((Algebra.norm ℚ) (x : K)))

private theorem absoluteNorm_finitePart_unitEmbedding (x : Kˣ) :
    (FiniteAdeleRing.absoluteNorm (finitePart (unitEmbedding (𝓞 K) K x)) : ℝ≥0) =
      ⟨|((Algebra.norm ℚ) (x : K) : ℝ)|, abs_nonneg _⟩ := by
  rw [FiniteAdeleRing.absoluteNorm_eq_fractionalIdealAbsoluteNorm]
  change (fractionalIdealAbsoluteNorm (fractionalIdeal (unitEmbedding (𝓞 K) K x)) : ℝ≥0) = _
  rw [fractionalIdeal_unitEmbedding]
  exact fractionalIdealAbsoluteNorm_toPrincipalIdeal x

/-- The number-field product formula on the unit group of the adele ring. -/
@[simp]
theorem absoluteNorm_unitEmbedding (x : Kˣ) : absoluteNorm (unitEmbedding (𝓞 K) K x) = 1 := by
  rw [absoluteNorm_apply]
  have h : FiniteAdeleRing.absoluteNorm (finitePart (unitEmbedding (𝓞 K) K x)) =
      InfiniteAdeleRing.absoluteNorm (infinitePart (unitEmbedding (𝓞 K) K x)) :=
    Units.ext ((absoluteNorm_finitePart_unitEmbedding x).trans
      (absoluteNorm_infinitePart_unitEmbedding x).symm)
  rw [h, mul_inv_cancel]

/-- The standard principal subgroup lies in the kernel of the absolute norm. -/
theorem principalSubgroup_le_normOneSubgroup :
    principalSubgroup (𝓞 K) K ≤ normOneSubgroup (K := K) := by
  rintro _ ⟨x, rfl⟩
  exact absoluteNorm_unitEmbedding x

end NumberField.IdeleGroup

namespace NumberField.IdeleClassGroup

/-- The absolute norm on the standard principal quotient. -/
def absoluteNorm : IdeleClassGroup (𝓞 K) K →* ℝ≥0ˣ :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup (𝓞 K) K)
    (IdeleGroup.absoluteNorm (K := K)) IdeleGroup.principalSubgroup_le_normOneSubgroup

/-- The absolute class norm has the absolute norm of any idele representative. -/
@[simp]
theorem absoluteNorm_mk (a : IdeleGroup (𝓞 K) K) :
    absoluteNorm (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) a) =
      IdeleGroup.absoluteNorm a :=
  QuotientGroup.lift_mk _ _ _

/-- The norm-one subgroup of standard idele classes. -/
def normOneSubgroup : Subgroup (IdeleClassGroup (𝓞 K) K) := (absoluteNorm (K := K)).ker

end NumberField.IdeleClassGroup

namespace InfiniteIdeleGroup

/-- The archimedean norm of a principal idele is the absolute field norm. -/
theorem archimedeanNorm_principalIdele (x : Kˣ) :
    (NumberField.InfiniteAdeleRing.absoluteNorm
      (IdeleGroup.infinitePart (IdeleGroup.principalIdele K x)) : ℝ≥0) =
      ⟨|((Algebra.norm ℚ) (x : K) : ℝ)|, abs_nonneg _⟩ :=
  NumberField.IdeleGroup.absoluteNorm_infinitePart_unitEmbedding x

end InfiniteIdeleGroup

namespace FiniteIdeleGroup

/-- The finite idele norm is the absolute norm of its associated fractional
ideal. -/
theorem absoluteNorm_eq_fractionalIdealAbsoluteNorm
    (a : FiniteIdeleGroup K) :
    absoluteNorm a =
      NumberField.fractionalIdealAbsoluteNorm (fractionalIdeal a) :=
  (NumberField.fractionalIdealAbsoluteNorm_factorization (valuationVector a)).symm

/-- The finite norm of a principal idele is the absolute field norm. -/
theorem absoluteNorm_principalIdele (x : Kˣ) :
    ((absoluteNorm (IdeleGroup.finiteCoordinates (IdeleGroup.principalIdele K x)) : ℝ≥0ˣ) : ℝ≥0) =
      ⟨|((Algebra.norm ℚ) (x : K) : ℝ)|, abs_nonneg _⟩ :=
  NumberField.IdeleGroup.absoluteNorm_finitePart_unitEmbedding x

end FiniteIdeleGroup

namespace IdeleGroup

/-- The finite and archimedean norm factors agree on a principal idele. -/
theorem finite_absoluteNorm_eq_archimedeanNorm_principalIdele
    (x : Kˣ) :
    FiniteIdeleGroup.absoluteNorm (IdeleGroup.finiteCoordinates (principalIdele K x)) =
      NumberField.InfiniteAdeleRing.absoluteNorm
        (IdeleGroup.infinitePart (principalIdele K x)) := by
  apply Units.ext
  exact (FiniteIdeleGroup.absoluteNorm_principalIdele x).trans
    (InfiniteIdeleGroup.archimedeanNorm_principalIdele x).symm

/-- The number-field product formula in idelic form: every principal idele
has global absolute norm one. -/
@[simp]
theorem absoluteNorm_principalIdele (x : Kˣ) :
    absoluteNorm (principalIdele K x) = 1 :=
  NumberField.IdeleGroup.absoluteNorm_unitEmbedding x

/-- Principal ideles lie in the norm-one subgroup. -/
theorem principalSubgroup_le_normOneSubgroup :
    principalSubgroup K ≤ normOneSubgroup (K := K) := by
  rintro a ⟨x, rfl⟩
  exact absoluteNorm_principalIdele x

end IdeleGroup

namespace IdeleClassGroup

/-- The standard absolute class norm in restricted-product coordinates. -/
abbrev absoluteNorm : IdeleClassGroup K →* ℝ≥0ˣ :=
  NumberField.IdeleClassGroup.absoluteNorm

@[simp]
theorem absoluteNorm_mk (a : IdeleGroup K) :
    absoluteNorm
      (IdeleGroup.toStandardClass K a) =
        IdeleGroup.absoluteNorm a :=
  NumberField.IdeleClassGroup.absoluteNorm_mk a

/-- The norm-one idele classes. -/
abbrev normOneSubgroup : Subgroup (IdeleClassGroup K) :=
  NumberField.IdeleClassGroup.normOneSubgroup

/-- Pulling the norm-one idele classes back to the idele group recovers
exactly the norm-one ideles. -/
theorem comap_normOneSubgroup :
    Subgroup.comap
      (IdeleGroup.toStandardClass K)
      (normOneSubgroup (K := K)) =
        IdeleGroup.normOneSubgroup (K := K) := by
  ext a
  change absoluteNorm
      (IdeleGroup.toStandardClass K a) = 1 ↔
    IdeleGroup.absoluteNorm a = 1
  rw [absoluteNorm_mk]

@[simp]
theorem mk_mem_normOneSubgroup_iff (a : IdeleGroup K) :
    IdeleGroup.toStandardClass K a ∈
        normOneSubgroup (K := K) ↔
      a ∈ IdeleGroup.normOneSubgroup (K := K) := by
  change absoluteNorm
      (IdeleGroup.toStandardClass K a) = 1 ↔
    IdeleGroup.absoluteNorm a = 1
  rw [absoluteNorm_mk]

end IdeleClassGroup
