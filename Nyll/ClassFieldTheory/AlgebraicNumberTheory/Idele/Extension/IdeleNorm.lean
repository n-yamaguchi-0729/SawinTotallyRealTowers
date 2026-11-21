/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FieldNorm
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The norm on ordinary ideles

The ordinary determinant norm is defined on the standard adele-unit carrier.
This file expresses that same norm in the restricted-product coordinates still
used by some consumers, and likewise transports its principal quotient.
-/



@[expose] public section

open scoped NumberField IsMulCommutative
open NumberField

noncomputable section

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The norm on standard idele groups. -/
noncomputable abbrev norm : IdeleGroup L →* IdeleGroup K :=
  NumberField.IdeleGroup.norm K L

@[simp]
theorem norm_relativeIdeleBaseChangeMulEquiv
    (z : RelativeIdeleGroup K L) :
    norm K L
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z) =
      RelativeIdeleGroup.norm K L z := by
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  apply Units.ext
  exact NumberField.AdeleRing.fieldNorm_baseChange K L (z : RelativeAdeleRing K L)

/-- The determinant-norm comparison identifies the relative image with the ordinary norm range. -/
theorem norm_range_eq_relativeNorm_range :
    (norm K L).range = (RelativeIdeleGroup.norm K L).range := by
  let e := relativeIdeleBaseChangeMulEquiv (K := K) (L := L)
  apply Subgroup.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨e.symm b, (norm_relativeIdeleBaseChangeMulEquiv K L (e.symm b)).symm.trans ?_⟩
    exact congrArg (norm K L) (e.apply_symm_apply b)
  · rintro ⟨b, rfl⟩
    exact ⟨e b, norm_relativeIdeleBaseChangeMulEquiv K L b⟩

/-- On principal ideles, the ordinary idele norm is induced by the
field norm. -/
@[simp]
theorem norm_principalIdele
    (x : Lˣ) :
    norm K L (principalIdele L x) =
      principalIdele K (Units.map (Algebra.norm K) x) :=
  NumberField.IdeleGroup.norm_unitEmbedding K L x


end IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The ordinary idele-class norm (N_{L/K} : C_L → C_K). -/
noncomputable abbrev ideleClassNorm :
    IdeleClassGroup L →* IdeleClassGroup K :=
  NumberField.IdeleClassGroup.norm K L

@[simp]
theorem ideleClassNorm_mk
    (a : IdeleGroup L) :
    ideleClassNorm K L (IdeleGroup.toStandardClass L a) =
      IdeleGroup.toStandardClass K (IdeleGroup.norm K L a) :=
  NumberField.IdeleClassGroup.norm_mk K L a

/-- The principal quotient sends an ordinary idèle norm to an idèle-class norm. -/
theorem ideleClassNorm_range_mem_mk_of_mem_ideleNorm_range (a : IdeleGroup K)
    (ha : a ∈ (IdeleGroup.norm K L).range) :
    IdeleGroup.toStandardClass K a ∈ (ideleClassNorm K L).range := by
  obtain ⟨b, rfl⟩ := ha
  exact ⟨IdeleGroup.toStandardClass L b, ideleClassNorm_mk K L b⟩

/-- The native continuous projection from the idele class group to the quotient
by the image of the ordinary idele-class norm. -/
noncomputable def ideleClassNormQuotientContinuousMonoidHom :
    IdeleClassGroup K →ₜ* (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) :=
  { QuotientGroup.mk' (ideleClassNorm K L).range with
    continuous_toFun := QuotientGroup.continuous_mk }
