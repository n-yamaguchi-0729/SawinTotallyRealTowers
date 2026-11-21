/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.OrdinaryNormClassField
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassField
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Narrow

/-!
# Actual realizations of the Hilbert class fields

The big and small Hilbert norm subgroups are closed and have finite
index.  The finite-index class-field construction therefore supplies
genuine finite abelian subextensions of the rational separable closure.
This file fixes those subextensions once and for all, names their actual
relative fixed fields, and identifies their determinant-norm ranges.

The resulting degrees are the orders of the corresponding reciprocity
quotients: the narrow class number for the big Hilbert class field and
the ordinary class number for the small Hilbert class field.
-/



@[expose] public section

universe u

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open Reciprocity

variable {K : Type u} [Field K] [NumberField K]

/-- The concrete finite Galois norm neighbourhood used to realize the
big Hilbert class field. -/
noncomputable abbrev bigHilbertClassFieldNormAmbient (K : Type u)
    [Field K] [NumberField K] : Type u :=
  closedFiniteIndexClassFieldNormAmbient
    (K := K)
    (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The concrete finite Galois norm neighbourhood used to realize the
small Hilbert class field. -/
noncomputable abbrev smallHilbertClassFieldNormAmbient (K : Type u)
    [Field K] [NumberField K] : Type u :=
  closedFiniteIndexClassFieldNormAmbient
    (K := K)
    (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The compatible abstract base subgroup for the actual big Hilbert
class-field realization. -/
noncomputable abbrev bigHilbertClassFieldBaseSubgroup (K : Type u)
    [Field K] [NumberField K] :=
  numberFieldTowerBaseSubgroup K (bigHilbertClassFieldNormAmbient K)

/-- The finite abelian subextension selected by the big-Hilbert norm
subgroup.  This is the actual class-field witness, rather than merely an
existence proposition. -/
noncomputable abbrev bigHilbertClassFieldSubextension (K : Type u)
    [Field K] [NumberField K] :
    FiniteAbelianSubextension
      (bigHilbertClassFieldBaseSubgroup K) :=
  ordinaryNormClassFieldSubextension K (bigHilbertClassFieldNormAmbient K)
    (bigHilbertClassFieldNormSubgroup (K := K))
    (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (bigHilbertClassFieldNormSubgroup (K := K))
      (bigHilbertClassFieldNormSubgroup_isClosed (K := K)))

/-- The compatible actual copy of the original number field occurring
as the base fixed field in the big-Hilbert realization. -/
noncomputable abbrev bigHilbertClassFieldBase (K : Type u)
    [Field K] [NumberField K] : Type :=
  ordinaryNormClassFieldBase K (bigHilbertClassFieldNormAmbient K)

/-- The actual big Hilbert class field selected inside the rational
separable closure. -/
noncomputable abbrev bigHilbertClassField (K : Type u)
    [Field K] [NumberField K] : Type :=
  ordinaryNormClassFieldExtension K (bigHilbertClassFieldNormAmbient K)
    (bigHilbertClassFieldNormSubgroup (K := K))
    (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (bigHilbertClassFieldNormSubgroup (K := K))
      (bigHilbertClassFieldNormSubgroup_isClosed (K := K)))

/-- The canonical equivalence from `K` to the actual base fixed field
used by the selected big Hilbert class field. -/
noncomputable abbrev bigHilbertClassFieldBaseEquiv :
    K ≃ₐ[ℚ] bigHilbertClassFieldBase K :=
  ordinaryNormClassFieldBaseEquiv K (bigHilbertClassFieldNormAmbient K)

/-- The big-Hilbert norm subgroup transported to the actual base fixed
field of the selected realization. -/
def bigHilbertClassFieldTransportedNormSubgroup :
    Subgroup (IdeleClassGroup (bigHilbertClassFieldBase K)) :=
  (bigHilbertClassFieldNormSubgroup (K := K)).map
    (ideleClassCongr
      (bigHilbertClassFieldBaseEquiv (K := K))).toMonoidHom

/-- The determinant-norm range of the actual big Hilbert class field is
exactly the transported big-Hilbert norm subgroup. -/
theorem bigHilbertClassField_ideleClassNorm_range :
    (_root_.ideleClassNorm
      (bigHilbertClassFieldBase K)
      (bigHilbertClassField K)).range =
      bigHilbertClassFieldTransportedNormSubgroup (K := K) := by
  simpa only [bigHilbertClassFieldTransportedNormSubgroup,
    bigHilbertClassFieldBaseEquiv, bigHilbertClassField,
    bigHilbertClassFieldBase] using
    (ordinaryNormClassField_ideleClassNorm_range_over_base K (bigHilbertClassFieldNormAmbient K)
      (bigHilbertClassFieldNormSubgroup (K := K))
      (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (bigHilbertClassFieldNormSubgroup (K := K))
      (bigHilbertClassFieldNormSubgroup_isClosed (K := K))))

private theorem ordinaryNormClassField_finrank_over_base_eq_index
    (L : Type u) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    Module.finrank (ordinaryNormClassFieldBase K L) (ordinaryNormClassFieldExtension K L H hLH)
      = H.index := by
  let F := ordinaryNormClassFieldBase K L
  let E := ordinaryNormClassFieldExtension K L H hLH
  let e := ideleClassCongr (ordinaryNormClassFieldBaseEquiv K L)
  calc
    Module.finrank F E = (_root_.ideleClassNorm F E).range.index :=
      (ideleClassNorm_index_eq_finrank_abelian F E).symm
    _ = (H.map e.toMonoidHom).index :=
      congrArg Subgroup.index (ordinaryNormClassField_ideleClassNorm_range_over_base K L H hLH)
    _ = H.index := Subgroup.index_map_equiv H e

/-- The degree of the actual big Hilbert class field is the narrow
class number. -/
theorem bigHilbertClassField_finrank_eq_narrowClassGroup_card :
    Module.finrank
        (bigHilbertClassFieldBase K)
        (bigHilbertClassField K) =
      Nat.card (RayClass.NarrowClassGroup K) := by
  calc
    Module.finrank
        (bigHilbertClassFieldBase K)
        (bigHilbertClassField K) =
        (bigHilbertClassFieldNormSubgroup (K := K)).index :=
      ordinaryNormClassField_finrank_over_base_eq_index
        (bigHilbertClassFieldNormAmbient K)
        (bigHilbertClassFieldNormSubgroup (K := K))
        (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (bigHilbertClassFieldNormSubgroup (K := K))
      (bigHilbertClassFieldNormSubgroup_isClosed (K := K)))
    _ =
        Nat.card
          (IdeleClassGroup K ⧸
            bigHilbertClassFieldNormSubgroup (K := K)) :=
      Subgroup.index_eq_card
        (bigHilbertClassFieldNormSubgroup (K := K))
    _ = Nat.card (RayClass.NarrowClassGroup K) :=
      Nat.card_congr
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K)).toEquiv

/-- The compatible abstract base subgroup for the actual small Hilbert
class-field realization. -/
noncomputable abbrev smallHilbertClassFieldBaseSubgroup (K : Type u)
    [Field K] [NumberField K] :=
  numberFieldTowerBaseSubgroup K (smallHilbertClassFieldNormAmbient K)

/-- The finite abelian subextension selected by the small-Hilbert norm
subgroup.  This named witness is the input used by principalization. -/
noncomputable abbrev smallHilbertClassFieldSubextension (K : Type u)
    [Field K] [NumberField K] :
    FiniteAbelianSubextension
      (smallHilbertClassFieldBaseSubgroup K) :=
  ordinaryNormClassFieldSubextension K (smallHilbertClassFieldNormAmbient K)
    (smallHilbertClassFieldNormSubgroup (K := K))
    (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (smallHilbertClassFieldNormSubgroup (K := K))
      (smallHilbertClassFieldNormSubgroup_isClosed (K := K)))

/-- The compatible actual copy of the original number field occurring
as the base fixed field in the small-Hilbert realization. -/
noncomputable abbrev smallHilbertClassFieldBase (K : Type u)
    [Field K] [NumberField K] : Type :=
  ordinaryNormClassFieldBase K (smallHilbertClassFieldNormAmbient K)

/-- The actual small Hilbert class field selected inside the rational
separable closure. -/
noncomputable abbrev smallHilbertClassField (K : Type u)
    [Field K] [NumberField K] : Type :=
  ordinaryNormClassFieldExtension K (smallHilbertClassFieldNormAmbient K)
    (smallHilbertClassFieldNormSubgroup (K := K))
    (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (smallHilbertClassFieldNormSubgroup (K := K))
      (smallHilbertClassFieldNormSubgroup_isClosed (K := K)))

/-- The canonical equivalence from `K` to the actual base fixed field
used by the selected small Hilbert class field. -/
noncomputable abbrev smallHilbertClassFieldBaseEquiv :
    K ≃ₐ[ℚ] smallHilbertClassFieldBase K :=
  ordinaryNormClassFieldBaseEquiv K (smallHilbertClassFieldNormAmbient K)

/-- The small-Hilbert norm subgroup transported to the actual base fixed
field of the selected realization. -/
def smallHilbertClassFieldTransportedNormSubgroup :
    Subgroup (IdeleClassGroup (smallHilbertClassFieldBase K)) :=
  (smallHilbertClassFieldNormSubgroup (K := K)).map
    (ideleClassCongr
      (smallHilbertClassFieldBaseEquiv (K := K))).toMonoidHom

/-- The determinant-norm range of the actual small Hilbert class field
is exactly the transported small-Hilbert norm subgroup. -/
theorem smallHilbertClassField_ideleClassNorm_range :
    (_root_.ideleClassNorm
      (smallHilbertClassFieldBase K)
      (smallHilbertClassField K)).range =
      smallHilbertClassFieldTransportedNormSubgroup (K := K) := by
  simpa only [smallHilbertClassFieldTransportedNormSubgroup,
    smallHilbertClassFieldBaseEquiv, smallHilbertClassField,
    smallHilbertClassFieldBase] using
    (ordinaryNormClassField_ideleClassNorm_range_over_base K (smallHilbertClassFieldNormAmbient K)
      (smallHilbertClassFieldNormSubgroup (K := K))
      (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (smallHilbertClassFieldNormSubgroup (K := K))
      (smallHilbertClassFieldNormSubgroup_isClosed (K := K))))

/-- The degree of the actual small Hilbert class field is the ordinary
class number. -/
theorem smallHilbertClassField_finrank_eq_classNumber :
    Module.finrank
        (smallHilbertClassFieldBase K)
        (smallHilbertClassField K) =
      NumberField.classNumber K := by
  calc
    Module.finrank
        (smallHilbertClassFieldBase K)
        (smallHilbertClassField K) =
        (smallHilbertClassFieldNormSubgroup (K := K)).index :=
      ordinaryNormClassField_finrank_over_base_eq_index
        (smallHilbertClassFieldNormAmbient K)
        (smallHilbertClassFieldNormSubgroup (K := K))
        (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (smallHilbertClassFieldNormSubgroup (K := K))
      (smallHilbertClassFieldNormSubgroup_isClosed (K := K)))
    _ =
        Nat.card
          (IdeleClassGroup K ⧸
            smallHilbertClassFieldNormSubgroup (K := K)) :=
      Subgroup.index_eq_card
        (smallHilbertClassFieldNormSubgroup (K := K))
    _ = NumberField.classNumber K :=
      smallHilbertClassFieldQuotient_card_eq_classNumber
        (K := K)

end GlobalClassFields
end GlobalClassFieldTheory
