/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation

/-!
# Underlying algebraic closed finite-index reciprocity

The algebraic equivalence is obtained by forgetting topology from the named
continuous provider.  This avoids a second specialization of the full finite
global reciprocity instance tower.
-/



@[expose] public section

universe u

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

attribute [local instance]
  Reciprocity.globalNormResidueIdeleClassCommGroup
  Reciprocity.globalNormResidueIdeleClassIsMulCommutative

variable {K : Type u} [Field K] [NumberField K]

/-- Global reciprocity for the selected class field, stated over the original
number field and directly modulo its defining subgroup. -/
noncomputable abbrev closedFiniteIndexClassFieldGaloisEquivNormQuotient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Gal((closedFiniteIndexClassField
          (K := K) H hclosed) / K) ≃*
      IdeleClassGroup K ⧸ H :=
  (closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient
    (K := K) H hclosed).toMulEquiv

end GlobalClassFields
end GlobalClassFieldTheory
