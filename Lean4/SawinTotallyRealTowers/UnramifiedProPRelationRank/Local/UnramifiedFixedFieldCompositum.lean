import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.UnramifiedDegreeBaseChange
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.FiniteUnramifiedField
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormContainment
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum
import ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Order.Hom.Lattice
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

set_option autoImplicit false

/-!
# The standard unramified extension as a compositum

The relative degree-`m` unramified fixed field over an actual finite
absolute subgroup is its compositum with the standard absolute unramified
extension of degree `f * m`, where `f` is its absolute residue degree.
-/

namespace LocalClassFieldTheory
open ClassFormation CyclicCohomology

/-- The fixed field of the relative degree kernel is the actual compositum
with the standard unramified extension of degree residue-degree times `m`. -/
theorem relativeUnramifiedFixedField_eq_sup_standard
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (intrinsicAbsoluteGalois K))
    (m : ℕ) (hm : 0 < m) :
    abstractFixedField K (SeparableClosure K)
      ((localResidueDatum K).unramifiedExtensionOfDegree
        (H.toFiniteResidueAbstractField (localResidueDatum K)) m hm) =
      abstractFixedField K (SeparableClosure K) H.field ⊔
        localFiniteUnramifiedField K ((H.residueDegree (localResidueDatum K) : ℕ) * m)
          (Nat.mul_pos (H.residueDegree (localResidueDatum K)).property hm) := by
  let D : DegreeData (intrinsicAbsoluteGalois K) := localResidueDatum K
  let E : FiniteAbstractFieldExtension (intrinsicAbsoluteGalois K) :=
    { field := H
      base := FiniteAbstractField.base (intrinsicAbsoluteGalois K)
      below := le_baseField H.field
      finiteQuotient := H.finite }
  let ER : DegreeData.FiniteResidueAbstractExtension D :=
    E.toFiniteResidueAbstractExtension D
  have hbase : (ER.base.residueDegree : ℕ) = 1 := by
    change ((FiniteAbstractField.base (intrinsicAbsoluteGalois K)).residueDegree D : ℕ) = 1
    rw [FiniteAbstractField.base_residueDegree]
    rfl
  have hres : (ER.residueDegree : ℕ) = (H.residueDegree D : ℕ) := by
    have h := ER.residueDegree_mul_absoluteResidueDegree D
    rw [hbase, mul_one] at h
    exact h
  have hsub := D.unramifiedExtensionOfDegree_baseChange_mul ER m hm
  have hresPNat : ER.residueDegree = H.residueDegree D := Subtype.ext hres
  rw [hresPNat] at hsub
  have hfields := congrArg
    (fun J : ClosedSubgroup (intrinsicAbsoluteGalois K) =>
      abstractFixedField K (SeparableClosure K) J) hsub
  have hsup (J₁ J₂ : ClosedSubgroup (intrinsicAbsoluteGalois K)) :
      abstractFixedField K (SeparableClosure K) (J₁ ⊓ J₂) =
        abstractFixedField K (SeparableClosure K) J₁ ⊔
          abstractFixedField K (SeparableClosure K) J₂ := by
    exact (InfiniteGalois.IntermediateFieldEquivClosedSubgroup
      (k := K) (K := SeparableClosure K)).symm.map_sup J₁ J₂
  rw [hsup] at hfields
  change abstractFixedField K (SeparableClosure K)
      (D.unramifiedExtensionOfDegree (H.toFiniteResidueAbstractField D) m hm) =
    abstractFixedField K (SeparableClosure K) H.field ⊔
      abstractFixedField K (SeparableClosure K)
        (D.unramifiedExtensionOfDegree
          ((FiniteAbstractField.base (intrinsicAbsoluteGalois K)).toFiniteResidueAbstractField D)
          ((H.residueDegree D : ℕ) * m)
          (Nat.mul_pos (H.residueDegree D).property hm)) at hfields
  change abstractFixedField K (SeparableClosure K)
      (D.unramifiedExtensionOfDegree (H.toFiniteResidueAbstractField D) m hm) =
    abstractFixedField K (SeparableClosure K) H.field ⊔
      abstractFixedField K (SeparableClosure K)
        (D.unramifiedExtensionOfDegree
          ((intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D)
          ((H.residueDegree D : ℕ) * m)
          (Nat.mul_pos (H.residueDegree D).property hm))
  rw [intrinsicFiniteAbstractBase_eq_base]
  exact hfields

end LocalClassFieldTheory
