import SawinTotallyRealTowers.RealProPFrobeniusCut
import SawinTotallyRealTowers.MaximalRealProPOutside
import ProCGroups.Presentations.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

set_option autoImplicit false

/-!
# The actual fixed field of a Frobenius cut

Take the fixed field of the constructed closed normal subgroup inside the
maximal real extension, then lift it into the same algebraic closure of ℚ.
Its Galois group is the actual quotient from S3.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

open ProCGroups.Presentations

variable (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
variable (v : ℕ → HeightOneSpectrum (𝓞 ℚ))

private local instance fixedFieldMaximalIsGalois :
    IsGalois ℚ (maximalRealProPOutside p T) :=
  maximalRealProPOutside_isGalois p T

/-- The Frobenius-cut fixed field in the original algebraic closure. -/
def realProPFrobeniusFixedField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.lift (IntermediateField.fixedField (realProPFrobeniusCutKernel p T v))

/-- The constructed cut field is contained in its actual maximal parent. -/
theorem realProPFrobeniusFixedField_le :
    realProPFrobeniusFixedField p T v ≤ maximalRealProPOutside p T :=
  IntermediateField.lift_le _

/-- Normality of the actual cut kernel makes its fixed field Galois over ℚ. -/
theorem realProPFrobeniusFixedField_isGalois :
    IsGalois ℚ (realProPFrobeniusFixedField p T v) := by
  let L : IntermediateField ℚ (maximalRealProPOutside p T) :=
    IntermediateField.fixedField (realProPFrobeniusCutKernel p T v)
  have hL : IsGalois ℚ L :=
    IsGalois.of_fixedField_normal_subgroup (realProPFrobeniusCutKernel p T v)
  exact (IntermediateField.liftAlgEquiv L).transfer_galois.mp hL

/-- Total reality descends to the internal fixed field and is preserved by its lift. -/
theorem realProPFrobeniusFixedField_isTotallyReal :
    IsTotallyReal (realProPFrobeniusFixedField p T v) := by
  let L : IntermediateField ℚ (maximalRealProPOutside p T) :=
    IntermediateField.fixedField (realProPFrobeniusCutKernel p T v)
  let : IsTotallyReal (maximalRealProPOutside p T) :=
    maximalRealProPOutside_isTotallyReal p T
  let : IsTotallyReal L := inferInstance
  exact IsTotallyReal.ofRingEquiv (IntermediateField.liftAlgEquiv L).toRingEquiv

/-- The actual S3 quotient is the full Galois group of the constructed cut field. -/
def realProPFrobeniusCutEquivFixedField :
    RealProPFrobeniusCut p T v ≃*
      (realProPFrobeniusFixedField p T v ≃ₐ[ℚ] realProPFrobeniusFixedField p T v) := by
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := maximalRealProPOutside p T
  let H : ClosedSubgroup (M ≃ₐ[ℚ] M) :=
    ⟨realProPFrobeniusCutKernel p T v, closedNormalClosure_isClosed _⟩
  let L : IntermediateField ℚ M := IntermediateField.fixedField H.toSubgroup
  exact (InfiniteGalois.normalAutEquivQuotient (k := ℚ) (K := M) H).trans
    (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L))

end ClassFieldTower.Sawin
