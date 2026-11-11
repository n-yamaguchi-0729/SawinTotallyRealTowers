/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SawinTotallyRealTowers.RealProPFrobeniusCut
public import Nyll.SawinTotallyRealTowers.MaximalRealProPOutside
public import Nyll.ProCGroups.Presentations.Profinite
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# The actual fixed field of a Frobenius cut

Take the fixed field of the constructed closed normal subgroup inside the
maximal real extension, then lift it into the same algebraic closure of ℚ.
Its Galois group is the actual quotient from S3.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

open ProCGroups.Presentations

variable (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
variable (v : ℕ → HeightOneSpectrum (𝓞 ℚ))

local instance fixedFieldMaximalIsGalois :
    IsGalois ℚ (maximalRealProPOutside p T) :=
  maximalRealProPOutside_isGalois p T

local instance kernelFixedIsGalois :
    IsGalois ℚ (IntermediateField.fixedField (realProPFrobeniusCutKernel p T v)) :=
  IsGalois.of_fixedField_normal_subgroup (realProPFrobeniusCutKernel p T v)

local instance (priority := high) kernelFixedNormal :
    Normal ℚ (IntermediateField.fixedField (realProPFrobeniusCutKernel p T v)) :=
  (kernelFixedIsGalois p T v).to_normal

local instance cutCompactSpace : CompactSpace (RealProPFrobeniusCut p T v) := by
  let M := maximalRealProPOutside p T
  let : CompactSpace Gal(M/ℚ) :=
    (InfiniteGalois.continuousMulEquivToLimit ℚ M).symm.compactSpace
  exact Quotient.compactSpace

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
  letI : IsGalois ℚ M := maximalRealProPOutside_isGalois p T
  let H : ClosedSubgroup (M ≃ₐ[ℚ] M) :=
    ⟨realProPFrobeniusCutKernel p T v, closedNormalClosure_isClosed _⟩
  let L : IntermediateField ℚ M := IntermediateField.fixedField H.toSubgroup
  exact (InfiniteGalois.normalAutEquivQuotient (k := ℚ) (K := M) H).trans
    (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L))

/-- On an original automorphism, the fixed-field comparison is actual restriction
followed by the same intermediate-field lift used to construct the cut field. -/
theorem realProPFrobeniusCutEquivFixedField_apply_mk
    (σ : maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) :
    realProPFrobeniusCutEquivFixedField p T v (realProPFrobeniusCutProjection p T v σ) =
      AlgEquiv.autCongr
        (IntermediateField.liftAlgEquiv
          (IntermediateField.fixedField (realProPFrobeniusCutKernel p T v)))
        (AlgEquiv.restrictNormalHom
          (IntermediateField.fixedField (realProPFrobeniusCutKernel p T v)) σ) :=
  rfl

/-- The comparison acts on an element of the lifted fixed field by the original
automorphism in the same ambient algebraic closure. -/
theorem realProPFrobeniusCutEquivFixedField_apply_lift
    (σ : maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)
    (x : IntermediateField.fixedField (realProPFrobeniusCutKernel p T v)) :
    (realProPFrobeniusCutEquivFixedField p T v (realProPFrobeniusCutProjection p T v σ)
      (IntermediateField.liftAlgEquiv
        (IntermediateField.fixedField (realProPFrobeniusCutKernel p T v)) x) :
      AlgebraicClosure ℚ) = (σ (x : maximalRealProPOutside p T) : AlgebraicClosure ℚ) := by
  let L : IntermediateField ℚ (maximalRealProPOutside p T) :=
    IntermediateField.fixedField (realProPFrobeniusCutKernel p T v)
  rw [realProPFrobeniusCutEquivFixedField_apply_mk]
  change ((IntermediateField.liftAlgEquiv L)
    (AlgEquiv.restrictNormalHom L σ ((IntermediateField.liftAlgEquiv L).symm
      (IntermediateField.liftAlgEquiv L x))) : AlgebraicClosure ℚ) = _
  rw [AlgEquiv.symm_apply_apply]
  exact congrArg (fun a : maximalRealProPOutside p T => (a : AlgebraicClosure ℚ))
    (AlgEquiv.restrictNormalHom_apply L σ x)

/-- Restriction to each normal intermediate layer gives the original ambient
action. This applies in particular to every finite Galois layer. -/
theorem realProPFrobeniusCutEquivFixedField_restrict_apply
    (E : IntermediateField ℚ (realProPFrobeniusFixedField p T v)) [Normal ℚ E]
    (σ : maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) (x : E) :
    (((AlgEquiv.restrictNormalHom E
      (realProPFrobeniusCutEquivFixedField p T v
        (realProPFrobeniusCutProjection p T v σ))) x :
        realProPFrobeniusFixedField p T v) : AlgebraicClosure ℚ) =
      (σ ⟨((x : realProPFrobeniusFixedField p T v) : AlgebraicClosure ℚ),
        realProPFrobeniusFixedField_le p T v (x : realProPFrobeniusFixedField p T v).property⟩ :
        AlgebraicClosure ℚ) := by
  rw [AlgEquiv.restrictNormalHom_apply]
  let L : IntermediateField ℚ (maximalRealProPOutside p T) :=
    IntermediateField.fixedField (realProPFrobeniusCutKernel p T v)
  have h := realProPFrobeniusCutEquivFixedField_apply_lift p T v σ
    ((IntermediateField.liftAlgEquiv L).symm (x : realProPFrobeniusFixedField p T v))
  let e := IntermediateField.liftAlgEquiv L
  let f := realProPFrobeniusCutEquivFixedField p T v
    (realProPFrobeniusCutProjection p T v σ)
  exact (congrArg (fun y : realProPFrobeniusFixedField p T v =>
    (f y : AlgebraicClosure ℚ))
      (e.apply_symm_apply (x : realProPFrobeniusFixedField p T v))).symm.trans h

/-- The original algebraic fixed-field comparison is continuous for the quotient
topology and the Krull topology. -/
theorem continuous_realProPFrobeniusCutEquivFixedField :
    Continuous (realProPFrobeniusCutEquivFixedField p T v) := by
  let L : IntermediateField ℚ (maximalRealProPOutside p T) :=
    IntermediateField.fixedField (realProPFrobeniusCutKernel p T v)
  apply (QuotientGroup.isQuotientMap_mk
    (realProPFrobeniusCutKernel p T v)).continuous_iff.mpr
  change Continuous ((AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L)) ∘
    (AlgEquiv.restrictNormalHom L))
  exact (RamificationTheory.Field.absoluteGaloisGroup.algEquiv_autCongr_continuous
    (IntermediateField.liftAlgEquiv L)).comp
      (InfiniteGalois.restrictNormalHom_continuous L)

/-- The actual quotient-to-fixed-field map is an isomorphism of topological groups. -/
noncomputable def realProPFrobeniusCutContinuousEquivFixedField :
    RealProPFrobeniusCut p T v ≃ₜ*
      (realProPFrobeniusFixedField p T v ≃ₐ[ℚ] realProPFrobeniusFixedField p T v) := by
  let : CompactSpace (RealProPFrobeniusCut p T v) := cutCompactSpace p T v
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (realProPFrobeniusCutEquivFixedField p T v).toMonoidHom
    (continuous_realProPFrobeniusCutEquivFixedField p T v)
    (realProPFrobeniusCutEquivFixedField p T v).bijective

/-- Upgrading continuity does not change the fixed-field action. -/
@[simp] theorem realProPFrobeniusCutContinuousEquivFixedField_apply
    (x : RealProPFrobeniusCut p T v) :
    realProPFrobeniusCutContinuousEquivFixedField p T v x =
      realProPFrobeniusCutEquivFixedField p T v x :=
  rfl

/-- Every chosen arithmetic Frobenius acts trivially on the actual cut field. -/
theorem realProPFrobeniusCutContinuousEquivFixedField_frobenius (n : ℕ) :
    realProPFrobeniusCutContinuousEquivFixedField p T v
      (realProPFrobeniusCutProjection p T v
        (maximalRealProPArithmeticFrobenius p T (v n))) = 1 := by
  rw [realProPFrobeniusCutProjection_frobenius]
  exact map_one _

/-- Conjugation on the quotient corresponds to conjugation of the actual
fixed-field automorphisms, with no fresh choice of a field realization. -/
theorem realProPFrobeniusCutContinuousEquivFixedField_conjugate
    (σ : maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)
    (x : RealProPFrobeniusCut p T v) :
    realProPFrobeniusCutContinuousEquivFixedField p T v
      (realProPFrobeniusCutProjection p T v σ * x *
        (realProPFrobeniusCutProjection p T v σ)⁻¹) =
      realProPFrobeniusCutEquivFixedField p T v (realProPFrobeniusCutProjection p T v σ) *
        realProPFrobeniusCutContinuousEquivFixedField p T v x *
        (realProPFrobeniusCutEquivFixedField p T v
          (realProPFrobeniusCutProjection p T v σ))⁻¹ := by
  simp only [map_mul, map_inv, realProPFrobeniusCutContinuousEquivFixedField_apply]

end ClassFieldTower.Sawin
