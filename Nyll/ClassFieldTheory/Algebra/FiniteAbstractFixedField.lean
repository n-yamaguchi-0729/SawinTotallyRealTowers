/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.SetTheory.Cardinal.Finite
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension

/-!
# Fixed fields and quotient Galois groups

Closed subgroups of an ambient Galois group determine fixed fields.
This module identifies the relative quotient with the actual Galois group,
retains its action on field elements, and transports finite-index witnesses
to finite-dimensional fixed-field extensions. It uses no unit representation
or reciprocity theorem.
-/

@[expose] public section

namespace LocalClassFieldTheory
open RamificationTheory

open ClassFormation



noncomputable section

universe u v

variable (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The concrete fixed field represented by an abstract closed subgroup. -/
abbrev abstractFixedField (H : ClosedSubgroup (Gal(Ω/k))) :
    IntermediateField k Ω :=
  IntermediateField.fixedField H.toSubgroup

/-- The canonical algebra on the separable closure of the actual fixed field. -/
@[reducible] def finiteFixedFieldSeparableClosureAlgebra
    (K : Type u) [Field K] (H : FiniteAbstractField (Gal(SeparableClosure K/K))) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    Algebra F (SeparableClosure F) :=
  (separableClosure _ (AlgebraicClosure _)).toSubalgebra.algebra

/-- The fixed field's scalar action is the projection of its closure algebra. -/
@[reducible] def finiteFixedFieldSeparableClosureSMul
    (K : Type u) [Field K] (H : FiniteAbstractField (Gal(SeparableClosure K/K))) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    SMul F (SeparableClosure F) :=
  (finiteFixedFieldSeparableClosureAlgebra K H).toSMul

/-- Passing from an abstract field to its concrete fixed field
and back recovers the original closed subgroup. -/
theorem closedFixingSubgroup_abstractFixedField_eq
    (H : ClosedSubgroup (Gal(Ω/k))) :
    closedFixingSubgroup k Ω (abstractFixedField k Ω H) = H := by
  ext σ
  change σ ∈ (abstractFixedField k Ω H).fixingSubgroup ↔ σ ∈ H
  rw [InfiniteGalois.fixingSubgroup_fixedField H]
  rfl

omit [IsGalois k Ω] in
/-- Absolute finiteness in the abstract class-formation quotient presentation gives a
finite quotient of the ambient absolute Galois group by the same subgroup. -/
theorem ambientQuotientFiniteOfAbstractFinite
    (H : ClosedSubgroup (Gal(Ω/k)))
    (hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      (H.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup))) :
    Finite (Gal(Ω/k) ⧸ H.toSubgroup) := by
  apply Nat.finite_of_card_ne_zero
  change H.toSubgroup.index ≠ 0
  rw [← Subgroup.relIndex_top_right]
  change ((H.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup)).index ≠ 0
  exact @Subgroup.index_ne_zero_of_finite
    (baseField (Gal(Ω/k))).toSubgroup _
    ((H.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup))
    hfinite

omit [IsGalois k Ω] in
/-- An abstract field finite over the distinguished base is represented by
an open subgroup of the absolute Galois group. -/
theorem abstractFiniteClosedSubgroup_isOpen
    (H : ClosedSubgroup (Gal(Ω/k)))
    (hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      (H.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup))) :
    IsOpen H.carrier := by
  let : Finite (Gal(Ω/k) ⧸ H.toSubgroup) :=
    ambientQuotientFiniteOfAbstractFinite k Ω H hfinite
  let : Subgroup.FiniteIndex H.toSubgroup :=
    H.toSubgroup.finiteIndex_of_finite_quotient
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex H.toSubgroup H.isClosed'

/-- The fixed field of an abstract field finite over the distinguished base
is an actual finite field extension. -/
theorem abstractFixedField_finiteDimensional
    (H : ClosedSubgroup (Gal(Ω/k)))
    (hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      (H.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup))) :
    FiniteDimensional k (abstractFixedField k Ω H) := by
  apply (InfiniteGalois.isOpen_iff_finite
    (K := Ω) (abstractFixedField k Ω H)).1
  rw [InfiniteGalois.fixingSubgroup_fixedField H]
  exact abstractFiniteClosedSubgroup_isOpen k Ω H hfinite

omit [IsGalois k Ω] in
/-- Inclusion of abstract subgroups reverses to inclusion of their concrete
fixed fields. -/
theorem abstractFixedField_le {K L : ClosedSubgroup (Gal(Ω/k))}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    abstractFixedField k Ω K ≤ abstractFixedField k Ω L :=
  IntermediateField.fixedField_le hLK

/-- The abstract subgroup representing a fixed field is canonically the
absolute Galois group of the ambient extension over that fixed field. -/
def abstractSubgroupEquivGaloisGroup
    (H : ClosedSubgroup (Gal(Ω/k))) :
    H.toSubgroup ≃* Gal(Ω/abstractFixedField k Ω H) :=
  (MulEquiv.subgroupCongr
      (InfiniteGalois.fixingSubgroup_fixedField H).symm).trans
    (IntermediateField.fixingSubgroupEquiv (abstractFixedField k Ω H))

/-- States the theorem `abstractSubgroupEquivGaloisGroup_apply`. -/
@[simp]
theorem abstractSubgroupEquivGaloisGroup_apply
    (H : ClosedSubgroup (Gal(Ω/k))) (σ : H.toSubgroup) (x : Ω) :
    abstractSubgroupEquivGaloisGroup k Ω H σ x = σ.1 x :=
  rfl

/-- The upper fixed field, regarded as an intermediate field over the lower
fixed field in a relative abstract extension. -/
abbrev abstractRelativeFixedField
    {K L : ClosedSubgroup (Gal(Ω/k))}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    IntermediateField (abstractFixedField k Ω K) Ω :=
  IntermediateField.extendScalars (abstractFixedField_le k Ω hLK)

/-- Under the preceding Galois-group equivalence, the relative class-formation
subgroup is exactly the subgroup fixing the upper concrete field. -/
theorem map_extensionSubgroup_abstractSubgroupEquiv
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (L.toSubgroup.subgroupOf K.toSubgroup).map
        (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom =
      (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hσL : (σ.1 : Gal(Ω/k)) ∈ L :=
      hσ
    have hfix : ∀ y ∈ abstractFixedField k Ω L, σ.1 y = y := by
      have hσfix : σ.1 ∈ (abstractFixedField k Ω L).fixingSubgroup := by
        rw [InfiniteGalois.fixingSubgroup_fixedField L]
        exact hσL
      exact (IntermediateField.mem_fixingSubgroup_iff
        (abstractFixedField k Ω L) σ.1).1 hσfix
    exact hfix x hx
  · intro hτ
    let σ : K.toSubgroup :=
      (abstractSubgroupEquivGaloisGroup k Ω K).symm τ
    refine ⟨σ, ?_, (abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply τ⟩
    have hσfix : (σ.1 : Gal(Ω/k)) ∈
        (abstractFixedField k Ω L).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hτfix := (IntermediateField.mem_fixingSubgroup_iff
        (abstractRelativeFixedField k Ω hLK) τ).1 hτ x hx
      calc
        σ.1 x = abstractSubgroupEquivGaloisGroup k Ω K σ x :=
          (abstractSubgroupEquivGaloisGroup_apply k Ω K σ x).symm
        _ = τ x := by
          rw [show abstractSubgroupEquivGaloisGroup k Ω K σ = τ by
            exact (abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply τ]
        _ = x := hτfix
    rw [InfiniteGalois.fixingSubgroup_fixedField L] at hσfix
    exact hσfix

/-- Relative normality in the abstract class-formation framework is the actual normality of the
subgroup
fixing the upper field inside the lower field's absolute Galois group. -/
theorem abstractRelativeFixingSubgroup_normal
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal := by
  have hmap : ((L.toSubgroup.subgroupOf K.toSubgroup).map
      (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom).Normal :=
    hnormal.map (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom
      (abstractSubgroupEquivGaloisGroup k Ω K).surjective
  rw [map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK] at hmap
  exact hmap

/-- The concrete relative fixed field is Galois precisely from the normality
witness occurring in the abstract cyclic extension. -/
theorem abstractRelativeFixedField_isGalois
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    IsGalois (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (abstractRelativeFixedField k Ω hLK)).1
  exact abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal

/-- Restriction through the lower fixed field, followed by quotienting by
the upper fixing subgroup. -/
def abstractRelativeToAmbientQuotient
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    K.toSubgroup →*
      Gal(Ω/abstractFixedField k Ω K) ⧸
        (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (QuotientGroup.mk'
    (abstractRelativeFixedField k Ω hLK).fixingSubgroup).comp
      (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom

/-- The kernel of the preceding quotient map is the exact abstract class-formation
relative subgroup. -/
theorem abstractRelativeToAmbientQuotient_ker
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal).ker =
      (L.toSubgroup.subgroupOf K.toSubgroup) := by
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  ext σ
  change
    QuotientGroup.mk' (abstractRelativeFixedField k Ω hLK).fixingSubgroup
        (abstractSubgroupEquivGaloisGroup k Ω K σ) = 1 ↔
      σ ∈ (L.toSubgroup.subgroupOf K.toSubgroup)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [← map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK]
  constructor
  · rintro ⟨τ, hτ, hτσ⟩
    have : τ = σ :=
      (abstractSubgroupEquivGaloisGroup k Ω K).injective hτσ
    simpa [this] using hτ
  · intro hσ
    exact ⟨σ, hσ, rfl⟩

/-- The quotient map from the abstract lower subgroup is surjective. -/
theorem abstractRelativeToAmbientQuotient_surjective
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    Function.Surjective
      (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal) := by
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  intro q
  refine Quotient.inductionOn' q ?_
  intro τ
  refine ⟨(abstractSubgroupEquivGaloisGroup k Ω K).symm τ, ?_⟩
  change QuotientGroup.mk
    (abstractSubgroupEquivGaloisGroup k Ω K
      ((abstractSubgroupEquivGaloisGroup k Ω K).symm τ)) =
      QuotientGroup.mk τ
  rw [(abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply]

/-- The exact abstract class-formation quotient of a relative normal extension is the
ordinary quotient of the lower absolute Galois group by the upper fixing
subgroup. -/
def abstractExtensionQuotientEquivAmbient
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    let := hnormal
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup) ≃*
      Gal(Ω/abstractFixedField k Ω K) ⧸
        (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  intro sharedOwner1
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (QuotientGroup.quotientMulEquivOfEq
      (abstractRelativeToAmbientQuotient_ker
        k Ω K L hLK hnormal).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal)
      (abstractRelativeToAmbientQuotient_surjective
        k Ω K L hLK hnormal))

/-- The quotient group appearing in the abstract class-field-axiom predicate is
canonically the actual Galois group of the two concrete fixed fields. -/
def abstractExtensionQuotientEquivGaloisGroup
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    let := hnormal
    K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup) ≃*
      Gal(abstractRelativeFixedField k Ω hLK/abstractFixedField k Ω K) := by
  intro sharedOwner1
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  let H : ClosedSubgroup (Gal(Ω/abstractFixedField k Ω K)) :=
    closedFixingSubgroup (abstractFixedField k Ω K) Ω
      (abstractRelativeFixedField k Ω hLK)
  letI : H.toSubgroup.Normal := by
    exact abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (abstractExtensionQuotientEquivAmbient
      k Ω K L hLK hnormal).trans
    ((InfiniteGalois.normalAutEquivQuotient H).trans
      (AlgEquiv.autCongr
        (IntermediateField.equivOfEq
          (InfiniteGalois.fixedField_fixingSubgroup
            (abstractRelativeFixedField k Ω hLK)))))

/-- On a quotient representative, the concrete relative Galois
automorphism is restriction of the same ambient automorphism. -/
theorem abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (σ : K.toSubgroup)
    (x : abstractRelativeFixedField k Ω hLK) :
    let := hnormal
    σ.1 (x : Ω) =
      (((abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal
          (QuotientGroup.mk' (L.toSubgroup.subgroupOf K.toSubgroup) σ)) x :
        abstractRelativeFixedField k Ω hLK) : Ω) := by
  intro sharedOwner1
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  let H : ClosedSubgroup (Gal(Ω / abstractFixedField k Ω K)) :=
    closedFixingSubgroup (abstractFixedField k Ω K) Ω
      (abstractRelativeFixedField k Ω hLK)
  let : H.toSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  have hq :
      abstractExtensionQuotientEquivAmbient k Ω K L hLK hnormal
          (QuotientGroup.mk' (L.toSubgroup.subgroupOf K.toSubgroup) σ) =
        QuotientGroup.mk'
          (abstractRelativeFixedField k Ω hLK).fixingSubgroup
          (abstractSubgroupEquivGaloisGroup k Ω K σ) := by
    rfl
  rw [abstractExtensionQuotientEquivGaloisGroup, MulEquiv.trans_apply, hq,
    MulEquiv.trans_apply]
  change σ.1 (x : Ω) =
    ((((IntermediateField.equivOfEq
      (InfiniteGalois.fixedField_fixingSubgroup
        (abstractRelativeFixedField k Ω hLK))).autCongr
      (InfiniteGalois.normalAutEquivQuotient
        (closedFixingSubgroup (abstractFixedField k Ω K) Ω
          (abstractRelativeFixedField k Ω hLK))
        ((abstractSubgroupEquivGaloisGroup k Ω K σ :
            Gal(Ω / abstractFixedField k Ω K)) :
          Gal(Ω / abstractFixedField k Ω K) ⧸
            (abstractRelativeFixedField k Ω hLK).fixingSubgroup))) x :
      abstractRelativeFixedField k Ω hLK) : Ω)
  rw [InfiniteGalois.normalAutEquivQuotient_apply,
    AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
    IntermediateField.equivOfEq_apply]
  change σ.1 (x : Ω) =
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField H.toSubgroup)
      (abstractSubgroupEquivGaloisGroup k Ω K σ))
      ⟨(x : Ω), _⟩ : IntermediateField.fixedField H.toSubgroup) : Ω)
  rw [AlgEquiv.restrictNormalHom_apply]
  rfl

/-- In a finite abstract tower `L / K / k`, the concrete upper fixed field is
finite over the concrete lower fixed field. -/
theorem abstractFixedField_relativeFiniteDimensional
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      (K.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))) :
    let : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
      RingHom.toAlgebra
        (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
    FiniteDimensional (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) := by
  intro sharedOwner1
  let : IsScalarTower k (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      (K.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup)) :=
    hKfinite
  let : Finite
      (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) := hLKfinite
  let : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      (L.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup)) :=
    FiniteGaloisSubextension.finite_extension_trans hLK (le_baseField K)
  let : FiniteDimensional k (abstractFixedField k Ω L) :=
    abstractFixedField_finiteDimensional k Ω L inferInstance
  exact FiniteDimensional.right k
    (abstractFixedField k Ω K) (abstractFixedField k Ω L)

/-- The same relative finiteness statement in the scalar-extended
intermediate-field presentation used by infinite Galois theory. -/
theorem abstractRelativeFixedField_finiteDimensional
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      (K.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))) :
    FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) := by
  let : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
  let : FiniteDimensional (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) :=
    abstractFixedField_relativeFiniteDimensional
      k Ω K L hLK hKfinite hLKfinite
  let e : abstractFixedField k Ω L ≃ₗ[abstractFixedField k Ω K]
      abstractRelativeFixedField k Ω hLK :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finiteDimensional

/-- The abstract extension degree is the ordinary degree of the concrete
finite Galois extension represented by the same pair of fixed fields. -/
theorem finiteAbstractExtension_degree_eq_finrank
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      (K.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))) :
    ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) =
      Module.finrank (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  let := hnormal
  let : Finite
      (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) := hLKfinite
  let : FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKfinite hLKfinite
  let : IsGalois (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    abstractRelativeFixedField_isGalois k Ω K L hLK hnormal
  calc
    ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) =
        (L.toSubgroup.subgroupOf K.toSubgroup).index :=
      (DegreeData.FiniteAbstractExtension.ofInclusion L K
        hLK).extensionSubgroup_index_eq_degree.symm
    _ = Nat.card
        (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) :=
      Subgroup.index_eq_card (L.toSubgroup.subgroupOf K.toSubgroup)
    _ = Nat.card (Gal(abstractRelativeFixedField k Ω hLK/abstractFixedField k Ω K)) :=
      Nat.card_congr
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).toEquiv
    _ = Module.finrank (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) :=
      IsGalois.card_aut_eq_finrank
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK)

end
end LocalClassFieldTheory
