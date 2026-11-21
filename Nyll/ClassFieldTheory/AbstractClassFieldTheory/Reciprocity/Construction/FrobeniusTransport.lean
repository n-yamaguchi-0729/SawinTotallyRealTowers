/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormComparison
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField
public import Nyll.ProCGroups.Generation.Basic
public import Nyll.ProCGroups.Topologies.ContinuousQuotientEquiv

/-!
# Frobenius transport along a comparison of Galois groups

The normalized degree determines positivity and the relative inertia
subgroup. The same comparison transports the closed subgroup fixing the
field of a Frobenius lift.
-/

@[expose] public section

open CyclicCohomology

noncomputable section

namespace ClassFormation.DegreeData

universe u v

variable {G : Type u} {G' : Type v} [Group G] [Group G'] [TopologicalSpace G]
  [TopologicalSpace G'] [IsTopologicalGroup G] [IsTopologicalGroup G']
  (D : DegreeData G) (D' : DegreeData G')
  (R : D.FiniteResidueAbstractField) (R' : D'.FiniteResidueAbstractField)
  (J : ClosedSubgroup G) (J' : ClosedSubgroup G')
  (hJ : J.toSubgroup ≤ R.field.toSubgroup) (hJ' : J'.toSubgroup ≤ R'.field.toSubgroup)
  [(extensionSubgroup R.field J hJ).Normal] [(extensionSubgroup R'.field J' hJ').Normal]
  (e : R.field.toSubgroup ≃ₜ* R'.field.toSubgroup)
  (he : ∀ x : R.field.toSubgroup, x.1 ∈ J.toSubgroup ↔ (e x).1 ∈ J'.toSubgroup)
  (hd : ∀ x : R.field.toSubgroup, D.normalizedDegree R x = D'.normalizedDegree R' (e x))

include he hd in
omit [IsTopologicalGroup G] [IsTopologicalGroup G']
    [(extensionSubgroup R.field J hJ).Normal] [(extensionSubgroup R'.field J' hJ').Normal] in
/-- A comparison preserving membership and normalized degree maps the original relative inertia. -/
theorem extensionInertia_map :
    (D.extensionInertiaWithin R.field J hJ).map e.toMulEquiv.toMonoidHom =
      D'.extensionInertiaWithin R'.field J' hJ' := by
  have hInertia (x : R.field.toSubgroup) :
      x ∈ D.extensionInertiaWithin R.field J hJ ↔
        e x ∈ D'.extensionInertiaWithin R'.field J' hJ' := by
    change (x.1 ∈ J.toSubgroup ∧ x ∈ D.fieldInertiaWithin R.field) ↔
      ((e x).1 ∈ J'.toSubgroup ∧ e x ∈ D'.fieldInertiaWithin R'.field)
    rw [← D.normalizedDegree_ker R, ← D'.normalizedDegree_ker R']
    change (x.1 ∈ J.toSubgroup ∧ D.normalizedDegree R x = 1) ↔
      ((e x).1 ∈ J'.toSubgroup ∧ D'.normalizedDegree R' (e x) = 1)
    rw [he x, hd x]
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  constructor
  · rintro ⟨z, hz, hzx⟩
    exact (hInertia x).1 (e.injective hzx ▸ hz)
  · intro hx
    exact ⟨x, (hInertia x).2 hx, rfl⟩

/-- The lower-group comparison induces a continuous equivalence between
the actual quotients by relative inertia. -/
def extensionInertiaQuotientCongr :
    (R.field.toSubgroup ⧸ D.extensionInertiaWithin R.field J hJ) ≃ₜ*
      (R'.field.toSubgroup ⧸ D'.extensionInertiaWithin R'.field J' hJ') :=
  ProCGroups.QuotientGroup.congrₜ _ _ e
    (extensionInertia_map D D' R R' J J' hJ hJ' e he hd)

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
/-- The induced quotient comparison takes the class of an automorphism to
the class of its transported representative. -/
@[simp]
theorem extensionInertiaQuotientCongr_mk (x : R.field.toSubgroup) :
    extensionInertiaQuotientCongr D D' R R' J J' hJ hJ' e he hd (QuotientGroup.mk x) =
      QuotientGroup.mk (e x) :=
  rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
/-- The two normalized degrees on the inertia quotients agree after
transport. -/
theorem extensionNormalizedDegree_extensionInertiaQuotientCongr
    (x : R.field.toSubgroup ⧸ D.extensionInertiaWithin R.field J hJ) :
    D'.extensionNormalizedDegree R' J' hJ'
        (extensionInertiaQuotientCongr D D' R R' J J' hJ hJ' e he hd x) =
      D.extensionNormalizedDegree R J hJ x := by
  refine Quotient.inductionOn' x ?_
  intro g
  exact (hd g).symm

/-- The actual positive Frobenius lift is sent to the lift of the same
positive normalized degree. -/
def transportFrobenius (σ : D.FrobeniusElements R J hJ) :
    D'.FrobeniusElements R' J' hJ' :=
  ⟨extensionInertiaQuotientCongr D D' R R' J J' hJ hJ' e he hd σ.1, by
    obtain ⟨n, hn, hσ⟩ := σ.2
    exact ⟨n, hn, (extensionNormalizedDegree_extensionInertiaQuotientCongr
      D D' R R' J J' hJ hJ' e he hd σ.1).trans hσ⟩⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
/-- Frobenius transport respects the restriction to the finite relative
Galois group. -/
theorem transportFrobenius_restriction (σ : D.FrobeniusElements R J hJ) :
    D'.frobeniusRestriction R' J' hJ' (transportFrobenius D D' R R' J J' hJ hJ' e he hd σ) =
      relativeCosetEquivOfMulEquiv hJ hJ' e.toMulEquiv he
        (D.frobeniusRestriction R J hJ σ) := by
  change D'.extensionRestriction R'.field J' hJ'
    (extensionInertiaQuotientCongr D D' R R' J J' hJ hJ' e he hd σ.1) =
      relativeCosetEquivOfMulEquiv hJ hJ' e.toMulEquiv he (D.extensionRestriction R.field J hJ σ.1)
  let eQ := extensionInertiaQuotientCongr D D' R R' J J' hJ hJ' e he hd
  have h (q : R.field.toSubgroup ⧸ D.extensionInertiaWithin R.field J hJ) :
      D'.extensionRestriction R'.field J' hJ' (eQ q) =
        relativeCosetEquivOfMulEquiv hJ hJ' e.toMulEquiv he
          (D.extensionRestriction R.field J hJ q) := by
    refine Quotient.inductionOn' q ?_
    intro g
    rfl
  exact h σ.1

/-- Membership in the actual Frobenius fixed subgroup is preserved and
reflected by the lower-group comparison. -/
theorem transportFrobenius_mem_fixedField_iff
    (σ : D.FrobeniusElements R J hJ) (g : R.field.toSubgroup) :
    g.1 ∈ (D.frobeniusFixedField R J hJ σ).toSubgroup ↔
      (e g).1 ∈ (D'.frobeniusFixedField R' J' hJ'
        (transportFrobenius D D' R R' J J' hJ hJ' e he hd σ)).toSubgroup := by
  let σ' := transportFrobenius D D' R R' J J' hJ hJ' e he hd σ
  let eQ := extensionInertiaQuotientCongr D D' R R' J J' hJ hJ' e he hd
  change g ∈ (D.frobeniusFixedField R J hJ σ).toSubgroup.subgroupOf R.field.toSubgroup ↔
    e g ∈ (D'.frobeniusFixedField R' J' hJ' σ').toSubgroup.subgroupOf R'.field.toSubgroup
  rw [D.extensionSubgroup_frobeniusFixedField, D'.extensionSubgroup_frobeniusFixedField,
    D.mem_frobeniusFixedSubgroupWithin_iff, D'.mem_frobeniusFixedSubgroupWithin_iff]
  simp only [frobeniusClosure, Set.range_unique]
  let q : R.field.toSubgroup ⧸ D.extensionInertiaWithin R.field J hJ := QuotientGroup.mk g
  change q ∈ (closedSubgroupGenerated {σ.1}).toSubgroup ↔
    eQ q ∈ (closedSubgroupGenerated {eQ σ.1}).toSubgroup
  constructor
  · exact map_mem_closedSubgroupGenerated_singleton
      (ContinuousMonoidHom.toContinuousMonoidHom eQ) σ.1
  · intro h
    have h' := map_mem_closedSubgroupGenerated_singleton
      (ContinuousMonoidHom.toContinuousMonoidHom eQ.symm) (eQ σ.1) h
    change eQ.symm (eQ q) ∈ (closedSubgroupGenerated {eQ.symm (eQ σ.1)}).toSubgroup at h'
    simpa only [eQ.symm_apply_apply] using h'

end ClassFormation.DegreeData
