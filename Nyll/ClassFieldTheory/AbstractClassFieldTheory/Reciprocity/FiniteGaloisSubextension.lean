/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields

/-!
# Finite Galois extensions above an abstract field

The norm topology is indexed by the actual finite Galois extensions
of a fixed abstract field.  This file packages those extensions and their
composita contravariantly as intersections of closed subgroups.
-/

@[expose] public section

namespace ClassFormation




noncomputable section

universe u v

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite Galois extension `L / K`, represented by `G_L ≤ G_K`. -/
structure FiniteGaloisSubextension (K : ClosedSubgroup G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The top-field subgroup is normal inside the base-field subgroup. -/
  normal : (field.toSubgroup.subgroupOf K.toSubgroup).Normal
  /-- The relative Galois quotient is finite. -/
  finite : Finite (K.toSubgroup ⧸ (field.toSubgroup.subgroupOf K.toSubgroup))

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- A finite Galois subextension is determined by its closed subgroup. -/
@[ext]
theorem ext {L₁ L₂ : FiniteGaloisSubextension K}
    (h : L₁.field = L₂.field) : L₁ = L₂ := by
  cases L₁
  cases L₂
  cases h
  rfl

/-- Forget only finiteness from a finite Galois subextension. -/
def toGaloisSubextension (L : FiniteGaloisSubextension K) :
    DegreeData.GaloisSubextension K where
  field := L.field
  below := L.below
  normal := L.normal

/-- Forget normality, retaining the underlying finite abstract extension.
This is the canonical bridge from a finite Galois subextension to the degree
and ramification API. -/
def toFiniteAbstractExtension (L : FiniteGaloisSubextension K) :
    DegreeData.FiniteAbstractExtension G where
  field := L.field
  base := K
  below := L.below
  finiteQuotient := L.finite

/-- The actual finite quotient `G(L/K)`, kept behind a named object
boundary. -/
def extensionQuotient (L : FiniteGaloisSubextension K) : Type u :=
  K.toSubgroup ⧸ (L.field.toSubgroup.subgroupOf K.toSubgroup)

/-- Structural unramifiedness of the underlying finite extension. -/
def IsUnramified (L : FiniteGaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the underlying finite extension. -/
def IsTotallyRamified (L : FiniteGaloisSubextension K)
    (D : DegreeData G) : Prop :=
  L.toFiniteAbstractExtension.IsTotallyRamified D

/-- A finite Galois subextension is represented by a normal subgroup. -/
instance extensionSubgroup_normalInstance (L : FiniteGaloisSubextension K) :
    (L.field.toSubgroup.subgroupOf K.toSubgroup).Normal :=
  L.normal

/-- The group structure transported across the named finite quotient
boundary. -/
instance extensionQuotient_groupInstance (L : FiniteGaloisSubextension K) :
    Group L.extensionQuotient := by
  change Group
    (K.toSubgroup ⧸ (L.field.toSubgroup.subgroupOf K.toSubgroup))
  infer_instance

/-- The quotient represented by a finite Galois subextension is finite. -/
instance extensionQuotient_finiteInstance (L : FiniteGaloisSubextension K) :
    Finite L.extensionQuotient :=
  L.finite

/-- Comparison with the quotient presentation used by the underlying group
library. -/
def extensionQuotientMulEquiv (L : FiniteGaloisSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ (L.field.toSubgroup.subgroupOf K.toSubgroup)) :=
  MulEquiv.refl _

/-- The canonical quotient projection for a finite Galois subextension. -/
def extensionQuotientMk (L : FiniteGaloisSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  QuotientGroup.mk' (L.field.toSubgroup.subgroupOf K.toSubgroup)

/-- The named finite Galois quotient projection agrees with `QuotientGroup.mk`. -/
@[simp]
theorem extensionQuotientMk_apply (L : FiniteGaloisSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k :
        K.toSubgroup ⧸ (L.field.toSubgroup.subgroupOf K.toSubgroup)) :=
  rfl

/-- A quotient representative is trivial exactly when it lies in the extension subgroup. -/
@[simp]
theorem extensionQuotientMk_eq_one_iff (L : FiniteGaloisSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMk k = 1 ↔
      k ∈ (L.field.toSubgroup.subgroupOf K.toSubgroup) := by
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff k).1
    calc
      (QuotientGroup.mk k :
          K.toSubgroup ⧸ (L.field.toSubgroup.subgroupOf K.toSubgroup)) =
          L.extensionQuotientMulEquiv (L.extensionQuotientMk k) :=
        (L.extensionQuotientMk_apply k).symm
      _ = L.extensionQuotientMulEquiv 1 := congrArg L.extensionQuotientMulEquiv h
      _ = 1 := L.extensionQuotientMulEquiv.map_one
  · intro hk
    apply L.extensionQuotientMulEquiv.injective
    rw [L.extensionQuotientMk_apply, L.extensionQuotientMulEquiv.map_one]
    exact (QuotientGroup.eq_one_iff k).2 hk

/-- The canonical projection onto the finite Galois quotient is surjective. -/
theorem extensionQuotientMk_surjective (L : FiniteGaloisSubextension K) :
    Function.Surjective L.extensionQuotientMk := by
  intro q
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
    (L.field.toSubgroup.subgroupOf K.toSubgroup) (L.extensionQuotientMulEquiv q)
  refine ⟨k, L.extensionQuotientMulEquiv.injective ?_⟩
  rw [L.extensionQuotientMk_apply]
  exact hk

/-- The finite and non-finite Galois bundles have the same quotient; this
named equivalence is the only public comparison needed by clients. -/
def toGaloisExtensionQuotientMulEquiv (L : FiniteGaloisSubextension K) :
    L.extensionQuotient ≃* L.toGaloisSubextension.extensionQuotient :=
  L.extensionQuotientMulEquiv.trans
    L.toGaloisSubextension.extensionQuotientMulEquiv.symm

/-- Eliminate a finite Galois quotient without exposing a chosen
representative. -/
protected theorem extensionQuotient_inductionOn
    (L : FiniteGaloisSubextension K) {motive : L.extensionQuotient → Prop}
    (q : L.extensionQuotient)
    (mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k)) :
    motive q := by
  exact @Quotient.inductionOn' K.toSubgroup
    (QuotientGroup.leftRel (L.field.toSubgroup.subgroupOf K.toSubgroup))
    motive q mk

/-- Bundling a finite Galois extension preserves its unramified predicate. -/
@[simp]
theorem toGaloisSubextension_isUnramified_iff
    (L : FiniteGaloisSubextension K) (D : DegreeData G) :
    L.toGaloisSubextension.IsUnramified D ↔ L.IsUnramified D :=
  Iff.rfl

/-- Bundling a finite Galois extension preserves its total-ramification predicate. -/
@[simp]
theorem toGaloisSubextension_isTotallyRamified_iff
    (L : FiniteGaloisSubextension K) (D : DegreeData G) :
    L.toGaloisSubextension.IsTotallyRamified D ↔ L.IsTotallyRamified D :=
  Iff.rfl

/-- Transport an unramifiedness proof through the finite-to-Galois
forgetful map. -/
theorem isUnramified_toGaloisSubextension
    (L : FiniteGaloisSubextension K) (D : DegreeData G)
    (hL : L.IsUnramified D) :
    L.toGaloisSubextension.IsUnramified D :=
  (L.toGaloisSubextension_isUnramified_iff D).2 hL

/-- Transport a total-ramification proof through the finite-to-Galois
forgetful map. -/
theorem isTotallyRamified_toGaloisSubextension
    (L : FiniteGaloisSubextension K) (D : DegreeData G)
    (hL : L.IsTotallyRamified D) :
    L.toGaloisSubextension.IsTotallyRamified D :=
  (L.toGaloisSubextension_isTotallyRamified_iff D).2 hL

/-- Unramifiedness is the canonical inertia-containment condition. -/
theorem isUnramified_iff_inertia_le (L : FiniteGaloisSubextension K)
    (D : DegreeData G) :
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup :=
  L.toFiniteAbstractExtension.isUnramified_iff_inertia_le D

/-- Total ramification is the canonical equality of degree images. -/
theorem isTotallyRamified_iff_image_le (L : FiniteGaloisSubextension K)
    (D : DegreeData G) :
    L.IsTotallyRamified D ↔
      K.toSubgroup.map D.degree.toMonoidHom ≤
        L.field.toSubgroup.map D.degree.toMonoidHom :=
  L.toFiniteAbstractExtension.isTotallyRamified_iff_image_le D

/-- Retain the finite-over-base endpoint bundles of a finite Galois
subextension of an abstract field which is finite over the distinguished
base. -/
noncomputable def toFiniteAbstractFieldExtension
    {K : FiniteAbstractField G} (L : FiniteGaloisSubextension K.field) :
    FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸
        (L.field.toSubgroup.subgroupOf K.field.toSubgroup)) :=
    L.finite
  exact FiniteAbstractFieldExtension.ofInclusion L.field K L.below

/-- Finiteness is transitive in a tower of abstract fields. -/
theorem finite_extension_trans
    {P L K : ClosedSubgroup G}
    (_hPL : P.toSubgroup ≤ L.toSubgroup)
    (_hLK : L.toSubgroup ≤ K.toSubgroup)
    [hPLfinite : Finite
      (L.toSubgroup ⧸ (P.toSubgroup.subgroupOf L.toSubgroup))]
    [hLKfinite : Finite
      (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] :
    Finite (K.toSubgroup ⧸ (P.toSubgroup.subgroupOf K.toSubgroup)) := by
  have hPL0 : P.toSubgroup.relIndex L.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite L.toSubgroup _
      (P.toSubgroup.subgroupOf L.toSubgroup) hPLfinite
  have hLK0 : L.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (L.toSubgroup.subgroupOf K.toSubgroup) hLKfinite
  apply Nat.finite_of_card_ne_zero
  change (P.toSubgroup.subgroupOf K.toSubgroup).index ≠ 0
  simpa [Subgroup.relIndex] using
    Subgroup.relIndex_ne_zero_trans hPL0 hLK0

/-- A finite extension remains finite over every intermediate field. -/
theorem finite_extension_over_intermediate
    {P M K : ClosedSubgroup G}
    (_hPK : P.toSubgroup ≤ K.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    (hPM : P.toSubgroup ≤ M.toSubgroup)
    [hPKfinite : Finite
      (K.toSubgroup ⧸ (P.toSubgroup.subgroupOf K.toSubgroup))] :
    Finite (M.toSubgroup ⧸ (P.toSubgroup.subgroupOf M.toSubgroup)) := by
  have hPK0 : P.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (P.toSubgroup.subgroupOf K.toSubgroup) hPKfinite
  have hPM0 : P.toSubgroup.relIndex M.toSubgroup ≠ 0 := by
    intro hzero
    have hmul := Subgroup.relIndex_mul_relIndex
      P.toSubgroup M.toSubgroup K.toSubgroup hPM hMK
    rw [hzero, zero_mul] at hmul
    exact hPK0 hmul.symm
  apply Nat.finite_of_card_ne_zero
  change (P.toSubgroup.subgroupOf M.toSubgroup).index ≠ 0
  simpa [Subgroup.relIndex] using hPM0

/-- Every intermediate field of a finite extension is finite over the
base.  No normality hypothesis is needed: this is the finite-index
statement for an arbitrary subgroup between the two endpoint subgroups. -/
theorem finite_intermediate_extension
    {P M K : ClosedSubgroup G}
    (_hPK : P.toSubgroup ≤ K.toSubgroup)
    (hPM : P.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hPKfinite : Finite
      (K.toSubgroup ⧸ (P.toSubgroup.subgroupOf K.toSubgroup))] :
    Finite (K.toSubgroup ⧸ (M.toSubgroup.subgroupOf K.toSubgroup)) := by
  have hPK0 : P.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (P.toSubgroup.subgroupOf K.toSubgroup) hPKfinite
  have hMK0 : M.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    intro hzero
    have hmul := Subgroup.relIndex_mul_relIndex
      P.toSubgroup M.toSubgroup K.toSubgroup hPM hMK
    rw [hzero, mul_zero] at hmul
    exact hPK0 hmul.symm
  apply Nat.finite_of_card_ne_zero
  change (M.toSubgroup.subgroupOf K.toSubgroup).index ≠ 0
  simpa [Subgroup.relIndex] using hMK0

/-- Base change of a finite Galois extension `M / K` to an arbitrary
intermediate field `L / K`.  Contravariantly, the compositum `ML` is the
intersection `G_M ∩ G_L`; normality and finite index are pulled back from
`G_M ◁ G_K`. -/
def baseChange (M : FiniteGaloisSubextension K) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) : FiniteGaloisSubextension L where
  field := L ⊓ M.field
  below := inf_le_left
  normal := by
    let f : L.toSubgroup →* K.toSubgroup := Subgroup.inclusion hLK
    have heq : ((L ⊓ M.field).toSubgroup.subgroupOf L.toSubgroup) =
        (M.field.toSubgroup.subgroupOf K.toSubgroup).comap f := by
      ext x
      change (x : G) ∈ L ⊓ M.field ↔ (x : G) ∈ M.field
      exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
    rw [heq]
    let : (M.field.toSubgroup.subgroupOf K.toSubgroup).Normal := M.normal
    infer_instance
  finite := by
    let f : L.toSubgroup →* K.toSubgroup := Subgroup.inclusion hLK
    let E := (M.field.toSubgroup.subgroupOf K.toSubgroup)
    have heq : ((L ⊓ M.field).toSubgroup.subgroupOf L.toSubgroup) = E.comap f := by
      ext x
      change (x : G) ∈ L ⊓ M.field ↔ (x : G) ∈ M.field
      exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
    let : Finite (K.toSubgroup ⧸ E) := M.finite
    let : E.Normal := M.normal
    have hE0 : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hrel0 : E.relIndex f.range ≠ 0 := by
      intro hzero
      have hdvd : E.relIndex f.range ∣ E.index :=
        E.relIndex_dvd_index_of_normal f.range
      rw [hzero, zero_dvd_iff] at hdvd
      exact hE0 hdvd
    apply Nat.finite_of_card_ne_zero
    change (((L ⊓ M.field).toSubgroup.subgroupOf L.toSubgroup)).index ≠ 0
    rw [heq, E.index_comap f]
    exact hrel0

/-- The trivial extension `K / K`. -/
def refl (K : ClosedSubgroup G) : FiniteGaloisSubextension K where
  field := K
  below := le_rfl
  normal := by
    have htop : (K.toSubgroup.subgroupOf K.toSubgroup) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact x.2
    rw [htop]
    infer_instance
  finite := by
    have htop : (K.toSubgroup.subgroupOf K.toSubgroup) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact x.2
    rw [htop]
    infer_instance

/-- The compositum `L₁L₂`, represented by `G_{L₁} ∩ G_{L₂}`. -/
def compositum (L₁ L₂ : FiniteGaloisSubextension K) :
    FiniteGaloisSubextension K where
  field := L₁.field ⊓ L₂.field
  below := fun _ h => L₁.below h.1
  normal := by
    have heq : ((L₁.field ⊓ L₂.field).toSubgroup.subgroupOf K.toSubgroup) =
        (L₁.field.toSubgroup.subgroupOf K.toSubgroup) ⊓
          (L₂.field.toSubgroup.subgroupOf K.toSubgroup) := by
      ext k
      constructor
      · intro hk
        exact ⟨hk.1, hk.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂⟩
    rw [heq]
    let : (L₁.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₁.normal
    let : (L₂.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₂.normal
    infer_instance
  finite := by
    have heq : ((L₁.field ⊓ L₂.field).toSubgroup.subgroupOf K.toSubgroup) =
        (L₁.field.toSubgroup.subgroupOf K.toSubgroup) ⊓
          (L₂.field.toSubgroup.subgroupOf K.toSubgroup) := by
      ext k
      constructor
      · intro hk
        exact ⟨hk.1, hk.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂⟩
    let : (L₁.field.toSubgroup.subgroupOf K.toSubgroup).FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
        (L₁.field.toSubgroup.subgroupOf K.toSubgroup) L₁.finite
    let : (L₂.field.toSubgroup.subgroupOf K.toSubgroup).FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
        (L₂.field.toSubgroup.subgroupOf K.toSubgroup) L₂.finite
    rw [heq]
    exact Subgroup.finite_quotient_of_finiteIndex

/-- Swapping the two factors does not change the finite Galois compositum. -/
theorem compositum_comm (L₁ L₂ : FiniteGaloisSubextension K) :
    L₁.compositum L₂ = L₂.compositum L₁ := by
  apply ext
  exact inf_comm L₁.field L₂.field

/-- The constructed Galois compositum satisfies the left comparison bound. -/
theorem compositum_le_left (L₁ L₂ : FiniteGaloisSubextension K) :
    (L₁.compositum L₂).field.toSubgroup ≤ L₁.field.toSubgroup :=
  inf_le_left

/-- The constructed Galois compositum satisfies the right comparison bound. -/
theorem compositum_le_right (L₁ L₂ : FiniteGaloisSubextension K) :
    (L₁.compositum L₂).field.toSubgroup ≤ L₂.field.toSubgroup :=
  inf_le_right

end FiniteGaloisSubextension

end GroupOnly


end
end ClassFormation
