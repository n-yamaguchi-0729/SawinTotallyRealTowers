/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H1NormalSubgroupDescent
import ProCGroups.ProP.FinitePGroupMaximal
import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom
import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension

set_option autoImplicit false
/-!
# Degree-one vanishing for finite p-extensions of a class formation

The cyclic class-field axiom already supplies `H¹ = 0` through cyclic Tate
periodicity.  This file propagates that source result to every finite
`p`-extension by induction on its quotient order.

The induction works with cocycles on the ambient closed subgroups.  After
subtracting a primitive on a maximal subgroup, the cocycle descends to the
cyclic quotient.  This avoids introducing intermediate-field representation
comparisons or assuming a higher-degree class-formation theorem.
-/

open CategoryTheory groupCohomology

namespace ClassFieldTower.Cohomology

open ClassFormation CyclicCohomology

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)

include hcf

omit [IsTopologicalGroup G] in
/-- The cyclic class-field axiom produces an invariant primitive for a
cocycle on the base subgroup vanishing on the top-field subgroup. -/
theorem cyclicClassFormationH1Primitive
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (hcyc : IsCyclic L.extensionQuotient)
    (z : cocycles₁ (Rep.res K.field.toSubgroup.subtype A))
    (hz : ∀ n : extensionSubgroup K.field L.field L.below, z n.1 = 0) :
    ∃ a : A, (∀ l : L.field.toSubgroup, A.ρ l.1 a = a) ∧
      ∀ k : K.field.toSubgroup, A.ρ k.1 a - a = z k := by
  let : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    L.finite
  let : IsCyclic (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    hcyc
  let : Fintype (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below)
  let E : FiniteCyclicSubextension K :=
    { field := L.field
      below := L.below
      normal := L.normal
      finite := L.finite
      generator := g
      generates := hg }
  let d := descendedH1Cocycle (Rep.res K.field.toSubgroup.subtype A)
    (extensionSubgroup K.field L.field L.below) z hz
  have hT := hcf.tateHMinusOne_isZero K E
  have hH : Limits.IsZero (H1 (E.fixedRepresentation A)) :=
    hT.of_iso (finiteCyclicH1IsoTateHMinusOne (E.fixedRepresentation A) g hg)
  have hd : H1π (E.fixedRepresentation A) d = 0 :=
    @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hH) _ _
  obtain ⟨a, ha⟩ := (H1π_eq_zero_iff d).mp hd
  refine ⟨a.1, ?_, ?_⟩
  · intro l
    exact a.2 ⟨⟨l.1, L.below l.2⟩, l.2⟩
  · intro k
    exact congrArg Subtype.val (congrFun ha (QuotientGroup.mk' _ k))

omit hcf in
/-- A proper subgroup of a finite group has strictly smaller order. -/
private theorem subgroup_card_lt_of_ne_top
    {Q : Type} [Group Q] [Finite Q] (S : Subgroup Q) (hS : S ≠ ⊤) :
    Nat.card S < Nat.card Q := by
  let := Fintype.ofFinite Q
  let := Fintype.ofFinite S
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_lt_of_injective_not_surjective
      S.subtype S.subtype_injective (by
        intro hsurj
        apply hS
        rw [eq_top_iff]
        intro q _
        obtain ⟨s, hs⟩ := hsurj q
        rw [← hs]
        exact s.property))

/-- Produce an invariant primitive in every finite `p`-extension by
restricting to a maximal subgroup and then descending to its cyclic quotient. -/
theorem pClassFormationH1Primitive
    {p : ℕ} [Fact p.Prime]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (hP : IsPGroup p L.extensionQuotient)
    (z : cocycles₁ (Rep.res K.field.toSubgroup.subtype A))
    (hz : ∀ n : extensionSubgroup K.field L.field L.below, z n.1 = 0) :
    ∃ a : A, (∀ l : L.field.toSubgroup, A.ρ l.1 a = a) ∧
      ∀ k : K.field.toSubgroup, A.ρ k.1 a - a = z k := by
  classical
  by_cases hcyc : IsCyclic L.extensionQuotient
  · exact cyclicClassFormationH1Primitive A hcf K L hcyc z hz
  have hnt : Nontrivial L.extensionQuotient := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    let := hs
    exact hcyc inferInstance
  let := hnt
  obtain ⟨S, hS⟩ := IsCoatomic.exists_coatom (Subgroup L.extensionQuotient)
  let : S.Normal := ClassFieldTower.ProP.isCoatom_normal_of_isPGroup hP hS
  let M := L.intermediateField S
  let V := L.lowerFiniteGalois S
  let W := L.intermediateFiniteGalois S inferInstance
  let : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K.field (le_baseField K.field)) := K.finite
  let : Finite (K.field.toSubgroup ⧸
      extensionSubgroup K.field M (L.intermediateField_le_base S)) :=
    L.intermediateField_finite S
  let MF : FiniteAbstractField G :=
    ⟨M, FiniteGaloisSubextension.finite_extension_trans
      (L.intermediateField_le_base S) (le_baseField K.field)⟩
  have hPV : IsPGroup p V.extensionQuotient :=
    (hP.to_subgroup S).of_equiv (L.lowerQuotientEquiv S).symm
  have hcard : Nat.card V.extensionQuotient < Nat.card L.extensionQuotient := by
    rw [Nat.card_congr (L.lowerQuotientEquiv S).toEquiv]
    exact subgroup_card_lt_of_ne_top S hS.ne_top
  let zM : cocycles₁ (Rep.res M.toSubgroup.subtype A) :=
    ⟨fun m => z (Subgroup.inclusion (L.intermediateField_le_base S) m),
      (mem_cocycles₁_iff _).mpr (fun m n =>
        (mem_cocycles₁_iff z).mp z.2
          (Subgroup.inclusion (L.intermediateField_le_base S) m)
          (Subgroup.inclusion (L.intermediateField_le_base S) n))⟩
  have hzM : ∀ n : extensionSubgroup MF.field V.field V.below, zM n.1 = 0 := by
    intro n
    exact hz ⟨⟨n.1.1, L.below n.2⟩, n.2⟩
  obtain ⟨a, haFixed, ha⟩ := pClassFormationH1Primitive MF V hPV zM hzM
  let ba : cocycles₁ (Rep.res K.field.toSubgroup.subtype A) :=
    ⟨d₀₁ (Rep.res K.field.toSubgroup.subtype A) a,
      d₀₁_apply_mem_cocycles₁ (A := Rep.res K.field.toSubgroup.subtype A) a⟩
  let z' : cocycles₁ (Rep.res K.field.toSubgroup.subtype A) := z - ba
  have hz' : ∀ n : extensionSubgroup K.field W.field W.below, z' n.1 = 0 := by
    intro n
    change z n.1 - (A.ρ n.1.1 a - a) = 0
    exact sub_eq_zero.mpr (ha ⟨n.1.1, n.2⟩).symm
  let : IsCyclic (L.upperQuotient S) := by
    change IsCyclic (L.extensionQuotient ⧸ S)
    exact ClassFieldTower.ProP.quotient_isCyclic_of_isCoatom hS
  have hWcyc : IsCyclic W.extensionQuotient :=
    isCyclic_of_surjective (L.upperQuotientEquiv S).toMonoidHom
      (L.upperQuotientEquiv S).surjective
  obtain ⟨b, hbFixed, hb⟩ := cyclicClassFormationH1Primitive A hcf K W hWcyc z' hz'
  refine ⟨a + b, ?_, ?_⟩
  · intro l
    rw [map_add, haFixed l, hbFixed ⟨l.1, L.field_le_intermediateField S l.2⟩]
  · intro k
    have hk := hb k
    change A.ρ k.1 b - b = z k - (A.ρ k.1 a - a) at hk
    rw [map_add]
    calc
      _ = (A.ρ k.1 a - a) + (A.ρ k.1 b - b) := by abel
      _ = z k := by rw [hk]; abel
termination_by Nat.card L.extensionQuotient
decreasing_by exact hcard

/-- The cyclic class-field axiom implies degree-one vanishing for the actual
fixed representation of every finite `p`-extension. -/
theorem pClassFormationH1_subsingleton
    {p : ℕ} [Fact p.Prime]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (hP : IsPGroup p L.extensionQuotient) :
    Subsingleton (H1 (extensionFixedRepresentation A K.field L.field L.below L.normal)) := by
  let B := extensionFixedRepresentation A K.field L.field L.below L.normal
  have hzero (x : H1 B) : x = 0 := by
    refine H1_induction_on x ?_
    intro z
    let q := QuotientGroup.mk' (extensionSubgroup K.field L.field L.below)
    let zK : cocycles₁ (Rep.res K.field.toSubgroup.subtype A) :=
      ⟨fun k => (z (q k)).1,
        (mem_cocycles₁_iff _).mpr (fun k l =>
          congrArg Subtype.val ((mem_cocycles₁_iff z).mp z.2 (q k) (q l)))⟩
    have hzK : ∀ n : extensionSubgroup K.field L.field L.below, zK n.1 = 0 := by
      intro n
      change (z (q n.1)).1 = 0
      have hq : q n.1 = 1 := (QuotientGroup.eq_one_iff n.1).mpr n.2
      rw [hq, cocycles₁_map_one]
      rfl
    obtain ⟨a, haFixed, ha⟩ := pClassFormationH1Primitive A hcf K L hP zK hzK
    let aB : B := ⟨a, fun n => haFixed ⟨n.1.1, n.2⟩⟩
    apply (H1π_eq_zero_iff z).mpr
    refine ⟨aB, ?_⟩
    funext g
    refine QuotientGroup.induction_on g (fun k => ?_)
    apply Subtype.ext
    exact ha k
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

end

end ClassFieldTower.Cohomology
