/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.ProC.Quotients.ClosedNormal
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic

/-!
# Finite characters detect conjugation on topological abelianization

Distinct classes in the topological abelianization of a profinite group are
separated by a continuous homomorphism to an actual finite discrete abelian
quotient.  Applied to a normal subgroup, this identifies trivial conjugation
on its abelianization with invariance of all its finite continuous characters.
-/

open scoped Topology

namespace ProCGroups.Abelian

universe u v

namespace TopologicalAbelianization

/-- A finite discrete abelian quotient separates two distinct abelianization
classes.  The character is the composite of abelianization with an open-normal
quotient, so its finiteness and continuity are supplied by the construction. -/
theorem exists_finite_character_of_mk_ne
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {x y : G} (hxy : mk G x ≠ mk G y) :
    ∃ (A : Type u) (_ : CommGroup A) (_ : TopologicalSpace A)
      (_ : Finite A) (_ : DiscreteTopology A),
      ∃ χ : G →ₜ* A, χ x ≠ χ y := by
  let B : Type u := _root_.TopologicalAbelianization G
  have : TotallyDisconnectedSpace B :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator G) (Subgroup.isClosed_closedCommutator G)
  have hdiff : mk G x / mk G y ≠ 1 := by
    intro h
    exact hxy (div_eq_one.mp h)
  obtain ⟨U, hU⟩ := ProCGroups.ProC.exists_openNormalSubgroup_not_mem
    (G := B) (x := mk G x / mk G y) hdiff
  let A : Type u := B ⧸ (U : Subgroup B)
  let χ : G →ₜ* A :=
    (ProCGroups.ProC.OpenNormalSubgroup.quotientProj U).comp (mkₜ G)
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, χ, ?_⟩
  intro hχ
  apply hU
  apply (QuotientGroup.eq_one_iff
    (N := (U : Subgroup B)) (mk G x / mk G y)).mp
  change ProCGroups.ProC.OpenNormalSubgroup.quotientProj U
    (mk G x / mk G y) = 1
  rw [map_div]
  exact div_eq_one.mpr hχ

/-- Equality of abelianization classes is equivalent to equality under all
continuous characters with finite discrete abelian targets. -/
theorem mk_eq_iff_finite_characters_eq
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {x y : G} :
    mk G x = mk G y ↔
      ∀ (A : Type u) [CommGroup A] [TopologicalSpace A]
        [Finite A] [DiscreteTopology A],
        ∀ χ : G →ₜ* A, χ x = χ y := by
  constructor
  · intro h A _instCommGroupA _instTopologyA _instFiniteA _instDiscreteA χ
    calc
      χ x = lift χ (mk G x) := (lift_apply_mk χ x).symm
      _ = lift χ (mk G y) := congrArg (lift χ) h
      _ = χ y := lift_apply_mk χ y
  · intro h
    by_contra hxy
    obtain ⟨A, _instCommGroupA, _instTopologyA, _instFiniteA, _instDiscreteA,
      χ, hχ⟩ := exists_finite_character_of_mk_ne hxy
    exact hχ (h A χ)

end TopologicalAbelianization

/-- A character changed by conjugation detects a nontrivial automorphism of
the normal subgroup's topological abelianization.  This direction needs only
a T₁ commutative target, so it also applies to finite characters. -/
theorem quotientConjugationTopologicalAbelianizationMap_ne_one_of_character_ne
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {N : Subgroup G} [N.Normal]
    {A : Type v} [CommGroup A] [TopologicalSpace A] [T1Space A]
    (χ : N →ₜ* A) {g : G} {n : N}
    (hχ : χ (MulAut.conjNormal g n) ≠ χ n) :
    quotientConjugationTopologicalAbelianizationMap (G := G) N
      (QuotientGroup.mk' N g) ≠ 1 := by
  intro h
  apply hχ
  have hpoint := congrArg
    (fun a : MulAut (_root_.TopologicalAbelianization N) =>
      a (TopologicalAbelianization.mk N n)) h
  have hclasses :
      TopologicalAbelianization.mk N (MulAut.conjNormal g n) =
        TopologicalAbelianization.mk N n := by
    simpa only [quotientConjugationTopologicalAbelianizationMap_mk_apply_mk,
      MulAut.one_apply] using hpoint
  calc
    χ (MulAut.conjNormal g n) =
        TopologicalAbelianization.lift χ
          (TopologicalAbelianization.mk N (MulAut.conjNormal g n)) :=
      (TopologicalAbelianization.lift_apply_mk χ (MulAut.conjNormal g n)).symm
    _ = TopologicalAbelianization.lift χ (TopologicalAbelianization.mk N n) :=
      congrArg (TopologicalAbelianization.lift χ) hclasses
    _ = χ n := TopologicalAbelianization.lift_apply_mk χ n

/-- If the normal subgroup is profinite, a quotient element acts trivially
on its topological abelianization exactly when it fixes every finite
continuous character.  Profinite hypotheses are needed only on the subgroup. -/
theorem quotientConjugationTopologicalAbelianizationMap_eq_one_iff_finite_characters_fixed
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {N : Subgroup G} [N.Normal]
    [CompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]
    {g : G} :
    quotientConjugationTopologicalAbelianizationMap (G := G) N
        (QuotientGroup.mk' N g) = 1 ↔
      ∀ (A : Type u) [CommGroup A] [TopologicalSpace A]
        [Finite A] [DiscreteTopology A],
        ∀ (χ : N →ₜ* A) (n : N), χ (MulAut.conjNormal g n) = χ n := by
  constructor
  · intro h A _instCommGroupA _instTopologyA _instFiniteA _instDiscreteA χ n
    by_contra hχ
    exact
      quotientConjugationTopologicalAbelianizationMap_ne_one_of_character_ne χ hχ h
  · intro h
    apply MulEquiv.ext
    intro a
    obtain ⟨n, rfl⟩ := TopologicalAbelianization.surjective_mk N a
    rw [quotientConjugationTopologicalAbelianizationMap_mk_apply_mk,
      MulAut.one_apply]
    apply TopologicalAbelianization.mk_eq_iff_finite_characters_eq.mpr
    intro A _instCommGroupA _instTopologyA _instFiniteA _instDiscreteA χ
    exact h A χ n

end ProCGroups.Abelian
