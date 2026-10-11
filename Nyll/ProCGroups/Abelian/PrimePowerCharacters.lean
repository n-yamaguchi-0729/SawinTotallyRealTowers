/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Topology.Instances.ZMod

/-! # Prime-power characters separate abelian pro-p groups -/

namespace ProCGroups.Abelian

universe u

/-- A nonidentity element of a finite abelian p-group is detected by a character
to a cyclic p-power group. -/
theorem exists_primePower_character_finite
    {p : ℕ} [Fact p.Prime]
    {A : Type u} [CommGroup A] [Finite A]
    (hA : IsPGroup p A) {x : A} (hx : x ≠ 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ χ : A →* Multiplicative (ZMod (p ^ n)), χ x ≠ 1 := by
  classical
  obtain ⟨ι, instι, m, hm, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  have hcoord : ∃ i : ι, e x i ≠ 1 := by
    by_contra! h
    apply hx
    apply e.injective
    rw [map_one]
    exact funext h
  obtain ⟨i, hi⟩ := hcoord
  let ψ : A →* Multiplicative (ZMod (m i)) :=
    (Pi.evalMonoidHom (fun j : ι => Multiplicative (ZMod (m j))) i).comp e.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro a
    refine ⟨e.symm (Function.update 1 i a), ?_⟩
    change e (e.symm (Function.update 1 i a)) i = a
    rw [e.apply_symm_apply, Function.update_self]
  have hP := hA.of_surjective ψ hψ
  have : NeZero (m i) := ⟨ne_of_gt (lt_trans Nat.zero_lt_one (hm i))⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hmn : m i = p ^ n := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] using hn
  have hnpos : 0 < n := by
    by_contra hn0
    have hzero : n = 0 := Nat.eq_zero_of_not_pos hn0
    rw [hzero, pow_zero] at hmn
    exact (Nat.ne_of_gt (hm i)) hmn
  let ec := (ZMod.ringEquivCongr hmn).toAddEquiv.toMultiplicative
  refine ⟨n, hnpos, ec.toMonoidHom.comp ψ, ?_⟩
  intro hχ
  apply hi
  apply ec.injective
  exact hχ.trans (map_one ec).symm

/-- Continuous cyclic p-power characters separate a Hausdorff abelian pro-p group. -/
theorem exists_primePower_character_proP
    {p : ℕ} [Fact p.Prime]
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A]
    (hA : ProC.HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) A)
    {x : A} (hx : x ≠ 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ χ : A →ₜ* Multiplicative (ZMod (p ^ n)), χ x ≠ 1 := by
  obtain ⟨U, hU⟩ := hA.exists_openNormalSubgroupInClass_not_mem hx
  have : Finite (A ⧸ (U.1 : Subgroup A)) := U.2.1
  have hq : QuotientGroup.mk' (U.1 : Subgroup A) x ≠ 1 := by
    intro heq
    exact hU ((QuotientGroup.eq_one_iff (N := (U.1 : Subgroup A)) x).mp heq)
  obtain ⟨n, hn, χ, hχ⟩ := exists_primePower_character_finite U.2.2 hq
  let χcont : (A ⧸ (U.1 : Subgroup A)) →ₜ* Multiplicative (ZMod (p ^ n)) :=
    ⟨χ, continuous_of_discreteTopology⟩
  refine ⟨n, hn, χcont.comp (ProC.OpenNormalSubgroup.quotientProj U.1), ?_⟩
  exact hχ

end ProCGroups.Abelian
