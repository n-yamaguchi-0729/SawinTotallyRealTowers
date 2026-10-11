/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Book.ValueGroup
import Mathlib.GroupTheory.Archimedean
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.Int.Basic

/-!
# Coprime indices in a discrete book value group

The value group of a nontrivial discrete book exponential valuation is an
infinite cyclic additive group.  In an infinite cyclic group, two subgroups
which generate the whole group have coprime indices.  This file records that
group-theoretic fact and specializes it to actual book value subgroups.
-/

noncomputable section

universe u

namespace TameAbhyankar

open AlgebraicNumberTheory.Valuations

/-- Two subgroups of `ℤ` which generate `ℤ` have coprime indices. -/
theorem int_addSubgroup_index_coprime_of_sup_eq_top
    (A B : AddSubgroup ℤ) (hsup : A ⊔ B = ⊤) :
    Nat.Coprime A.index B.index := by
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic A
  obtain ⟨b, hb⟩ := Int.subgroup_cyclic B
  have ha' : A = AddSubgroup.zmultiples a :=
    ha.trans (AddSubgroup.zmultiples_eq_closure a).symm
  have hb' : B = AddSubgroup.zmultiples b :=
    hb.trans (AddSubgroup.zmultiples_eq_closure b).symm
  rw [ha', hb'] at hsup ⊢
  rw [Int.index_zmultiples, Int.index_zmultiples,
    ← Int.isCoprime_iff_nat_coprime]
  have hone : (1 : ℤ) ∈
      AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b := by
    rw [hsup]
    exact AddSubgroup.mem_top 1
  rcases AddSubgroup.mem_sup.mp hone with ⟨x, hx, y, hy, hxy⟩
  rcases AddSubgroup.mem_zmultiples_iff.mp hx with ⟨m, rfl⟩
  rcases AddSubgroup.mem_zmultiples_iff.mp hy with ⟨n, rfl⟩
  refine ⟨m, n, ?_⟩
  simpa [zsmul_eq_mul, mul_comm] using hxy

/-- Coprimality of subgroup indices is invariant under identifying the
ambient additive group with `ℤ`. -/
theorem addSubgroup_index_coprime_of_addEquiv_int
    {G : Type u} [AddCommGroup G] (e : G ≃+ ℤ)
    (A B : AddSubgroup G) (hsup : A ⊔ B = ⊤) :
    Nat.Coprime A.index B.index := by
  let A' : AddSubgroup ℤ := A.map e.toAddMonoidHom
  let B' : AddSubgroup ℤ := B.map e.toAddMonoidHom
  have hsup' : A' ⊔ B' = ⊤ := by
    have hmap := congrArg
      (fun H : AddSubgroup G => H.map e.toAddMonoidHom) hsup
    simpa [A', B', AddSubgroup.map_sup] using hmap
  have hcop := int_addSubgroup_index_coprime_of_sup_eq_top A' B' hsup'
  simpa [A', B'] using hcop

/-- The subgroups of a discrete book value group which generate the whole
value group have coprime indices. -/
theorem bookValueSubgroup_index_coprime_of_sup_eq_top
    {Top : Type u} [Field Top]
    (w : LubinTate.Valuations.ExponentialValuation Top)
    (hwdisc : LubinTate.Valuations.DiscreteExponentialValuation w)
    (A B : AddSubgroup (exponentialValueSubgroup w))
    (hsup : A ⊔ B = ⊤) :
    Nat.Coprime A.index B.index := by
  rcases hwdisc with ⟨s, hs, hvalues, pi, hpival⟩
  let Gamma := exponentialValueSubgroup w
  have hpi0 : pi ≠ 0 :=
    LubinTate.Valuations.discretePrimeElement_ne_zero_of_value w hpival
  let g : Gamma := ⟨s, pi, hpi0, hpival⟩
  have hg0 : g ≠ 0 := by
    intro hg
    have hval := congrArg Subtype.val hg
    exact hs.ne' (by simpa [g] using hval)
  let : Nontrivial Gamma := ⟨⟨g, 0, hg0⟩⟩
  let : IsAddCyclic Gamma := by
    refine ⟨g, ?_⟩
    intro x
    rcases x.property with ⟨z, hz0, hzvalue⟩
    rcases hvalues z hz0 with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    apply Subtype.ext
    have hx : (x : ℝ) = (m : ℝ) * s :=
      WithTop.coe_eq_coe.mp (hzvalue.symm.trans hm)
    simpa [g, zsmul_eq_mul] using hx.symm
  obtain ⟨e⟩ :=
    (LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int
      (A := Gamma)).mp (inferInstance : IsAddCyclic Gamma)
  exact addSubgroup_index_coprime_of_addEquiv_int e.toAddEquiv A B hsup

/-- Ambient-subgroup form: if two subgroups of `ℝ` lie in a discrete book
value group and their supremum is that value group, their relative indices
in the value group are coprime. -/
theorem bookValueSubgroup_relIndex_coprime_of_sup_eq
    {Top : Type u} [Field Top]
    (w : LubinTate.Valuations.ExponentialValuation Top)
    (hwdisc : LubinTate.Valuations.DiscreteExponentialValuation w)
    (GammaA GammaB : AddSubgroup ℝ)
    (hsup : GammaA ⊔ GammaB = exponentialValueSubgroup w) :
    Nat.Coprime
      (GammaA.relIndex (exponentialValueSubgroup w))
      (GammaB.relIndex (exponentialValueSubgroup w)) := by
  let Gamma := exponentialValueSubgroup w
  let A : AddSubgroup Gamma := GammaA.comap Gamma.subtype
  let B : AddSubgroup Gamma := GammaB.comap Gamma.subtype
  have hA : GammaA ≤ Gamma := by
    change GammaA ≤ exponentialValueSubgroup w
    rw [← hsup]
    exact le_sup_left
  have hB : GammaB ≤ Gamma := by
    change GammaB ≤ exponentialValueSubgroup w
    rw [← hsup]
    exact le_sup_right
  have hAB : A ⊔ B = ⊤ := by
    apply top_unique
    intro x _hx
    have hx : (x : ℝ) ∈ GammaA ⊔ GammaB := by
      rw [hsup]
      exact x.property
    rcases AddSubgroup.mem_sup.mp hx with ⟨a, ha, b, hb, hab⟩
    let a' : Gamma := ⟨a, hA ha⟩
    let b' : Gamma := ⟨b, hB hb⟩
    apply AddSubgroup.mem_sup.mpr
    refine ⟨a', ?_, b', ?_, ?_⟩
    · exact ha
    · exact hb
    · apply Subtype.ext
      exact hab
  change Nat.Coprime A.index B.index
  exact bookValueSubgroup_index_coprime_of_sup_eq_top w hwdisc A B hAB

/-- Book-valuation form of the cyclic-index calculation.  Exact extensions
whose two value subgroups generate the discrete target value group have
coprime book ramification indices. -/
theorem bookRamificationIndex_coprime_of_valueSubgroup_sup_eq
    {A B Top : Type u} [Field A] [Field B] [Field Top]
    (vA : LubinTate.Valuations.ExponentialValuation A)
    (vB : LubinTate.Valuations.ExponentialValuation B)
    (w : LubinTate.Valuations.ExponentialValuation Top)
    (hwdisc : LubinTate.Valuations.DiscreteExponentialValuation w)
    (hsup : exponentialValueSubgroup vA ⊔
      exponentialValueSubgroup vB = exponentialValueSubgroup w) :
    Nat.Coprime (exponentialRamificationIndex vA w)
      (exponentialRamificationIndex vB w) := by
  rw [bookRamificationIndex_eq_valueSubgroup_relIndex,
    bookRamificationIndex_eq_valueSubgroup_relIndex]
  exact bookValueSubgroup_relIndex_coprime_of_sup_eq w hwdisc
    (exponentialValueSubgroup vA)
    (exponentialValueSubgroup vB) hsup

end TameAbhyankar

end
