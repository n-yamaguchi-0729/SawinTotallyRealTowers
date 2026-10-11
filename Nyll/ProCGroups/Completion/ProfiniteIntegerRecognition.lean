/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Completion.ProCInteger
import Nyll.ProCGroups.Generation.Basic
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Recognizing the full profinite integers

A profinite group with a topological generator and open normal quotients of every positive
order is isomorphic to the actual inverse limit of all finite cyclic groups. Normalizing each
coefficient map at the generator proves its uniqueness and hence the compatibility of the
independently chosen finite quotients.
-/

noncomputable section

open scoped Topology

namespace ProCGroups.Completion

open ProCGroups.Generation ProCGroups.ProC

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Normalize an actual finite quotient at a fixed topological generator. The resulting
coefficient map detects exactly equality in that quotient. -/
theorem exists_normalized_cyclic_coefficient [CompactSpace G]
    (g : G) (hg : TopologicallyGenerates ({g} : Set G))
    (U : OpenNormalSubgroup G) {n : ℕ}
    (hn : Nat.card (G ⧸ (U : Subgroup G)) = n) :
    ∃ f : G →ₜ* Multiplicative (ZMod n),
      f g = Multiplicative.ofAdd 1 ∧
      ∀ x y : G, f x = f y ↔
        OpenNormalSubgroup.quotientProj U x = OpenNormalSubgroup.quotientProj U y := by
  let q : G →ₜ* (G ⧸ (U : Subgroup G)) := OpenNormalSubgroup.quotientProj U
  have hgen : ∀ x : G ⧸ (U : Subgroup G), x ∈ Subgroup.zpowers (q g) := by
    intro x
    obtain ⟨a, rfl⟩ := OpenNormalSubgroup.quotientProj_surjective U x
    exact map_mem_zpowers_of_topologicallyGenerates_singleton q hg
  let e : Multiplicative (ZMod n) ≃* (G ⧸ (U : Subgroup G)) :=
    zmodMulEquivOfGenerator hgen hn
  have he : Continuous e.symm := continuous_of_discreteTopology
  let f : G →ₜ* Multiplicative (ZMod n) :=
    { toMonoidHom := e.symm.toMonoidHom.comp q.toMonoidHom
      continuous_toFun := he.comp q.continuous_toFun }
  refine ⟨f, ?_, ?_⟩
  · exact zmodMulEquivOfGenerator_symm_apply_generator hgen hn
  · intro x y
    exact e.symm.injective.eq_iff

/-- A topological generator and actual finite quotients of every positive order identify a
profinite group with the full inverse limit of finite cyclic groups. The isomorphism sends the
specified generator to the compatible residue class of the integer one. -/
theorem exists_profiniteInteger_equiv_of_generator_and_quotient_orders
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (g : G) (hg : TopologicallyGenerates ({g} : Set G))
    (horders : ∀ n : ℕ, 0 < n →
      ∃ U : OpenNormalSubgroup G, Nat.card (G ⧸ (U : Subgroup G)) = n) :
    ∃ e : G ≃ₜ* Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.allFinite : FiniteGroupClass.{0})),
      e g = proCIntegerOne (C := FiniteGroupClass.allFinite) := by
  classical
  have coefficients : ∀ n : ℕ, ∀ hn : 0 < n,
      ∃ f : G →ₜ* Multiplicative (ZMod n), f g = Multiplicative.ofAdd 1 := by
    intro n hn
    obtain ⟨U, hU⟩ := horders n hn
    obtain ⟨f, hfg, _⟩ := exists_normalized_cyclic_coefficient g hg U hU
    exact ⟨f, hfg⟩
  choose f hfg using coefficients
  let C : FiniteGroupClass.{0} := FiniteGroupClass.allFinite
  have compatible : ∀ (i j : ProCIntegerIndex C) (hij : i ≤ j) (x : G),
      proCIntegerTransition (C := C) hij (f j.modulus j.positive x).toAdd =
        (f i.modulus i.positive x).toAdd := by
    intro i j hij
    let t : Multiplicative (ZMod j.modulus) →ₜ* Multiplicative (ZMod i.modulus) :=
      { toMonoidHom :=
          (proCIntegerTransition (C := C) hij).toAddMonoidHom.toMultiplicative
        continuous_toFun := continuous_of_discreteTopology }
    have h : t.comp (f j.modulus j.positive) = f i.modulus i.positive := by
      apply continuousMonoidHom_ext_of_topologicallyGenerates hg
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      change t (f j.modulus j.positive g) = f i.modulus i.positive g
      rw [hfg, hfg]
      apply Multiplicative.ext
      exact map_one (proCIntegerTransition (C := C) hij)
    intro x
    exact congrArg Multiplicative.toAdd (DFunLike.congr_fun h x)
  let φ : G →ₜ* Multiplicative (ProCIntegerLimitCarrier C) :=
    { toFun := fun x => Multiplicative.ofAdd
        ⟨fun i => (f i.modulus i.positive x).toAdd, fun i j hij => compatible i j hij x⟩
      map_one' := by
        apply Multiplicative.ext
        apply ProCIntegerLimitCarrier.ext
        intro i
        change (f i.modulus i.positive 1).toAdd = 0
        rw [map_one]
        rfl
      map_mul' := by
        intro x y
        apply Multiplicative.ext
        apply ProCIntegerLimitCarrier.ext
        intro i
        change (f i.modulus i.positive (x * y)).toAdd =
          (f i.modulus i.positive x).toAdd + (f i.modulus i.positive y).toAdd
        rw [map_mul]
        rfl
      continuous_toFun := continuous_ofAdd.comp
        ((continuous_pi fun i =>
          continuous_toAdd.comp (f i.modulus i.positive).continuous).subtype_mk _) }
  have hφg : φ g = proCIntegerOne (C := C) := by
    apply Multiplicative.ext
    apply ProCIntegerLimitCarrier.ext
    intro i
    change (f i.modulus i.positive g).toAdd = 1
    rw [hfg]
    rfl
  have injective : Function.Injective φ := by
    intro x y hxy
    apply OpenNormalSubgroup.eq_of_forall_quotientProj_eq
    intro U
    let m : ℕ := Nat.card (G ⧸ (U : Subgroup G))
    have hm : 0 < m := Nat.card_pos
    obtain ⟨a, hag, ha⟩ := exists_normalized_cyclic_coefficient g hg U (n := m) rfl
    have haf : a = f m hm := by
      apply continuousMonoidHom_ext_of_topologicallyGenerates hg
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact hag.trans (hfg m hm).symm
    apply (ha x y).mp
    rw [haf]
    let i : ProCIntegerIndex C := ProCIntegerIndex.ofAllFiniteModulus m hm
    have hi := congrArg (fun z : Multiplicative (ProCIntegerLimitCarrier C) =>
      proCIntegerProj (C := C) i z.toAdd) hxy
    apply Multiplicative.ext
    exact hi
  have surjective : Function.Surjective φ := by
    have closedRange : IsClosed (Set.range φ) := by
      have h := (isCompact_univ.image φ.continuous).isClosed
      rw [Set.image_univ] at h
      exact h
    have integerRange : Set.range (multiplicativeIntToProCInteger (C := C)) ⊆
        Set.range φ := by
      rintro z ⟨n, rfl⟩
      refine ⟨g ^ n.toAdd, ?_⟩
      rw [map_zpow, hφg]
      exact (multiplicativeIntToProCInteger_zpow_one (C := C) n.toAdd).symm
    intro z
    apply closure_minimal integerRange closedRange
    exact denseRange_multiplicativeIntToProCInteger_allFinite z
  let e : G ≃ₜ* Multiplicative (ProCIntegerLimitCarrier C) :=
    ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
      φ.toMonoidHom φ.continuous ⟨injective, surjective⟩
  refine ⟨e, ?_⟩
  exact (ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2_apply
    φ.toMonoidHom φ.continuous ⟨injective, surjective⟩ g).trans hφg

end ProCGroups.Completion
