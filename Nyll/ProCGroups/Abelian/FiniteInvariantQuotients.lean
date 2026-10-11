/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import Mathlib.Topology.Constructions

/-!
# Finite invariant quotients

A finite group of continuous automorphisms admits arbitrarily small invariant
open normal subgroups. The construction is the kernel of the product of the
translated finite quotient maps; in particular, invariance is proved from the
given action rather than supplied as additional data.
-/

open scoped Topology

namespace ProCGroups.Abelian

universe u v

variable {C : Type u} [Group C] [Finite C]
variable {A : Type v} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]

/-- The intersection of all translates of an open normal subgroup under a
finite continuous action, constructed as a continuous kernel. -/
def invariantOpenNormalCore
    (ρ : C →* MulAut A) (hρ : ∀ c : C, Continuous (ρ c))
    (U : OpenNormalSubgroup A) : OpenNormalSubgroup A :=
  ProC.OpenNormalSubgroup.ker
    { toMonoidHom :=
        { toFun := fun x c => ProC.OpenNormalSubgroup.quotientProj U (ρ c x)
          map_one' := by
            funext c
            change ProC.OpenNormalSubgroup.quotientProj U (ρ c 1) = 1
            simp only [map_one]
          map_mul' := by
            intro x y
            funext c
            change ProC.OpenNormalSubgroup.quotientProj U (ρ c (x * y)) =
              ProC.OpenNormalSubgroup.quotientProj U (ρ c x) *
                ProC.OpenNormalSubgroup.quotientProj U (ρ c y)
            simp only [map_mul] }
      continuous_toFun := continuous_pi fun c =>
        (ProC.OpenNormalSubgroup.quotientProj U).continuous_toFun.comp (hρ c) }

/-- Membership in the invariant core is membership of every translate in the
original open normal subgroup. -/
theorem mem_invariantOpenNormalCore_iff
    (ρ : C →* MulAut A) (hρ : ∀ c : C, Continuous (ρ c))
    (U : OpenNormalSubgroup A) (x : A) :
    x ∈ invariantOpenNormalCore ρ hρ U ↔ ∀ c : C, ρ c x ∈ U := by
  change (fun c : C => ProC.OpenNormalSubgroup.quotientProj U (ρ c x)) =
      (1 : C → A ⧸ (U : Subgroup A)) ↔ ∀ c : C, ρ c x ∈ U
  constructor
  · intro hx c
    exact ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mp (congrFun hx c)
  · intro hx
    funext c
    exact ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mpr (hx c)

/-- The invariant core refines the original subgroup. -/
theorem invariantOpenNormalCore_le
    (ρ : C →* MulAut A) (hρ : ∀ c : C, Continuous (ρ c))
    (U : OpenNormalSubgroup A) :
    (invariantOpenNormalCore ρ hρ U : Subgroup A) ≤ (U : Subgroup A) := by
  intro x hx
  have h := (mem_invariantOpenNormalCore_iff ρ hρ U x).mp hx 1
  change x ∈ U
  simpa only [map_one, MulAut.one_apply] using h

/-- Every element of the acting group preserves the invariant core. -/
theorem action_mem_invariantOpenNormalCore
    (ρ : C →* MulAut A) (hρ : ∀ c : C, Continuous (ρ c))
    (U : OpenNormalSubgroup A) (c : C) {x : A}
    (hx : x ∈ invariantOpenNormalCore ρ hρ U) :
    ρ c x ∈ invariantOpenNormalCore ρ hρ U := by
  apply (mem_invariantOpenNormalCore_iff ρ hρ U (ρ c x)).mpr
  intro d
  have h := (mem_invariantOpenNormalCore_iff ρ hρ U x).mp hx (d * c)
  simpa only [map_mul, MulAut.mul_apply] using h

/-- An automorphism in the action maps the invariant core onto itself. -/
theorem map_invariantOpenNormalCore
    (ρ : C →* MulAut A) (hρ : ∀ c : C, Continuous (ρ c))
    (U : OpenNormalSubgroup A) (c : C) :
    (invariantOpenNormalCore ρ hρ U : Subgroup A).map (ρ c).toMonoidHom =
      (invariantOpenNormalCore ρ hρ U : Subgroup A) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact action_mem_invariantOpenNormalCore ρ hρ U c hx
  · intro y hy
    refine ⟨ρ c⁻¹ y, action_mem_invariantOpenNormalCore ρ hρ U c⁻¹ hy, ?_⟩
    change ρ c (ρ c⁻¹ y) = y
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

/-- The action induced on the quotient by the invariant open normal core. -/
def invariantOpenNormalQuotientAction
    (ρ : C →* MulAut A) (hρ : ∀ c : C, Continuous (ρ c))
    (U : OpenNormalSubgroup A) :
    C →* MulAut (A ⧸ (invariantOpenNormalCore ρ hρ U : Subgroup A)) where
  toFun c := QuotientGroup.congr
    (invariantOpenNormalCore ρ hρ U : Subgroup A)
    (invariantOpenNormalCore ρ hρ U : Subgroup A)
    (ρ c) (map_invariantOpenNormalCore ρ hρ U c)
  map_one' := by
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    change QuotientGroup.mk' (invariantOpenNormalCore ρ hρ U : Subgroup A) (ρ 1 x) =
      QuotientGroup.mk' (invariantOpenNormalCore ρ hρ U : Subgroup A) x
    rw [map_one, MulAut.one_apply]
  map_mul' := by
    intro c d
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    change QuotientGroup.mk' (invariantOpenNormalCore ρ hρ U : Subgroup A)
        (ρ (c * d) x) =
      QuotientGroup.mk' (invariantOpenNormalCore ρ hρ U : Subgroup A)
        (ρ c (ρ d x))
    rw [map_mul, MulAut.mul_apply]

/-- The quotient projection is equivariant for the induced finite action. -/
theorem invariantOpenNormalQuotientAction_apply_mk
    (ρ : C →* MulAut A) (hρ : ∀ c : C, Continuous (ρ c))
    (U : OpenNormalSubgroup A) (c : C) (x : A) :
    invariantOpenNormalQuotientAction ρ hρ U c
        (QuotientGroup.mk' (invariantOpenNormalCore ρ hρ U : Subgroup A) x) =
      QuotientGroup.mk' (invariantOpenNormalCore ρ hρ U : Subgroup A) (ρ c x) := by
  exact QuotientGroup.congr_mk'
    (invariantOpenNormalCore ρ hρ U : Subgroup A)
    (invariantOpenNormalCore ρ hρ U : Subgroup A)
    (ρ c) (map_invariantOpenNormalCore ρ hρ U c) x

/-- A nonidentity element of a profinite group can be excluded from an invariant
open normal subgroup for any finite continuous action. -/
theorem exists_invariantOpenNormalCore_not_mem
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (ρ : C →* MulAut A) (hρ : ∀ c : C, Continuous (ρ c))
    {x : A} (hx : x ≠ 1) :
    ∃ U : OpenNormalSubgroup A, x ∉ invariantOpenNormalCore ρ hρ U := by
  have hopen : IsOpen (({x} : Set A)ᶜ) := isClosed_singleton.isOpen_compl
  have hone : (1 : A) ∈ ({x} : Set A)ᶜ := by
    intro heq
    exact hx (Set.mem_singleton_iff.mp heq).symm
  obtain ⟨U, hU⟩ := ProC.exists_openNormalSubgroup_sub_open_nhds_of_one hopen hone
  refine ⟨U, ?_⟩
  intro hcore
  exact hU (invariantOpenNormalCore_le ρ hρ U hcore) (Set.mem_singleton x)

/-- A faithful finite continuous action on a profinite group remains faithful
on a finite quotient by an invariant open normal subgroup. No commutativity
of the original group is required. -/
theorem exists_faithful_invariantOpenNormalQuotientAction
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (ρ : C →* MulAut A) (hρ : ∀ c : C, Continuous (ρ c))
    (hfaithful : Function.Injective ρ) :
    ∃ U : OpenNormalSubgroup A,
      Function.Injective (invariantOpenNormalQuotientAction ρ hρ U) := by
  classical
  have hex : ∀ c : C, ∃ U : OpenNormalSubgroup A, ∃ x : A,
      c ≠ 1 → (ρ c x)⁻¹ * x ∉ U := by
    intro c
    by_cases hc : c = 1
    · exact ⟨⊤, 1, fun hne => False.elim (hne hc)⟩
    · have hmove : ∃ x : A, ρ c x ≠ x := by
        by_contra hnone
        apply hc
        apply hfaithful
        apply MulEquiv.ext
        intro x
        rw [map_one, MulAut.one_apply]
        exact Classical.not_not.mp (fun hx => hnone ⟨x, hx⟩)
      obtain ⟨x, hx⟩ := hmove
      have hdiff : (ρ c x)⁻¹ * x ≠ 1 := by
        intro h
        exact hx (inv_mul_eq_one.mp h)
      obtain ⟨U, hU⟩ := exists_invariantOpenNormalCore_not_mem ρ hρ hdiff
      exact ⟨invariantOpenNormalCore ρ hρ U, x, fun _hc => hU⟩
  choose V x hV using hex
  let f : A →ₜ* (∀ c : C, A ⧸ (V c : Subgroup A)) :=
    { toMonoidHom :=
        { toFun := fun a c => ProC.OpenNormalSubgroup.quotientProj (V c) a
          map_one' := by
            funext c
            exact map_one (ProC.OpenNormalSubgroup.quotientProj (V c))
          map_mul' := by
            intro a b
            funext c
            exact map_mul (ProC.OpenNormalSubgroup.quotientProj (V c)) a b }
      continuous_toFun := continuous_pi fun c =>
        (ProC.OpenNormalSubgroup.quotientProj (V c)).continuous_toFun }
  let U : OpenNormalSubgroup A := ProC.OpenNormalSubgroup.ker f
  have hUV : ∀ c : C, (U : Subgroup A) ≤ (V c : Subgroup A) := by
    intro c a ha
    have hf : f a = 1 := ha
    exact ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mp (congrFun hf c)
  refine ⟨U, ?_⟩
  apply (injective_iff_map_eq_one (invariantOpenNormalQuotientAction ρ hρ U)).mpr
  intro c hc
  by_contra hne
  have hpoint := congrArg
    (fun e : MulAut (A ⧸ (invariantOpenNormalCore ρ hρ U : Subgroup A)) =>
      e (QuotientGroup.mk' (invariantOpenNormalCore ρ hρ U : Subgroup A) (x c))) hc
  have hclasses :
      QuotientGroup.mk' (invariantOpenNormalCore ρ hρ U : Subgroup A) (ρ c (x c)) =
        QuotientGroup.mk' (invariantOpenNormalCore ρ hρ U : Subgroup A) (x c) := by
    simpa only [invariantOpenNormalQuotientAction_apply_mk, MulAut.one_apply] using hpoint
  have hcore : (ρ c (x c))⁻¹ * x c ∈ invariantOpenNormalCore ρ hρ U :=
    QuotientGroup.eq.mp hclasses
  exact hV c hne (hUV c (invariantOpenNormalCore_le ρ hρ U hcore))

end ProCGroups.Abelian
