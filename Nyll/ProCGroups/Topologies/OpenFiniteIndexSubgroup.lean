/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Open finite-index subgroups and transport

The carrier is the subtype of Mathlib open subgroups with finite index.
Transport along a topological group equivalence preserves the underlying
subgroup and its ordinary inclusion order.
-/

@[expose] public section

universe u v

/-- Open subgroups with finite index, ordered by subgroup inclusion. -/
abbrev OpenFiniteIndexGroupSubgroup
    (G : Type u) [Group G] [TopologicalSpace G] :=
  { H : OpenSubgroup G // H.toSubgroup.FiniteIndex }

namespace OpenFiniteIndexGroupSubgroup

variable {G : Type u} {G' : Type v}
  [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

/-- Open finite-index subgroups are determined by their underlying subgroups. -/
@[ext]
theorem ext {H J : OpenFiniteIndexGroupSubgroup G}
    (h : H.1.toSubgroup = J.1.toSubgroup) : H = J := by
  apply Subtype.ext
  apply SetLike.coe_injective
  exact congrArg (fun S : Subgroup G => (S : Set G)) h

/-- A topological group equivalence transports open finite-index subgroups. -/
noncomputable def map (e : G ≃ₜ* G') :
    OpenFiniteIndexGroupSubgroup G ≃o OpenFiniteIndexGroupSubgroup G' where
  toEquiv := {
    toFun := fun H => ⟨{
      toSubgroup := H.1.toSubgroup.map e.toMulEquiv.toMonoidHom
      isOpen' := by
        change IsOpen (e '' (H.1 : Set G))
        exact e.toHomeomorph.isOpenMap _ H.1.isOpen
    }, by
      let : H.1.toSubgroup.FiniteIndex := H.2
      exact Subgroup.FiniteIndex.map_of_surjective H.1.toSubgroup e.surjective⟩
    invFun := fun H => ⟨{
      toSubgroup := H.1.toSubgroup.map e.symm.toMulEquiv.toMonoidHom
      isOpen' := by
        change IsOpen (e.symm '' (H.1 : Set G'))
        exact e.symm.toHomeomorph.isOpenMap _ H.1.isOpen
    }, by
      let : H.1.toSubgroup.FiniteIndex := H.2
      exact Subgroup.FiniteIndex.map_of_surjective H.1.toSubgroup e.symm.surjective⟩
    left_inv := by
      intro H
      apply ext
      exact (e.toMulEquiv.mapSubgroup).symm_apply_apply H.1.toSubgroup
    right_inv := by
      intro H
      apply ext
      exact (e.toMulEquiv.mapSubgroup).apply_symm_apply H.1.toSubgroup
  }
  map_rel_iff' := by
    intro H J
    change e '' (H.1 : Set G) ⊆ e '' (J.1 : Set G) ↔
      (H.1 : Set G) ⊆ J.1
    exact Set.image_subset_image_iff e.injective

/-- Transport uses the usual subgroup image of the same multiplicative map. -/
@[simp]
theorem map_toSubgroup (e : G ≃ₜ* G') (H : OpenFiniteIndexGroupSubgroup G) :
    (map e H).1.toSubgroup = H.1.toSubgroup.map e.toMulEquiv.toMonoidHom :=
  rfl

end OpenFiniteIndexGroupSubgroup
