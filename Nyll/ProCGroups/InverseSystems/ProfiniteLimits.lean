/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.InverseSystems.CofinalityAndDensity
import Nyll.ProCGroups.Profinite.Basic

/-!
# Projection kernels in profinite inverse limits

For inverse systems of finite discrete groups, the canonical projections are bundled as group
homomorphisms.  Their kernels are open normal subgroups, and under the usual directedness and
surjectivity assumptions these kernels form a fundamental system of neighborhoods of one in
the inverse limit.
-/

open scoped Topology Pointwise

namespace ProCGroups

universe u v

section

variable {G : Type u} [Group G] [TopologicalSpace G]

/--
The projection from a group-valued inverse limit to one component is viewed as a homomorphism.
-/
def inverseLimitProjectionHom {I : Type v} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S] (i : I) :
    S.inverseLimit →* S.X i where
  toFun := S.projection i
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- The kernel of a projection from an inverse limit of discrete groups is open normal. -/
def inverseLimitProjectionKer {I : Type v} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, DiscreteTopology (S.X i)] (i : I) :
    OpenNormalSubgroup S.inverseLimit where
  toOpenSubgroup :=
    { toSubgroup := (inverseLimitProjectionHom S i).ker
      isOpen' := by
        change IsOpen (S.projection i ⁻¹' ({1} : Set (S.X i)))
        exact
          (isOpen_discrete ({1} : Set (S.X i))).preimage
            (S.continuous_projection i) }
  isNormal' := by
    change ((inverseLimitProjectionHom S i).ker).Normal
    infer_instance

/--
Membership in the kernel of an inverse-limit projection is membership in the kernel at that
finite stage.
-/
@[simp] theorem mem_inverseLimitProjectionKer {I : Type v} [Preorder I]
    {S : InverseSystems.InverseSystem (I := I)}
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, DiscreteTopology (S.X i)]
    {i : I} {x : S.inverseLimit} :
    x ∈ inverseLimitProjectionKer S i ↔ S.projection i x = 1 :=
  Iff.rfl

/--
In an inverse limit of discrete groups, every open neighborhood of \(1\) contains the kernel of
one projection map.
-/
theorem exists_inverseLimitProjectionKer_sub_open_nhds_of_one
    {I : Type v} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I)) [Nonempty I]
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, DiscreteTopology (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    {W : Set S.inverseLimit} (hW : IsOpen W) (h1W : (1 : S.inverseLimit) ∈ W) :
    ∃ i : I,
      (((inverseLimitProjectionKer S i : OpenNormalSubgroup S.inverseLimit) :
        Subgroup S.inverseLimit) : Set S.inverseLimit) ⊆ W := by
  rcases S.exists_projection_preimage_subset hdir hW h1W with ⟨i, V, -, h1V, hVW⟩
  refine ⟨i, ?_⟩
  intro x hx
  have hxker : S.projection i x = 1 := (mem_inverseLimitProjectionKer (S := S) (i := i)).1 hx
  have hV1 : (1 : S.X i) ∈ V := h1V
  have hxV : x ∈ S.projection i ⁻¹' V := by
    change S.projection i x ∈ V
    rw [hxker]
    exact hV1
  exact hVW hxV

/--
The projection kernels form a fundamental system of open neighborhoods of 1 in the inverse
limit.
-/
theorem inverseLimitProjectionKer_fundamentalSystemAtOne
    {I : Type v} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I)) [Nonempty I]
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, DiscreteTopology (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    (∀ i : I,
      IsOpen ((((inverseLimitProjectionKer S i : OpenNormalSubgroup S.inverseLimit) :
        Subgroup S.inverseLimit) : Set S.inverseLimit)) ∧
      (1 : S.inverseLimit) ∈ (((inverseLimitProjectionKer S i :
        OpenNormalSubgroup S.inverseLimit) : Subgroup S.inverseLimit) : Set S.inverseLimit)) ∧
    ∀ W : Set S.inverseLimit, IsOpen W → (1 : S.inverseLimit) ∈ W →
      ∃ i : I,
        ((((inverseLimitProjectionKer S i : OpenNormalSubgroup S.inverseLimit) :
          Subgroup S.inverseLimit) : Set S.inverseLimit)) ⊆ W := by
  refine ⟨?_, ?_⟩
  · intro i
    refine ⟨openNormalSubgroup_isOpen (G := S.inverseLimit) (inverseLimitProjectionKer S i), ?_⟩
    change ((1 : S.inverseLimit).1 i) = 1
    rfl
  · intro W hW h1W
    exact exists_inverseLimitProjectionKer_sub_open_nhds_of_one S hdir hW h1W

end

end ProCGroups
