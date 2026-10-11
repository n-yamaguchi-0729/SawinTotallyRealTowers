/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.InverseSystems.FiniteStageFactorization
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.FilteredFamilies
import Nyll.ProCGroups.Profinite.Basic

/-!
# The order structure on closed subgroups

This module equips closed subgroups with basic lattice operations, develops continuous images and
preimages, and relates order-theoretic constructions to finite quotients of profinite groups.
-/

open Set
open scoped Topology Pointwise BigOperators

namespace ProCGroups.Order

universe u v w

open ProCGroups.InverseSystems
open ProCGroups.ProC

namespace ClosedSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {K : Type v} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- Closed subgroups have a top element: the whole group. -/
instance instTopClosedSubgroup : Top (ClosedSubgroup G) :=
  ⟨{ toSubgroup := ⊤, isClosed' := isClosed_univ }⟩

/--
Closed subgroups have a bottom element: the trivial subgroup, closed in a \(T_1\) topological
group.
-/
instance instBotClosedSubgroup [T1Space G] : Bot (ClosedSubgroup G) :=
  ⟨{ toSubgroup := ⊥
     isClosed' := by
       change IsClosed ({(1 : G)} : Set G)
       exact isClosed_singleton }⟩

/--
The image of a closed subgroup under a continuous homomorphism from a compact domain into a
Hausdorff codomain.
-/
noncomputable def map [CompactSpace G] [T2Space K] (H : ClosedSubgroup G)
    (φ : G →* K) (hφ : Continuous φ) : ClosedSubgroup K where
  toSubgroup := (H : Subgroup G).map φ
  isClosed' := by
    let f : H → K := fun x => φ x
    have hcont : Continuous f := hφ.comp continuous_subtype_val
    have hcompact : IsCompact (Set.range f) := isCompact_range hcont
    have hEq : Set.range f = ((H : Subgroup G).map φ : Set K) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact (Subgroup.mem_map).2 ⟨x.1, x.2, rfl⟩
      · intro hy
        rcases (Subgroup.mem_map).1 hy with ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    change IsClosed (((H : Subgroup G).map φ : Subgroup K) : Set K)
    rw [← hEq]
    exact hcompact.isClosed

omit [IsTopologicalGroup K] in
/-- The underlying subgroup of the image closed subgroup is the image of the underlying subgroup. -/
@[simp, norm_cast]
theorem toSubgroup_map [CompactSpace G] [T2Space K] (H : ClosedSubgroup G)
    (φ : G →* K) (hφ : Continuous φ) :
    ((map H φ hφ : ClosedSubgroup K) : Subgroup K) = (H : Subgroup G).map φ :=
  rfl

omit [IsTopologicalGroup K] in
/-- Membership in the image closed subgroup is membership in the subgroup map. -/
theorem mem_map [CompactSpace G] [T2Space K] {H : ClosedSubgroup G}
    {φ : G →* K} (hφ : Continuous φ) {y : K} :
    y ∈ map H φ hφ ↔ ∃ x ∈ (H : Subgroup G), φ x = y := by
  rfl

/-- Mapping a closed subgroup along the identity homomorphism gives the same closed subgroup. -/
@[simp]
theorem map_id [CompactSpace G] [T2Space G] (H : ClosedSubgroup G) :
    map H (MonoidHom.id G) continuous_id = H := by
  apply ClosedSubgroup.toSubgroup_injective
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [IsTopologicalGroup K] in
/-- Images of closed subgroups compose under composition of continuous homomorphisms. -/
theorem map_comp
    {L : Type w} [Group L] [TopologicalSpace L]
    [CompactSpace G] [T2Space K] [CompactSpace K] [T2Space L]
    (H : ClosedSubgroup G) (φ : G →* K) (hφ : Continuous φ)
    (ψ : K →* L) (hψ : Continuous ψ) :
    map (map H φ hφ) ψ hψ = map H (ψ.comp φ) (hψ.comp hφ) := by
  apply ClosedSubgroup.toSubgroup_injective
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases (Subgroup.mem_map).1 hy with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ x, (Subgroup.mem_map).2 ⟨x, hx, rfl⟩, rfl⟩

omit [IsTopologicalGroup K] in
/-- The image construction on closed subgroups is monotone. -/
theorem map_mono [CompactSpace G] [T2Space K] {H H' : ClosedSubgroup G}
    (hHH' : (H : Subgroup G) ≤ (H' : Subgroup G))
    (φ : G →* K) (hφ : Continuous φ) :
    ((map H φ hφ : ClosedSubgroup K) : Subgroup K) ≤
      ((map H' φ hφ : ClosedSubgroup K) : Subgroup K) :=
  Subgroup.map_mono hHH'

omit [IsTopologicalGroup K] in
/-- The image of the bottom closed subgroup is the bottom closed subgroup. -/
@[simp]
theorem map_bot [CompactSpace G] [T1Space G] [T2Space K]
    (φ : G →* K) (hφ : Continuous φ) :
    map (⊥ : ClosedSubgroup G) φ hφ = (⊥ : ClosedSubgroup K) := by
  apply ClosedSubgroup.toSubgroup_injective
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ (⊥ : Subgroup G) at hx
    change φ x ∈ (⊥ : Subgroup K)
    rw [Subgroup.mem_bot] at hx ⊢
    simp [hx]
  · intro hy
    change y ∈ (⊥ : Subgroup K) at hy
    refine ⟨1, by simp only [SetLike.mem_coe, one_mem], ?_⟩
    rw [Subgroup.mem_bot] at hy
    simp [hy]

omit [IsTopologicalGroup K] in
/-- The image of the top closed subgroup under a surjective homomorphism is top. -/
theorem map_eq_top_of_surjective [CompactSpace G] [T2Space K] (H : ClosedSubgroup G)
    (φ : G →* K) (hφ : Continuous φ)
    (hφH : ∀ y : K, ∃ x ∈ (H : Subgroup G), φ x = y) :
    map H φ hφ = (⊤ : ClosedSubgroup K) := by
  apply ClosedSubgroup.toSubgroup_injective
  ext y
  constructor
  · intro _
    trivial
  · intro _
    exact hφH y

omit [IsTopologicalGroup K] in
/-- Image containment for closed subgroups is equivalent to containment in the comap. -/
theorem map_le_iff_le_comap [CompactSpace G] [T2Space K]
    {H : ClosedSubgroup G} {L : ClosedSubgroup K}
    {φ : G →* K} (hφ : Continuous φ) :
    ((map H φ hφ : ClosedSubgroup K) : Subgroup K) ≤ (L : Subgroup K) ↔
      (H : Subgroup G) ≤ Subgroup.comap φ (L : Subgroup K) := by
  constructor
  · intro h x hx
    exact h ((Subgroup.mem_map).2 ⟨x, hx, rfl⟩)
  · intro h y hy
    rcases (Subgroup.mem_map).1 hy with ⟨x, hx, rfl⟩
    exact h hx

end ClosedSubgroup

/-- The surjectivity hypothesis for transition maps in a group-valued inverse system. -/
def IsSurjectiveInverseSystem {I : Type v} [Preorder I]
    (S : ProCGroups.InverseSystems.InverseSystem (I := I)) : Prop :=
  ∀ ⦃i j : I⦄ (hij : i ≤ j), Function.Surjective (S.map hij)

/-- The image of a closed subgroup under a projection from a group-valued inverse limit. -/
noncomputable def inverseLimitProjectionImage
    {I : Type v} [Preorder I]
    (S : ProCGroups.InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [ProCGroups.InverseSystems.IsGroupSystem S]
    [∀ i, TopologicalSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [CompactSpace S.inverseLimit]
    (H : ClosedSubgroup S.inverseLimit) (i : I) : ClosedSubgroup (S.X i) :=
  let πi : S.inverseLimit →* S.X i := {
    toFun := fun x => S.projection i x
    map_one' := rfl
    map_mul' := by
      intro x y
      rfl
  }
  have hπi : Continuous (fun x : S.inverseLimit => S.projection i x) := by
    exact (continuous_apply i).comp continuous_subtype_val
  ClosedSubgroup.map H πi hπi

section FiniteQuotientImages

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The image of a closed subgroup in an open-normal finite quotient. -/
noncomputable def quotientImage [CompactSpace G] (H : ClosedSubgroup G)
    (U : OpenNormalSubgroup G) : ClosedSubgroup (G ⧸ (U : Subgroup G)) :=
  ClosedSubgroup.map H (QuotientGroup.mk' (U : Subgroup G)) continuous_quotient_mk'

/-- The subgroup underlying a quotient image is the image of the closed subgroup in the quotient. -/
@[simp, norm_cast]
theorem toSubgroup_quotientImage [CompactSpace G] (H : ClosedSubgroup G)
    (U : OpenNormalSubgroup G) :
    ((quotientImage (G := G) H U : ClosedSubgroup (G ⧸ (U : Subgroup G))) :
      Subgroup (G ⧸ (U : Subgroup G))) =
        (H : Subgroup G).map (QuotientGroup.mk' (U : Subgroup G)) :=
  rfl

/-- Membership in a quotient image is membership in the image of the underlying closed subgroup. -/
@[simp]
theorem mem_quotientImage [CompactSpace G] {H : ClosedSubgroup G}
    {U : OpenNormalSubgroup G} {y : G ⧸ (U : Subgroup G)} :
    y ∈ quotientImage (G := G) H U ↔
      ∃ x ∈ (H : Subgroup G), QuotientGroup.mk' (U : Subgroup G) x = y := by
  rfl

/--
Membership in a closed subgroup of a profinite group can be checked after all open-normal finite
quotients.
-/
theorem mem_closedSubgroup_iff_forall_quotientImage_mem
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {H : ClosedSubgroup G} {x : G} :
    x ∈ H ↔
      ∀ U : OpenNormalSubgroup G,
        OpenNormalSubgroup.quotientProj U x ∈
          (quotientImage (G := G) H U : Subgroup (G ⧸ (U : Subgroup G))) := by
  constructor
  · intro hx U
    exact (Subgroup.mem_map).2 ⟨x, hx, rfl⟩
  · intro hx
    have hxOpen :
        ∀ N : Subgroup G, IsOpen (N : Set G) ∧ (H : Subgroup G) ≤ N → x ∈ N := by
      intro N hN
      let V : OpenSubgroup G := ⟨N, hN.1⟩
      rcases exists_openNormalSubgroup_mul_subset_openSubgroup (G := G) H V hN.2 with
        ⟨U, hHU⟩
      have hxImg :
          QuotientGroup.mk' (U : Subgroup G) x ∈
            (quotientImage (G := G) H U : Subgroup (G ⧸ (U : Subgroup G))) := by
        have hxU := hx U
        change QuotientGroup.mk' (U : Subgroup G) x ∈
          (quotientImage (G := G) H U : Subgroup (G ⧸ (U : Subgroup G))) at hxU
        exact hxU
      have hxSup : x ∈ (H : Subgroup G) ⊔ (U : Subgroup G) := by
        have hEq :
            (H : Subgroup G) ⊔ (U : Subgroup G) =
              Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                ((quotientImage (G := G) H U :
                  ClosedSubgroup (G ⧸ (U : Subgroup G))) :
                    Subgroup (G ⧸ (U : Subgroup G))) := by
          calc
            (H : Subgroup G) ⊔ (U : Subgroup G) =
                (H : Subgroup G) ⊔ (QuotientGroup.mk' (U : Subgroup G)).ker := by
                  rw [QuotientGroup.ker_mk']
            _ = Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                  (((H : Subgroup G).map (QuotientGroup.mk' (U : Subgroup G))) :
                    Subgroup (G ⧸ (U : Subgroup G))) := by
                  rw [← Subgroup.comap_map_eq]
            _ = Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                  ((quotientImage (G := G) H U :
                    ClosedSubgroup (G ⧸ (U : Subgroup G))) :
                      Subgroup (G ⧸ (U : Subgroup G))) := by
                  rfl
        rw [hEq]
        exact hxImg
      rcases
          (Subgroup.mem_sup_of_normal_right (s := (H : Subgroup G)) (t := (U : Subgroup G))).1
            hxSup with
        ⟨h, hhH, u, huU, hhu⟩
      have hxV : x ∈ (V : Set G) := hHU ⟨h, hhH, u, huU, hhu⟩
      change x ∈ N at hxV
      exact hxV
    have hxInf :
        x ∈ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ (H : Subgroup G) ≤ N} := by
      simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
      intro N hN
      exact hxOpen N hN
    change x ∈ (H : Subgroup G)
    exact (closedSubgroup_eq_sInf_open (G := G) H).symm ▸ hxInf

/--
Inclusion of closed subgroups of a profinite group can be checked on all open-normal finite
quotients.
-/
theorem closedSubgroup_le_iff_forall_quotientImages_le
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {H K : ClosedSubgroup G} :
    (H : Subgroup G) ≤ (K : Subgroup G) ↔
      ∀ U : OpenNormalSubgroup G,
        (quotientImage (G := G) H U : Subgroup (G ⧸ (U : Subgroup G))) ≤
          (quotientImage (G := G) K U : Subgroup (G ⧸ (U : Subgroup G))) := by
  constructor
  · intro hHK U y hy
    rcases (Subgroup.mem_map).1 hy with ⟨x, hx, rfl⟩
    exact (Subgroup.mem_map).2 ⟨x, hHK hx, rfl⟩
  · intro hHK x hx
    exact (mem_closedSubgroup_iff_forall_quotientImage_mem (G := G) (H := K)).2 (by
      intro U
      exact hHK U ((Subgroup.mem_map).2 ⟨x, hx, rfl⟩))

/-- Two closed subgroups are equal if their images agree in every finite quotient. -/
theorem closedSubgroup_eq_of_quotientImages_eq
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {H K : ClosedSubgroup G}
    (hHK : ∀ U : OpenNormalSubgroup G,
      quotientImage (G := G) H U = quotientImage (G := G) K U) :
    H = K := by
  have hle :
      ∀ {A B : ClosedSubgroup G},
        (∀ U : OpenNormalSubgroup G,
          quotientImage (G := G) A U = quotientImage (G := G) B U) →
            (A : Subgroup G) ≤ B := by
    intro A B hAB x hxA
    have hxOpen :
        ∀ N : Subgroup G, IsOpen (N : Set G) ∧ (B : Subgroup G) ≤ N → x ∈ N := by
      intro N hN
      let V : OpenSubgroup G := ⟨N, hN.1⟩
      rcases exists_openNormalSubgroup_mul_subset_openSubgroup (G := G) B V hN.2 with
        ⟨U, hBU⟩
      have hxImgA :
          QuotientGroup.mk' (U : Subgroup G) x ∈ (quotientImage (G := G) A U : Subgroup _) := by
        exact (Subgroup.mem_map).2 ⟨x, hxA, rfl⟩
      have hxImgB :
          QuotientGroup.mk' (U : Subgroup G) x ∈ (quotientImage (G := G) B U : Subgroup _) := by
        rw [← hAB U]
        exact hxImgA
      have hxSup : x ∈ (B : Subgroup G) ⊔ (U : Subgroup G) := by
        have hEq :
            (B : Subgroup G) ⊔ (U : Subgroup G) =
              Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                ((quotientImage (G := G) B U :
                  ClosedSubgroup (G ⧸ (U : Subgroup G))) :
                    Subgroup (G ⧸ (U : Subgroup G))) := by
          calc
            (B : Subgroup G) ⊔ (U : Subgroup G) =
                (B : Subgroup G) ⊔ (QuotientGroup.mk' (U : Subgroup G)).ker := by
                  rw [QuotientGroup.ker_mk']
            _ = Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                  (((B : Subgroup G).map (QuotientGroup.mk' (U : Subgroup G))) :
                    Subgroup (G ⧸ (U : Subgroup G))) := by
                  rw [← Subgroup.comap_map_eq]
            _ = Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                  ((quotientImage (G := G) B U :
                    ClosedSubgroup (G ⧸ (U : Subgroup G))) :
                      Subgroup (G ⧸ (U : Subgroup G))) := by
                  rfl
        rw [hEq]
        exact hxImgB
      rcases
          (Subgroup.mem_sup_of_normal_right (s := (B : Subgroup G)) (t := (U : Subgroup G))).1
            hxSup with
        ⟨b, hbB, u, huU, hbu⟩
      have hxV : x ∈ (V : Set G) := hBU ⟨b, hbB, u, huU, hbu⟩
      change x ∈ N at hxV
      exact hxV
    have hxB :
        x ∈ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ (B : Subgroup G) ≤ N} := by
      simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
      intro N hN
      exact hxOpen N hN
    exact (closedSubgroup_eq_sInf_open (G := G) B).symm ▸ hxB
  exact le_antisymm (hle hHK) (hle (fun U => (hHK U).symm))

end FiniteQuotientImages

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section CompatibleClosedSubgroupFamilies


variable {I : Type v} [Preorder I]
variable (S : ProCGroups.InverseSystems.InverseSystem (I := I))
variable [∀ i, Group (S.X i)] [ProCGroups.InverseSystems.IsGroupSystem S]
variable [∀ i, IsTopologicalGroup (S.X i)]
variable [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]

/-- The transition map of a group-valued inverse system, viewed as a homomorphism. -/
def inverseSystemStageHom {i j : I} (hij : i ≤ j) : S.X j →* S.X i where
  toFun := S.map hij
  map_one' := ProCGroups.InverseSystems.IsGroupSystem.map_one (S := S) hij
  map_mul' := ProCGroups.InverseSystems.IsGroupSystem.map_mul (S := S) hij

omit [∀ i, IsTopologicalGroup (S.X i)] [∀ i, CompactSpace (S.X i)]
  [∀ i, T2Space (S.X i)] in
/-- The stage homomorphism associated to a group-valued inverse system is continuous. -/
theorem inverseSystemStageHom_continuous {i j : I} (hij : i ≤ j) :
    Continuous (inverseSystemStageHom (S := S) hij) := by
  simpa [inverseSystemStageHom] using (S.continuous_map hij :
    Continuous (fun x : S.X j => S.map hij x))

/--
The inverse system obtained by restricting an ambient inverse system to a compatible family of
closed subgroups.
-/
def compatibleClosedSubgroupSystem
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i))) :
    ProCGroups.InverseSystems.InverseSystem (I := I) where
  X := fun i => L i
  topologicalSpace := fun i => inferInstance
  map := fun {i j} hij x =>
    ⟨S.map hij x.1, by
      have hx :
          S.map hij x.1 ∈
            ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
                (inverseSystemStageHom_continuous (S := S) hij) :
                  ClosedSubgroup (S.X i)) : Subgroup (S.X i)) := by
        exact (Subgroup.mem_map).2 ⟨x.1, x.2, rfl⟩
      rw [hcompat hij] at hx
      exact hx⟩
  continuous_map := fun {i j} hij =>
    Continuous.subtype_mk
      ((inverseSystemStageHom_continuous (S := S) hij).comp continuous_subtype_val) (fun x => by
      have hx :
          S.map hij x.1 ∈
            ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
                (inverseSystemStageHom_continuous (S := S) hij) :
                  ClosedSubgroup (S.X i)) : Subgroup (S.X i)) := by
        exact (Subgroup.mem_map).2 ⟨x.1, x.2, rfl⟩
      rw [hcompat hij] at hx
      exact hx)
  map_id := fun i => by
    funext x
    apply Subtype.ext
    simp only [InverseSystem.map_id_apply, id_eq]
  map_comp := fun {i j k} hij hjk => by
    funext x
    apply Subtype.ext
    simp only [Function.comp_apply, InverseSystem.map_comp_apply]

/-- Each stage of a compatible closed-subgroup system is a group. -/
instance compatibleClosedSubgroupSystem_group
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i)))
    (i : I) :
    Group ((compatibleClosedSubgroupSystem (S := S) L hcompat).X i) := by
  dsimp [compatibleClosedSubgroupSystem]
  infer_instance

/-- A compatible closed-subgroup system is a group-valued inverse system. -/
instance compatibleClosedSubgroupSystem_isGroupSystem
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i))) :
    ProCGroups.InverseSystems.IsGroupSystem (compatibleClosedSubgroupSystem (S := S) L hcompat)
        where
  map_one := by
    intro i j hij
    apply Subtype.ext
    change S.map hij (1 : S.X j) = 1
    exact ProCGroups.InverseSystems.IsGroupSystem.map_one (S := S) hij
  map_mul := by
    intro i j hij x y
    apply Subtype.ext
    change S.map hij (x.1 * y.1) = S.map hij x.1 * S.map hij y.1
    exact ProCGroups.InverseSystems.IsGroupSystem.map_mul (S := S) hij x.1 y.1
  map_inv := by
    intro i j hij x
    apply Subtype.ext
    change S.map hij x.1⁻¹ = (S.map hij x.1)⁻¹
    exact ProCGroups.InverseSystems.IsGroupSystem.map_inv (S := S) hij x.1

/--
The canonical coordinatewise inclusion of a compatible subgroup system into the ambient system.
-/
def compatibleClosedSubgroupInclusion
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i))) :
    (compatibleClosedSubgroupSystem (S := S) L hcompat).Morphism S where
  map := fun i => Subtype.val
  continuous_map := fun i => by
    dsimp [compatibleClosedSubgroupSystem]
    exact continuous_subtype_val
  comm := fun {i j} hij => by
    funext x
    rfl

/--
The induced homomorphism from the inverse limit of a compatible subgroup family into the ambient
inverse limit.
-/
noncomputable def compatibleClosedSubgroupLimHom
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i))) :
    (compatibleClosedSubgroupSystem (S := S) L hcompat).inverseLimit →* S.inverseLimit where
  toFun :=
    (compatibleClosedSubgroupSystem (S := S) L hcompat).limMap
      (compatibleClosedSubgroupInclusion (S := S) L hcompat)
  map_one' := by
    apply S.ext
    intro i
    rfl
  map_mul' := by
    intro x y
    apply S.ext
    intro i
    rfl

/--
Closed subgroup of the ambient inverse limit obtained from a compatible family of closed
subgroups with surjective transition maps.
-/
noncomputable def closedSubgroupFromCompatibleFamily
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i))) :
    ClosedSubgroup S.inverseLimit where
  toSubgroup := (compatibleClosedSubgroupLimHom (S := S) L hcompat).range
  isClosed' := by
    let T : InverseSystem (I := I) := compatibleClosedSubgroupSystem (S := S) L hcompat
    let : ∀ i, CompactSpace (T.X i) := fun i =>
      (inferInstance : CompactSpace (L i))
    let : ∀ i, T2Space (T.X i) := fun i =>
      (inferInstance : T2Space (L i))
    let φ : T.inverseLimit →* S.inverseLimit :=
      compatibleClosedSubgroupLimHom (S := S) L hcompat
    have hφcont :
        Continuous (φ : T.inverseLimit → S.inverseLimit) := by
      change Continuous (T.limMap (compatibleClosedSubgroupInclusion (S := S) L hcompat))
      exact T.continuous_limMap (compatibleClosedSubgroupInclusion (S := S) L hcompat)
    change IsClosed (Set.range (φ : T.inverseLimit → S.inverseLimit))
    exact (isCompact_range hφcont).isClosed

omit [∀ i, IsTopologicalGroup (S.X i)] in
/--
Projection images of a closed subgroup recovered from a compatible family match the given
family.
-/
theorem inverseLimitProjectionImage_closedSubgroupFromCompatibleFamily
    [CompactSpace S.inverseLimit]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i))) (i : I) :
    inverseLimitProjectionImage S (closedSubgroupFromCompatibleFamily (S := S) L hcompat) i =
      L i := by
  let T : InverseSystem (I := I) := compatibleClosedSubgroupSystem (S := S) L hcompat
  let incl : T.Morphism S := compatibleClosedSubgroupInclusion (S := S) L hcompat
  let φ : T.inverseLimit →* S.inverseLimit :=
    compatibleClosedSubgroupLimHom (S := S) L hcompat
  have hTsurj : ∀ {i j : I} (hij : i ≤ j), Function.Surjective (T.map hij) := by
    intro i j hij y
    have hy :
        y.1 ∈
        ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
            (inverseSystemStageHom_continuous (S := S) hij) :
            ClosedSubgroup (S.X i)) : Subgroup (S.X i)) := by
      exact (hcompat hij).symm ▸ (show y.1 ∈ (L i : Subgroup (S.X i)) from y.2)
    rcases (Subgroup.mem_map).1 hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    change S.map hij x = y.1
    change S.map hij x = y.1 at hxy
    exact hxy
  let : ∀ i, CompactSpace (T.X i) := fun i =>
    (inferInstance : CompactSpace (L i))
  let : ∀ i, T2Space (T.X i) := fun i =>
    (inferInstance : T2Space (L i))
  ext y
  constructor
  · intro hy
    rcases (Subgroup.mem_map).1 hy with ⟨x, hx, hxy⟩
    rcases hx with ⟨z, rfl⟩
    have hcoord :
        S.projection i ((φ : T.inverseLimit →* S.inverseLimit) z) = (T.projection i z).1 := by
      rfl
    have hmem : (T.projection i z).1 ∈ (L i : Subgroup (S.X i)) := by
      exact (T.projection i z).2
    have hmem' : S.projection i ((φ : T.inverseLimit →* S.inverseLimit) z) ∈ (L i : Subgroup
        (S.X i)) := by
      exact hcoord ▸ hmem
    exact hxy ▸ hmem'
  · intro hy
    have hπsurj : Function.Surjective (T.projection i) := T.surjective_π hdir hTsurj i
    rcases hπsurj ⟨y, hy⟩ with ⟨z, hz⟩
    refine (Subgroup.mem_map).2 ?_
    refine ⟨φ z, ⟨z, rfl⟩, ?_⟩
    have hcoord :
        S.projection i ((φ : T.inverseLimit →* S.inverseLimit) z) = y := by
      calc
        S.projection i ((φ : T.inverseLimit →* S.inverseLimit) z) =
            (T.projection i z).1 := by rfl
        _ = y := congrArg Subtype.val hz
    exact hcoord

omit [∀ i, IsTopologicalGroup (S.X i)] in
/--
Projection images commute with mapping a closed subgroup along a compatible inverse-limit
morphism.
-/
theorem map_inverseLimitProjectionImage
    [CompactSpace S.inverseLimit]
    (H : ClosedSubgroup S.inverseLimit) {i j : I} (hij : i ≤ j) :
    ((ClosedSubgroup.map (inverseLimitProjectionImage S H j) (inverseSystemStageHom (S := S) hij)
        (inverseSystemStageHom_continuous (S := S) hij) :
        ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
      (inverseLimitProjectionImage S H i : Subgroup (S.X i)) := by
  ext x
  constructor
  · intro hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hxy⟩
    rcases (Subgroup.mem_map).1 hy with ⟨z, hz, hzy⟩
    refine (Subgroup.mem_map).2 ⟨z, hz, ?_⟩
    calc
      S.projection i z = S.map hij (S.projection j z) := by
        symm
        simpa using z.2 i j hij
      _ = S.map hij y := by simpa using congrArg (S.map hij) hzy
      _ = x := hxy
  · intro hx
    rcases (Subgroup.mem_map).1 hx with ⟨z, hz, hzx⟩
    refine (Subgroup.mem_map).2 ⟨S.projection j z, ?_, ?_⟩
    · exact (Subgroup.mem_map).2 ⟨z, hz, rfl⟩
    · calc
        S.map hij (S.projection j z) = S.projection i z := by
          simpa using z.2 i j hij
        _ = x := hzx

omit [∀ i, IsTopologicalGroup (S.X i)] in
/--
The stage-transition compatibility of projection images, repackaged as an equality of closed
subgroups.
-/
theorem map_inverseLimitProjectionImage_closed
    [CompactSpace S.inverseLimit]
    (H : ClosedSubgroup S.inverseLimit) {i j : I} (hij : i ≤ j) :
    ClosedSubgroup.map (inverseLimitProjectionImage S H j)
        (inverseSystemStageHom (S := S) hij)
        (inverseSystemStageHom_continuous (S := S) hij) =
      inverseLimitProjectionImage S H i := by
  ext x
  simpa using congrArg (fun K : Subgroup (S.X i) => x ∈ K)
    (map_inverseLimitProjectionImage (S := S) H hij)

omit [∀ i, IsTopologicalGroup (S.X i)] [∀ i, CompactSpace (S.X i)] in
/-- The projection image of the trivial closed subgroup is trivial. -/
theorem inverseLimitProjectionImage_bot
    [CompactSpace S.inverseLimit] (i : I) :
    inverseLimitProjectionImage S (⊥ : ClosedSubgroup S.inverseLimit) i = ⊥ := by
  ext x
  constructor
  · intro hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hyx⟩
    change y ∈ (⊥ : Subgroup S.inverseLimit) at hy
    have hy1 : y = 1 := (Subgroup.mem_bot).1 hy
    cases hy1
    change x ∈ (⊥ : Subgroup (S.X i))
    rw [Subgroup.mem_bot]
    calc
      x = S.projection i (1 : S.inverseLimit) := hyx.symm
      _ = 1 := projection_one (S := S) i
  · intro hx
    change x ∈ (⊥ : Subgroup (S.X i)) at hx
    have hx1 : x = 1 := (Subgroup.mem_bot).1 hx
    refine (Subgroup.mem_map).2 ⟨1, by simp only [one_mem], ?_⟩
    rw [hx1]
    rfl

omit [∀ i, IsTopologicalGroup (S.X i)] in
/--
Under surjective transition maps, the projection image of the whole inverse limit is the whole
stage group.
-/
theorem inverseLimitProjectionImage_top
    [CompactSpace S.inverseLimit]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (hsurj : IsSurjectiveInverseSystem S) (i : I) :
    inverseLimitProjectionImage S (⊤ : ClosedSubgroup S.inverseLimit) i = ⊤ := by
  ext x
  constructor
  · intro _
    change x ∈ (⊤ : Subgroup (S.X i))
    simp only [Subgroup.mem_top]
  · intro _
    have hπsurj : Function.Surjective (S.projection i) :=
      S.surjective_π hdir (fun {i j} hij => hsurj hij) i
    rcases hπsurj x with ⟨y, hy⟩
    refine (Subgroup.mem_map).2 ⟨y, ?_, hy⟩
    change y ∈ (⊤ : Subgroup S.inverseLimit)
    simp only [Subgroup.mem_top]

omit [∀ i, IsTopologicalGroup (S.X i)] [∀ i, CompactSpace (S.X i)] in
/-- Projection images are monotone in the closed subgroup argument. -/
theorem inverseLimitProjectionImage_mono
    [CompactSpace S.inverseLimit]
    {H K : ClosedSubgroup S.inverseLimit}
    (hHK : (H : Subgroup S.inverseLimit) ≤ K) (i : I) :
    (inverseLimitProjectionImage S H i : Subgroup (S.X i)) ≤
      (inverseLimitProjectionImage S K i : Subgroup (S.X i)) := by
  intro x hx
  rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
  exact (Subgroup.mem_map).2 ⟨y, hHK hy, rfl⟩

/-- Closed subgroups of an inverse limit are determined by their stagewise projection images. -/
theorem closedSubgroup_le_of_projectionImages_le
    [Nonempty I] [CompactSpace S.inverseLimit]
    [TotallyDisconnectedSpace S.inverseLimit] [IsTopologicalGroup S.inverseLimit]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (H K : ClosedSubgroup S.inverseLimit)
    (hproj : ∀ i,
      (inverseLimitProjectionImage S H i : Subgroup (S.X i)) ≤
        (inverseLimitProjectionImage S K i : Subgroup (S.X i))) :
    (H : Subgroup S.inverseLimit) ≤ (K : Subgroup S.inverseLimit) := by
  intro x hx
  have hx' :
      x ∈ sInf {N : Subgroup S.inverseLimit |
        IsOpen (N : Set S.inverseLimit) ∧ (K : Subgroup S.inverseLimit) ≤ N} := by
    simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
    intro N hN
    let V : OpenSubgroup S.inverseLimit := ⟨N, hN.1⟩
    rcases exists_openNormalSubgroup_mul_subset_openSubgroup (G := S.inverseLimit) K V hN.2 with
      ⟨U, hKU⟩
    let β : S.inverseLimit →* S.inverseLimit ⧸ (U : Subgroup S.inverseLimit) :=
      QuotientGroup.mk' (U : Subgroup S.inverseLimit)
    rcases ProCGroups.InverseSystems.InverseSystem.factors_through_projection_finite_group_hom
        (S := S) hdir β continuous_quotient_mk' with ⟨k, βk, hβkcont, hβfac⟩
    have hxk : S.projection k x ∈ (inverseLimitProjectionImage S H k : Subgroup (S.X k)) := by
      exact (Subgroup.mem_map).2 ⟨x, hx, rfl⟩
    have hxkK : S.projection k x ∈ (inverseLimitProjectionImage S K k : Subgroup (S.X k)) :=
        hproj k hxk
    rcases (Subgroup.mem_map).1 hxkK with ⟨z, hzK, hzxk⟩
    have hβz : β z = βk (S.projection k z) := by
      simpa [Function.comp] using
        congrArg (fun f : S.inverseLimit → S.inverseLimit ⧸ (U : Subgroup S.inverseLimit) =>
          f z) hβfac
    have hβx : β x = βk (S.projection k x) := by
      simpa [Function.comp] using
        congrArg (fun f : S.inverseLimit → S.inverseLimit ⧸ (U : Subgroup S.inverseLimit) =>
          f x) hβfac
    have hzxu : z⁻¹ * x ∈ (U : Subgroup S.inverseLimit) := by
      apply (QuotientGroup.eq_one_iff (N := (U : Subgroup S.inverseLimit)) (z⁻¹ * x)).1
      have hβeq : β z = β x := by
        calc
          β z = βk (S.projection k z) := hβz
          _ = βk (S.projection k x) := by simpa using congrArg βk hzxk
          _ = β x := hβx.symm
      calc
        β (z⁻¹ * x) = (β z)⁻¹ * β x := by simp only [QuotientGroup.mk'_apply,
            QuotientGroup.mk_mul, QuotientGroup.mk_inv, β]
        _ = 1 := by simp only [hβeq, inv_mul_cancel]
    have hxKU : x ∈ (((K : Subgroup S.inverseLimit) : Set S.inverseLimit) *
        (((U : Subgroup S.inverseLimit) : Set S.inverseLimit))) := by
      refine ⟨z, hzK, z⁻¹ * x, hzxu, ?_⟩
      simp only [mul_inv_cancel_left]
    exact hKU hxKU
  exact (closedSubgroup_eq_sInf_open (G := S.inverseLimit) K).symm ▸ hx'

/-- Stagewise equality of projection images determines a closed subgroup of an inverse limit. -/
theorem closedSubgroup_eq_of_projectionImages_eq
    [Nonempty I] [CompactSpace S.inverseLimit]
    [TotallyDisconnectedSpace S.inverseLimit] [IsTopologicalGroup S.inverseLimit]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (H K : ClosedSubgroup S.inverseLimit)
    (hproj : ∀ i, inverseLimitProjectionImage S H i = inverseLimitProjectionImage S K i) :
    H = K := by
  have hHK : (H : Subgroup S.inverseLimit) ≤ (K : Subgroup S.inverseLimit) :=
    closedSubgroup_le_of_projectionImages_le (S := S) hdir H K (fun i => by
      exact
        le_of_eq <|
          congrArg (fun (L : ClosedSubgroup (S.X i)) => (L : Subgroup (S.X i))) (hproj i))
  have hKH : (K : Subgroup S.inverseLimit) ≤ (H : Subgroup S.inverseLimit) :=
    closedSubgroup_le_of_projectionImages_le (S := S) hdir K H (fun i => by
      exact
        le_of_eq <|
          congrArg (fun (L : ClosedSubgroup (S.X i)) => (L : Subgroup (S.X i))) (hproj i).symm)
  apply SetLike.ext'
  exact Set.ext fun x => ⟨fun hx => hHK hx, fun hx => hKH hx⟩

/-- If every stagewise projection image is trivial, then the closed subgroup itself is trivial. -/
theorem closedSubgroup_eq_bot_of_projectionImages_eq_bot
    [Nonempty I] [CompactSpace S.inverseLimit]
    [TotallyDisconnectedSpace S.inverseLimit] [IsTopologicalGroup S.inverseLimit]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (H : ClosedSubgroup S.inverseLimit)
    (hproj : ∀ i, inverseLimitProjectionImage S H i = ⊥) :
    H = ⊥ := by
  apply closedSubgroup_eq_of_projectionImages_eq (S := S) hdir H ⊥
  intro i
  rw [hproj i, inverseLimitProjectionImage_bot (S := S) (i := i)]

/--
If every stagewise projection image is the whole stage group, then the closed subgroup itself is
the whole inverse limit.
-/
theorem closedSubgroup_eq_top_of_projectionImages_eq_top
    [Nonempty I] [CompactSpace S.inverseLimit]
    [TotallyDisconnectedSpace S.inverseLimit] [IsTopologicalGroup S.inverseLimit]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (hsurj : IsSurjectiveInverseSystem S)
    (H : ClosedSubgroup S.inverseLimit)
    (hproj : ∀ i, inverseLimitProjectionImage S H i = ⊤) :
    H = ⊤ := by
  apply closedSubgroup_eq_of_projectionImages_eq (S := S) hdir H ⊤
  intro i
  rw [hproj i, inverseLimitProjectionImage_top (S := S) hdir hsurj i]


end CompatibleClosedSubgroupFamilies

end ProCGroups.Order
