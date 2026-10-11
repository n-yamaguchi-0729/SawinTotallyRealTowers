/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.Quotients.ClosedSubgroupNeighborhoods
import Nyll.ProCGroups.Topologies.ContinuousMonoidHom

/-! # Extending discrete characters to an open normal supergroup -/

namespace ProCGroups

open ProC

universe u v

/-- A continuous character on a closed normal subgroup extends to an open
normal supergroup inside any prescribed open normal neighborhood of that
subgroup. The extension is constructed through an actual finite quotient. -/
theorem exists_openNormal_character_extension
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {A : Type v} [Group A] [TopologicalSpace A] [DiscreteTopology A]
    (D : Subgroup G) [D.Normal] (hD : IsClosed (D : Set G))
    (χ : D →ₜ* A) (V₀ : OpenNormalSubgroup G) :
    ∃ U : OpenNormalSubgroup G, ∃ hDU : D ≤ (U : Subgroup G),
      (U : Subgroup G) ≤ D ⊔ (V₀ : Subgroup G) ∧
      ∃ η : U →ₜ* A, ∀ d : D, η (Subgroup.inclusion hDU d) = χ d := by
  classical
  let T : ClosedSubgroup G := ⟨D, hD⟩
  let K : OpenSubgroup D := (OpenNormalSubgroup.ker χ).toOpenSubgroup
  obtain ⟨W, hW⟩ := exists_openNormalSubgroup_inter_closedSubgroup_le T K
  let V : OpenNormalSubgroup G := W ⊓ V₀
  let Usub : Subgroup G := D ⊔ (V : Subgroup G)
  have hUopen : IsOpen (Usub : Set G) :=
    Subgroup.isOpen_of_openSubgroup Usub (show (V : Subgroup G) ≤ Usub from le_sup_right)
  let U : OpenNormalSubgroup G :=
    { toOpenSubgroup := ⟨Usub, hUopen⟩
      isNormal' := inferInstance }
  have hDU : D ≤ (U : Subgroup G) := le_sup_left
  let q := QuotientGroup.mk' (V : Subgroup G)
  let L : Subgroup (G ⧸ (V : Subgroup G)) := D.map q
  let ψ : D →* L :=
    { toFun := fun d => ⟨q d.1, ⟨d.1, d.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun a b => Subtype.ext (map_mul q a.1 b.1) }
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨d, hd, hdz⟩ := z.2
    exact ⟨⟨d, hd⟩, Subtype.ext hdz⟩
  have hψker : ψ.ker ≤ χ.toMonoidHom.ker := by
    intro d hd
    have hdV : d.1 ∈ (V : Subgroup G) :=
      (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) d.1).mp
        (congrArg Subtype.val hd)
    exact hW hdV.1
  let ψlift : L →* A := ψ.liftOfSurjective hψsurj ⟨χ.toMonoidHom, hψker⟩
  let qU : U →* L :=
    { toFun := fun u => ⟨q u.1, by
        obtain ⟨d, hd, v, hv, hdv⟩ :=
          (Subgroup.mem_sup_of_normal_right (s := D) (t := (V : Subgroup G))).mp u.2
        refine ⟨d, hd, ?_⟩
        have hqv : q v = 1 :=
          (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) v).mpr hv
        rw [← hdv, map_mul, hqv, mul_one]⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun a b => Subtype.ext (map_mul q a.1 b.1) }
  have hqU : Continuous qU := by
    exact (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk
      (fun u => (qU u).2)
  let η : U →ₜ* A :=
    ⟨ψlift.comp qU, (show Continuous ψlift from continuous_of_discreteTopology).comp hqU⟩
  refine ⟨U, hDU, sup_le_sup le_rfl inf_le_right, η, ?_⟩
  intro d
  change ψlift (ψ d) = χ d
  exact DFunLike.congr_fun (ψ.liftOfRightInverse_comp
    (Function.surjInv hψsurj) (Function.rightInverse_surjInv hψsurj)
    ⟨χ.toMonoidHom, hψker⟩) d

end ProCGroups
