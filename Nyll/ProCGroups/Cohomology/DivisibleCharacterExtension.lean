/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Cohomology.FiniteCharacterExtension
import Mathlib.Algebra.Category.Grp.Injective

/-! # Extending finite characters into divisible groups -/

namespace ProCGroups

open ProC

universe u v w

/-- A continuous discrete character on a closed subgroup of a profinite abelian
group extends continuously after mapping its values to a divisible group. -/
theorem exists_continuous_character_extension_divisible
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    {B : Type v} [Group B] [TopologicalSpace B] [DiscreteTopology B]
    {M : Type w} [CommGroup M] [TopologicalSpace M] [DivisibleBy (Additive M) ℤ]
    (D : Subgroup A) (hD : IsClosed (D : Set A)) (χ : D →ₜ* B) (ι : B →* M) :
    ∃ η : A →ₜ* M, ∀ d : D, η d.1 = ι (χ d) := by
  let T : ClosedSubgroup A := ⟨D, hD⟩
  let K : OpenSubgroup D := (OpenNormalSubgroup.ker χ).toOpenSubgroup
  obtain ⟨V, hV⟩ := exists_openNormalSubgroup_inter_closedSubgroup_le T K
  let q := QuotientGroup.mk' (V : Subgroup A)
  let L : Subgroup (A ⧸ (V : Subgroup A)) := D.map q
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
    apply hV
    exact (QuotientGroup.eq_one_iff (N := (V : Subgroup A)) d.1).mp
      (congrArg Subtype.val hd)
  let α : L →* B := ψ.liftOfSurjective hψsurj ⟨χ.toMonoidHom, hψker⟩
  have hα (d : D) : α (ψ d) = χ d :=
    DFunLike.congr_fun
      (ψ.liftOfRightInverse_comp (Function.surjInv hψsurj)
        (Function.rightInverse_surjInv hψsurj) ⟨χ.toMonoidHom, hψker⟩) d
  obtain ⟨β, hβ⟩ := (Module.Baer.of_divisible (Additive M)).extension_property_addMonoidHom
    L.subtype.toAdditive (show Function.Injective L.subtype.toAdditive from Subtype.val_injective)
    (ι.comp α).toAdditive
  let βmul : (A ⧸ (V : Subgroup A)) →* M := β.toMultiplicative
  let βcont : (A ⧸ (V : Subgroup A)) →ₜ* M :=
    ⟨βmul, continuous_of_discreteTopology⟩
  refine ⟨βcont.comp (OpenNormalSubgroup.quotientProj V), ?_⟩
  intro d
  have hh := DFunLike.congr_fun hβ (Additive.ofMul (ψ d))
  change βmul (q d.1) = ι (α (ψ d)) at hh
  exact hh.trans (congrArg ι (hα d))

end ProCGroups
