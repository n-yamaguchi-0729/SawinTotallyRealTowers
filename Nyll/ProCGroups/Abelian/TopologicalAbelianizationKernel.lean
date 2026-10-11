/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients

/-!
# Kernels after topological abelianization

For a continuous surjection from a compact group to a Hausdorff group, the
kernel of the induced map on topological abelianizations is the image of the
original kernel. Compactness makes the image of the closed commutator closed,
so every target commutator class has a lift in the source closed commutator.
-/

namespace ProCGroups.Abelian.TopologicalAbelianization

universe u v

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G]
  {H : Type v} [TopologicalSpace H] [Group H] [IsTopologicalGroup H] [T2Space H]

/-- The kernel after topological abelianization is the abelianized image of
the original kernel of a continuous surjection from a compact group. -/
theorem ker_map_of_surjective (f : G →ₜ* H) (hf : Function.Surjective f) :
    (map f).toMonoidHom.ker = f.toMonoidHom.ker.map (mk G) := by
  have htop : (⊤ : Subgroup G).map f.toMonoidHom = ⊤ := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top]
    exact hf
  have hcomm : (Subgroup.closedCommutator G).map f.toMonoidHom =
      Subgroup.closedCommutator H := by
    apply FiniteStepSolvableQuotients.map_closedCommutator_eq_of_map_eq
      (f := f) htop htop
    exact f.continuous.isClosedMap _ (Subgroup.isClosed_closedCommutator G)
  apply le_antisymm
  · intro a ha
    obtain ⟨g, rfl⟩ := surjective_mk G a
    have hfg : f g ∈ Subgroup.closedCommutator H := by
      apply mk_eq_one_iff.mp
      exact ha
    rw [← hcomm] at hfg
    obtain ⟨d, hd, hfd⟩ := hfg
    change f d = f g at hfd
    refine ⟨g * d⁻¹, ?_, ?_⟩
    · change f (g * d⁻¹) = 1
      rw [map_mul, map_inv, hfd, mul_inv_cancel]
    · rw [map_mul, map_inv, mk_eq_one_iff.mpr hd, inv_one, mul_one]
  · rintro a ⟨g, hg, rfl⟩
    change mk H (f g) = 1
    change f g = 1 at hg
    rw [hg, map_one]

/-- For a continuous surjection from a compact group, injectivity on
abelianizations is exactly containment of its kernel in the closed commutator. -/
theorem injective_map_iff_ker_le_closedCommutator
    (f : G →ₜ* H) (hf : Function.Surjective f) :
    Function.Injective (map f) ↔
      f.toMonoidHom.ker ≤ Subgroup.closedCommutator G := by
  change Function.Injective (map f).toMonoidHom ↔ _
  rw [← MonoidHom.ker_eq_bot_iff, ker_map_of_surjective f hf,
    Subgroup.map_eq_bot_iff]
  exact forall_congr' fun g ↦ forall_congr' fun _ ↦ mk_eq_one_iff

end ProCGroups.Abelian.TopologicalAbelianization
