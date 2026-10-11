/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.DifferentialModule.Map.Limit

/-!
# Fox differential: completed — differential module — map — group like

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraMap_of`
  The completed prime-power group-algebra map sends the group-like element of `g` to the group-like
  element of `ψ g`.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [Fact (0 < ℓ)] in
/--
The completed prime-power group-algebra map sends the group-like element of `g` to the group-like
element of `ψ g`.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraMap_of
    (ψ : ContinuousMonoidHom G H) (g : G) :
    primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := G) g) =
      primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := H) (ψ g) := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ H).ext
  intro i
  change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := H) i
      (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := G) g)) =
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := H) i
      (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := H) (ψ g))
  erw [primePowerCompletedGroupAlgebraProjection_map]
  erw [primePowerCompletedGroupAlgebraProjection_of]
  erw [primePowerCompletedGroupAlgebraMapStage_of]
  erw [primePowerCompletedGroupAlgebraProjection_of]
  rfl


end

end FoxDifferential
