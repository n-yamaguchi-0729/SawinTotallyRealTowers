/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! SectionsGluing for scheme modules. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Sections of a scheme module satisfy separatedness and gluing on an open cover. -/
theorem eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (V : X.Opens)
    (hUV : ∀ i, U i ≤ V) (hV : V ≤ ⨆ i, U i) :
    (∀ s t : Γ(M, V),
        (∀ i, M.presheaf.map (homOfLE (hUV i)).op s =
          M.presheaf.map (homOfLE (hUV i)).op t) → s = t) ∧
      (∀ v : ∀ i, Γ(M, U i),
        (∀ i j, M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (v i) =
            M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (v j)) →
          ∃ s : Γ(M, V), ∀ i, M.presheaf.map (homOfLE (hUV i)).op s = v i) := by
  let F : TopCat.Sheaf Ab X.carrier := ⟨M.val.presheaf, M.isSheaf⟩
  constructor
  · intro s t h
    exact TopCat.Sheaf.eq_of_locally_eq' F U V (fun i => homOfLE (hUV i)) hV s t h
  · intro v hv
    obtain ⟨s, hs, -⟩ :=
      TopCat.Sheaf.existsUnique_gluing' F U V (fun i => homOfLE (hUV i)) hV v (fun i j => hv i j)
    exact ⟨s, hs⟩

end AlgebraicGeometry.Scheme.Modules
