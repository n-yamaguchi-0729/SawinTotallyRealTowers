/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Category Theory Is Pullback fst pullback Map of comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CategoryTheory.Proofs
namespace CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq

universe v w u

open _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem _root_.CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq {C : Type w} [Category.{v} C]
  {X X' S T : C}
    (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f')
    [HasPullback f t] [HasPullback f' t] :
    IsPullback (pullback.fst f' t)
      (pullback.map f' t f t π (𝟙 T) (𝟙 S)
        (by rw [Category.comp_id, hπ]) (by rw [Category.comp_id, Category.id_comp]))
      π (pullback.fst f t) := by
  have big : IsPullback (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ])
      (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.snd f t)
      (pullback.fst f' t) t (π ≫ f) := by
    rw [pullback.lift_snd, Category.comp_id, hπ]
    exact (IsPullback.of_hasPullback f' t).flip
  exact (IsPullback.of_right big (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f
    t).flip).flip
end CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq
end AlgebraicCurves.Foundations.CategoryTheory.Proofs
end ProofImplementation
