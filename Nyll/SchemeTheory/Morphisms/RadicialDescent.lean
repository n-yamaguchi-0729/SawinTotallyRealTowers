/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Descent of universal injectivity through a surjective morphism

The map between the two diagonal objects induced by a surjective morphism is
surjective. Thus surjectivity of the diagonal of a composite implies
surjectivity of the diagonal of its second factor.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.UniversallyInjective

/-- Universal injectivity descends through a surjective first factor. -/
theorem of_comp_surjective {X Y Z : Scheme.{u}}
    (t : X ⟶ Y) (g : Y ⟶ Z) [Surjective t] [UniversallyInjective (t ≫ g)] :
    UniversallyInjective g := by
  let m : pullback (t ≫ g) (t ≫ g) ⟶ pullback g g :=
    pullback.map (t ≫ g) (t ≫ g) g g t t (𝟙 Z)
      (by simp only [Category.comp_id]) (by simp only [Category.comp_id])
  let : Surjective m := ⟨by
    apply Set.range_eq_univ.mp
    dsimp only [m]
    rw [Scheme.Pullback.range_map]
    simp only [Set.range_eq_univ.mpr t.surjective, Set.preimage_univ, Set.inter_self]⟩
  let : Surjective (pullback.diagonal (t ≫ g)) :=
    (UniversallyInjective.iff_diagonal (t ≫ g)).mp inferInstance
  have h : pullback.diagonal (t ≫ g) ≫ m = t ≫ pullback.diagonal g := by
    apply pullback.hom_ext
    · simp only [m, Category.assoc, pullback.lift_fst,
        pullback.diagonal_fst, pullback.diagonal_fst_assoc, Category.comp_id]
    · simp only [m, Category.assoc, pullback.lift_snd,
        pullback.diagonal_snd, pullback.diagonal_snd_assoc, Category.comp_id]
  let : Surjective (t ≫ pullback.diagonal g) := by
    rw [← h]
    infer_instance
  exact (UniversallyInjective.iff_diagonal g).mpr
    (Surjective.of_comp t (pullback.diagonal g))

end AlgebraicGeometry.UniversallyInjective
