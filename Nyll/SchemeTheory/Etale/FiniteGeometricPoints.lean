/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Geometric lifts through a finite morphism

An algebraically closed geometric fiber of a finite morphism is Artinian.
The correspondence between rational points and closed points therefore
constructs every geometric lift and proves that the set of lifts is finite.
No étaleness or reducedness of the finite morphism is used.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (q : Y ⟶ X)
  {Ω : Type u} [Field Ω] (t : Spec (CommRingCat.of Ω) ⟶ X)

/-- Geometric lifts through a scheme morphism are sections of its geometric fiber. -/
def Scheme.Hom.geometricLiftEquivFiberSection :
    {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t} ≃
      {p : Spec (CommRingCat.of Ω) ⟶ pullback q t //
        p ≫ pullback.snd q t = 𝟙 _} where
  toFun s := ⟨pullback.lift s.val (𝟙 _) (s.property.trans (Category.id_comp t).symm),
    pullback.lift_snd _ _ _⟩
  invFun p := ⟨p.val ≫ pullback.fst q t, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, p.property,
      Category.id_comp]⟩
  left_inv s := Subtype.ext (pullback.lift_fst _ _ _)
  right_inv p := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans p.property.symm

variable [IsFinite q] [IsAlgClosed Ω]

/-- Every point of the ordinary fiber is the image of an algebraically closed
geometric lift. -/
theorem Scheme.Hom.exists_geometricLift_of_isFinite
    (y : Y) (hy : q y = t default) :
    ∃ s : Spec (CommRingCat.of Ω) ⟶ Y, s ≫ q = t ∧ s default = y := by
  let p : pullback q t ⟶ Spec (CommRingCat.of Ω) := pullback.snd q t
  have : IsLocallyArtinian (pullback q t) :=
    IsLocallyArtinian.of_locallyQuasiFinite p
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := q) (g := t) y default hy
  let a : Spec (CommRingCat.of Ω) ⟶ pullback q t :=
    pointOfClosedPoint p z isClosed_singleton
  have ha : a ≫ p = 𝟙 _ := pointOfClosedPoint_comp p z isClosed_singleton
  refine ⟨a ≫ pullback.fst q t, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (fun k => k ≫ t) ha).trans (Category.id_comp t)
  · rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
    exact hz

/-- The lifts of an algebraically closed geometric point through a finite
morphism form a finite type, including an empty fiber. -/
theorem Scheme.Hom.finite_geometricLifts_of_isFinite :
    Finite {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t} := by
  let YΩ : Scheme.{u} := pullback q t
  let p : YΩ ⟶ Spec (CommRingCat.of Ω) := pullback.snd q t
  have : IsLocallyArtinian YΩ :=
    IsLocallyArtinian.of_locallyQuasiFinite p
  have : CompactSpace YΩ := QuasiCompact.compactSpace_of_compactSpace p
  have : Finite YΩ := finite_of_compact_of_discrete
  exact Finite.of_equiv (closedPoints YΩ)
    ((q.geometricLiftEquivFiberSection t).trans (pointEquivClosedPoint p)).symm

end AlgebraicGeometry
