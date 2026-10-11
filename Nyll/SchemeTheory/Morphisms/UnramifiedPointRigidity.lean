/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.UnramifiedHomExt
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Topology.Connected.Clopen

/-!
# Unramified maps determined at one nonempty test scheme

The relative equalizer of maps to a separated unramified scheme is both
open and closed. Agreement after a map from a nonempty scheme makes this
equalizer nonempty. A preconnected source therefore forces the maps equal.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Over a preconnected source, maps into a separated unramified scheme
are equal if they agree after any map from a nonempty scheme. -/
theorem Over.hom_ext_of_nonempty_of_unramified
    {S : Scheme.{u}} {X Y Z : Over S}
    [PreconnectedSpace X.left] [Nonempty Z.left]
    [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y) (i : Z ⟶ X) (h : i ≫ f = i ≫ g) : f = g := by
  let e : equalizer f g ⟶ X := equalizer.ι f g
  let l : Z ⟶ equalizer f g := equalizer.lift i h
  have : Nonempty (equalizer f g).left := Nonempty.map l.left inferInstance
  have hRange : Set.range e.left = Set.univ :=
    IsClopen.eq_univ
      ⟨e.left.isClosedEmbedding.isClosed_range, e.left.isOpenEmbedding.isOpen_range⟩
      (Set.range_nonempty e.left)
  have : Surjective e.left := ⟨Set.range_eq_univ.mp hRange⟩
  have : IsIso e.left :=
    (isIso_iff_isOpenImmersion_and_surjective e.left).mpr ⟨inferInstance, inferInstance⟩
  apply CategoryTheory.Over.OverMorphism.ext
  apply (cancel_epi e.left).mp
  exact congrArg (fun a : equalizer f g ⟶ Y => a.left) (equalizer.condition f g)

/-- A relative endomorphism of a preconnected separated unramified scheme
is the identity if it fixes a morphism from a nonempty scheme. -/
theorem Scheme.Hom.eq_id_of_unramified_of_fixes_nonempty
    {X S T : Scheme.{u}} [PreconnectedSpace X] [Nonempty T]
    (f : X ⟶ S) [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f]
    (e : X ⟶ X) (he : e ≫ f = f) (z : T ⟶ X) (hz : z ≫ e = z) : e = 𝟙 X := by
  let Xo : Over S := Over.mk f
  let To : Over S := Over.mk (z ≫ f)
  let eo : Xo ⟶ Xo := Over.homMk e he
  let zo : To ⟶ Xo := Over.homMk z rfl
  have hpoint : zo ≫ eo = zo ≫ 𝟙 Xo := by
    apply CategoryTheory.Over.OverMorphism.ext
    change z ≫ e = z ≫ 𝟙 X
    exact hz.trans (Category.comp_id z).symm
  have : PreconnectedSpace Xo.left := inferInstanceAs (PreconnectedSpace X)
  have : Nonempty To.left := inferInstanceAs (Nonempty T)
  have : FormallyUnramified Xo.hom := inferInstanceAs (FormallyUnramified f)
  have : LocallyOfFiniteType Xo.hom := inferInstanceAs (LocallyOfFiniteType f)
  have : IsSeparated Xo.hom := inferInstanceAs (IsSeparated f)
  have hidentity : eo = 𝟙 Xo :=
    Over.hom_ext_of_nonempty_of_unramified eo (𝟙 Xo) zo hpoint
  exact congrArg (fun k : Xo ⟶ Xo => k.left) hidentity

end AlgebraicGeometry
