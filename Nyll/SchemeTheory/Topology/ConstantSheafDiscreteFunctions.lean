/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# The actual constant sheaf as discrete-valued functions

The constant presheaf maps to the existing sheaf of continuous functions
into a discrete space. This map is locally injective by evaluation and
locally surjective because each continuous function is constant on the
open fibre of its value at a point. Sheafification therefore gives an
isomorphism from the categorical constant sheaf.

This is the constant-sheaf comparison used in the Stacks Project,
tag 09ZG: https://stacks.math.columbia.edu/tag/09ZG.
The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory TopCat TopologicalSpace Opposite

namespace SchemeTheory

variable (X : TopCat.{u}) (A : Type u)

/-- Send a value to its constant function, in the existing sheaf of
continuous maps into the actual discrete topological space. -/
def constantToDiscreteFunctions :
    (Functor.const (Opens X)ᵒᵖ).obj A ⟶ presheafToTop X (TopCat.discrete.obj A) where
  app U := TypeCat.ofHom (fun a =>
    TopCat.const (X := (Opens.toTopCat X).obj U.unop) (Y := TopCat.discrete.obj A) a)
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro a
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl

/-- The categorical constant sheaf is the existing sheaf of continuous
functions to the discrete value space. -/
def constantSheafIsoDiscreteFunctions :
    (constantSheaf (Opens.grothendieckTopology X) (Type u)).obj A ≅
      (sheafToTop (X := X) (TopCat.discrete.obj A) :
        CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) := by
  let J : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let P : (Opens X)ᵒᵖ ⥤ Type u := presheafToTop X (TopCat.discrete.obj A)
  let τ : (Functor.const (Opens X)ᵒᵖ).obj A ⟶ P := constantToDiscreteFunctions X A
  have hi : CategoryTheory.Presheaf.IsLocallyInjective J τ := by
    constructor
    intro U a b hab x hx
    have heq : a = b := congrArg
      (fun k : (Opens.toTopCat X).obj U.unop ⟶ TopCat.discrete.obj A => k ⟨x, hx⟩) hab
    refine ⟨U.unop, 𝟙 U.unop, ?_, hx⟩
    change a = b
    exact heq
  have hs : CategoryTheory.Presheaf.IsLocallySurjective J τ := by
    constructor
    intro U s x hx
    let s' : (Opens.toTopCat X).obj U ⟶ TopCat.discrete.obj A := s
    let a : TopCat.discrete.obj A := s' ⟨x, hx⟩
    let W : Set U := {y | s' y = a}
    have hW : IsOpen W :=
      s'.hom.continuous.isOpen_preimage {a} (isOpen_discrete {a})
    let V : Opens X := ⟨Subtype.val '' W, U.isOpen.isOpenMap_subtype_val W hW⟩
    have hVU : V ≤ U := by
      rintro y ⟨z, _, rfl⟩
      exact z.2
    have hxV : x ∈ V := ⟨⟨x, hx⟩, rfl, rfl⟩
    refine ⟨V, homOfLE hVU, ⟨a, ?_⟩, hxV⟩
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    change a = s' ⟨y.1, hVU y.2⟩
    obtain ⟨z, hz, hzy⟩ := y.2
    have heq : z = ⟨y.1, hVU y.2⟩ := Subtype.ext hzy
    exact hz.symm.trans (congrArg s' heq)
  have hW : J.W τ := J.W_of_isLocallyBijective τ
  let F : CategoryTheory.Sheaf J (Type u) := sheafToTop (X := X) (TopCat.discrete.obj A)
  let m : (constantSheaf J (Type u)).obj A ⟶ (presheafToSheaf J (Type u)).obj F.obj :=
    (presheafToSheaf J (Type u)).map τ
  have : IsIso m := (J.W_iff τ).mp hW
  exact asIso m ≪≫ (sheafificationIso F).symm

end SchemeTheory
