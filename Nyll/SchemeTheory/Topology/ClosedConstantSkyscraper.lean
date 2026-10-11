/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.Sober

/-!
# Skyscrapers as closed-supported constant sheaves

On a space with a generic point, the skyscraper at that point is the
actual sheafification of a constant presheaf. The comparison is locally
bijective because every nonempty open contains the generic point.
Pushing this comparison forward from the closure of a point identifies
its skyscraper with the pushforward of the actual constant sheaf on that
closed subset.

This supplies the closed-constant comparison in Stacks Project, tag 0CAL:
https://stacks.math.columbia.edu/tag/0CAL. The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopCat TopologicalSpace Opposite

namespace SchemeTheory

attribute [local instance] Classical.propDecidable

variable {X : TopCat.{u}}

/-- The constant presheaf maps to the skyscraper by the identity on opens
containing the point, and the terminal map on the remaining opens. -/
def constantToSkyscraper (x : X) (A : Type u) :
    (Functor.const (Opens X)ᵒᵖ).obj A ⟶ skyscraperPresheaf x A where
  app U := if h : x ∈ U.unop then eqToHom (ite_eq_left h).symm
    else terminal.from A ≫ eqToHom (ite_eq_right h).symm
  naturality U V f := by
    dsimp only [Functor.const_obj_obj, skyscraperPresheaf_obj]
    by_cases hV : x ∈ V.unop
    · have hU : x ∈ U.unop := f.unop.le hV
      simp only [Functor.const_obj_map, Category.id_comp, dite_eq_left hU, dite_eq_left hV,
        skyscraperPresheaf_map]
      let eU : A = (skyscraperPresheaf x A).obj U := (ite_eq_left hU).symm
      let eUV : (skyscraperPresheaf x A).obj U =
          (skyscraperPresheaf x A).obj V := (ite_eq_left hU).trans (ite_eq_left hV).symm
      exact (eqToHom_trans eU eUV).symm
    · simp only [Functor.const_obj_map, Category.id_comp, dite_eq_right hV,
        skyscraperPresheaf_map]
      apply ((ite_eq_right hV).symm.ndrec terminalIsTerminal).hom_ext

private lemma constantToSkyscraper_app_isIso (x : X) (A : Type u)
    (U : (Opens X)ᵒᵖ) (hx : x ∈ U.unop) :
    IsIso ((constantToSkyscraper x A).app U) := by
  dsimp only [constantToSkyscraper, Functor.const_obj_obj, skyscraperPresheaf_obj]
  rw [dite_eq_left hx]
  exact (eqToIso (show A = (skyscraperPresheaf x A).obj U from
    (ite_eq_left hx).symm)).isIso_hom

/-- For a generic point, the locally bijective map from the constant
presheaf induces an isomorphism of the actual constant sheaf. -/
def constantSheafIsoSkyscraper (x : X) (hx : ∀ y : X, x ⤳ y) (A : Type u) :
    (constantSheaf (Opens.grothendieckTopology X) (Type u)).obj A ≅
      skyscraperSheaf x A := by
  let J := Opens.grothendieckTopology X
  let τ := constantToSkyscraper x A
  have hi : CategoryTheory.Presheaf.IsLocallyInjective J τ := by
    constructor
    intro U a b hab y hy
    have hxU : x ∈ U.unop := (hx y).mem_open U.unop.isOpen hy
    have : IsIso (τ.app U) := constantToSkyscraper_app_isIso x A U hxU
    have heq : a = b := (ConcreteCategory.injective_of_mono_of_preservesPullback (τ.app U)) hab
    refine ⟨U.unop, 𝟙 U.unop, ?_, hy⟩
    change ((Functor.const (Opens X)ᵒᵖ).obj A).map (𝟙 U.unop).op a =
      ((Functor.const (Opens X)ᵒᵖ).obj A).map (𝟙 U.unop).op b
    exact congrArg _ heq
  have hs : CategoryTheory.Presheaf.IsLocallySurjective J τ := by
    constructor
    intro U s y hy
    have hxU : x ∈ U := (hx y).mem_open U.isOpen hy
    have : IsIso (τ.app (op U)) := constantToSkyscraper_app_isIso x A (op U) hxU
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (τ.app (op U))).surjective s
    refine ⟨U, 𝟙 U, ⟨a, ?_⟩, hy⟩
    change τ.app (op U) a = (skyscraperPresheaf x A).map (𝟙 (op U)) s
    have hid : (skyscraperPresheaf x A).map (𝟙 (op U)) s = s :=
      congrArg (fun k : (skyscraperPresheaf x A).obj (op U) ⟶
        (skyscraperPresheaf x A).obj (op U) => k s)
        ((skyscraperPresheaf x A).map_id (op U))
    exact ha.trans hid.symm
  have hW : J.W τ := J.W_of_isLocallyBijective τ
  let m : (constantSheaf J (Type u)).obj A ⟶
      (presheafToSheaf J (Type u)).obj (skyscraperSheaf x A).obj :=
    (presheafToSheaf J (Type u)).map τ
  have : IsIso m := (J.W_iff τ).mp hW
  exact asIso m ≪≫
    (sheafificationIso (skyscraperSheaf x A)).symm

/-- A skyscraper is the pushforward of the actual constant sheaf on the
closure of its point. No finiteness or separation hypothesis is needed. -/
def closedConstantSkyscraperIso (x : X) (A : Type u) :
    (TopCat.Sheaf.pushforward (Type u)
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C(closure ({x} : Set X), X)))).obj
      ((constantSheaf (Opens.grothendieckTopology (closure ({x} : Set X)))
        (Type u)).obj A) ≅ skyscraperSheaf x A := by
  let Z : TopCat.{u} := TopCat.of (closure ({x} : Set X))
  let p : Z := ⟨x, subset_closure (Set.mem_singleton x)⟩
  have hp (y : Z) : p ⤳ y :=
    (subtype_specializes_iff p y).mpr (specializes_iff_mem_closure.mpr y.2)
  let i : Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  refine (TopCat.Sheaf.pushforward (Type u) i).mapIso
    (constantSheafIsoSkyscraper p hp A) ≪≫ ?_
  exact Iso.refl _

end SchemeTheory
