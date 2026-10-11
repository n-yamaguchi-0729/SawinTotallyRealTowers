/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.Topology.Sheaves.Stalks
import Nyll.SchemeTheory.Topology.ClosedDiscreteSheaf

/-!
# The stalk outside a closed discrete-function support

The open complement of the support has exactly the empty function as
section, even for an empty value type. Every germ at a point outside the
support restricts to this section, so the actual stalk is terminal.
The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopCat TopologicalSpace Opposite

namespace SchemeTheory

/-- Outside a closed support, the actual supported discrete-function
sheaf has a terminal stalk. No inhabitedness of the value type is needed. -/
def closedDiscreteStalkIsTerminal {X : TopCat.{u}} (C : Set X) (hC : IsClosed C)
    (A : Type u) (x : X) (hx : x ∉ C) :
    IsTerminal (TopCat.Presheaf.stalk (closedDiscreteSheaf C A).obj x) := by
  let Z : TopCat.{u} := TopCat.of C
  let i : Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let P : X.Presheaf (Type u) := (TopCat.Presheaf.pushforward (Type u) i).obj
    (presheafToTop Z (TopCat.discrete.obj A))
  let V : Opens X := ⟨Cᶜ, hC.isOpen_compl⟩
  have hxV : x ∈ V := hx
  let emptyFunction : {z : C // z.1 ∈ V} → TopCat.discrete.obj A :=
    fun z => False.elim (z.2 z.1.2)
  have hEmptyFunction : Continuous emptyFunction :=
    continuous_of_const (fun z _ => False.elim (z.2 z.1.2))
  let e : TopCat.of {z : C // z.1 ∈ V} ⟶ TopCat.discrete.obj A :=
    (TopCat.Hom.equivContinuousMap (TopCat.of {z : C // z.1 ∈ V})
      (TopCat.discrete.obj A)).symm ⟨emptyFunction, hEmptyFunction⟩
  let sV : P.obj (op V) := e
  change IsTerminal (P.stalk x)
  have hUnique : Unique (P.stalk x) := by
    refine { default := P.germ V x hxV sV, uniq := ?_ }
    intro a
    obtain ⟨U, hxU, s, hs⟩ := P.exists_germ_eq a
    have heq : P.map (Opens.infLELeft U V).op s =
        P.map (Opens.infLERight U V).op sV := by
      let f : TopCat.of {z : C // z.1 ∈ U ⊓ V} ⟶ TopCat.discrete.obj A :=
        P.map (Opens.infLELeft U V).op s
      let g : TopCat.of {z : C // z.1 ∈ U ⊓ V} ⟶ TopCat.discrete.obj A :=
        P.map (Opens.infLERight U V).op sV
      change f = g
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      exact False.elim (z.2.2 z.1.2)
    exact hs.symm.trans (P.germ_ext (U ⊓ V) ⟨hxU, hxV⟩
      (Opens.infLELeft U V) (Opens.infLERight U V) heq)
  exact (Types.isTerminalEquivUnique (P.stalk x)).symm hUnique

end SchemeTheory
