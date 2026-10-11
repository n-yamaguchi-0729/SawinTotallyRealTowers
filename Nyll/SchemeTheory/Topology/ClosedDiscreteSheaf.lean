/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks of discrete-valued functions on a closed support

The actual sheaf of continuous functions into a discrete value space has
stalk equal to that value space, by evaluation. Constant functions give
surjectivity, while open fibers give injectivity. Pushing forward from a
subset preserves these stalks at points of the subset.

The constructions keep the actual evaluation and germ formulas visible
for the closed-support pullback and restriction comparisons.
The Lean proofs are original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopCat TopologicalSpace Topology Opposite

namespace SchemeTheory

/-- The actual evaluation morphism on the discrete-function sheaf's stalk. -/
def discreteFunctionsStalkEval (X : TopCat.{u}) (A : Type u) (x : X) :
    TopCat.Presheaf.stalk (presheafToTop X (TopCat.discrete.obj A)) x ⟶ A :=
  (TopCat.Presheaf.stalkFunctor (Type u) x).map
    (subpresheafContinuousPrelocalIsoPresheafToTop (X := X) (TopCat.discrete.obj A)).inv ≫
      stalkToFiber (continuousLocal X (TopCat.discrete.obj A)) x

theorem discreteFunctionsStalkEval_bijective (X : TopCat.{u}) (A : Type u) (x : X) :
    Function.Bijective (discreteFunctionsStalkEval X A x) := by
  let L : LocalPredicate (fun _ : X => TopCat.discrete.obj A) :=
    continuousLocal X (TopCat.discrete.obj A)
  let Q : X.Presheaf (Type u) := (subsheafToTypes L).obj
  let P : X.Presheaf (Type u) := presheafToTop X (TopCat.discrete.obj A)
  let e : Q ≅ P := subpresheafContinuousPrelocalIsoPresheafToTop (TopCat.discrete.obj A)
  let ev : Q.stalk x ⟶ A := stalkToFiber L x
  have hsurj : Function.Surjective ev := by
    apply stalkToFiber_surjective L x
    intro a
    refine ⟨⟨⊤, trivial⟩, fun _ => a, ?_, rfl⟩
    exact continuous_const
  have hinj : Function.Injective ev := by
    apply stalkToFiber_injective L x
    intro U V fU hU fV hV hUV
    have hfU : Continuous fU := hU
    have hfV : Continuous fV := hV
    let AU : Set U.1 := fU ⁻¹' {fU ⟨x, U.2⟩}
    let AV : Set V.1 := fV ⁻¹' {fV ⟨x, V.2⟩}
    have hAU : IsOpen AU := hfU.isOpen_preimage _ (isOpen_discrete _)
    have hAV : IsOpen AV := hfV.isOpen_preimage _ (isOpen_discrete _)
    let OU : Opens X := ⟨Subtype.val '' AU, U.1.isOpen.isOpenMap_subtype_val AU hAU⟩
    let OV : Opens X := ⟨Subtype.val '' AV, V.1.isOpen.isOpenMap_subtype_val AV hAV⟩
    have hOU : OU ≤ U.1 := by
      rintro y ⟨z, _, rfl⟩
      exact z.2
    have hOV : OV ≤ V.1 := by
      rintro y ⟨z, _, rfl⟩
      exact z.2
    let W : OpenNhds x := ⟨OU ⊓ OV,
      ⟨⟨⟨x, U.2⟩, rfl, rfl⟩, ⟨⟨x, V.2⟩, rfl, rfl⟩⟩⟩
    let iU : W ⟶ U := homOfLE (inf_le_left.trans hOU)
    let iV : W ⟶ V := homOfLE (inf_le_right.trans hOV)
    refine ⟨W, iU, iV, ?_⟩
    intro w
    obtain ⟨a, ha, haw⟩ := w.2.1
    obtain ⟨b, hb, hbw⟩ := w.2.2
    have haw' : a = (iU w : U.1) := Subtype.ext haw
    have hbw' : b = (iV w : V.1) := Subtype.ext hbw
    exact (congrArg fU haw').symm.trans
      (ha.trans (hUV.trans (hb.symm.trans (congrArg fV hbw'))))
  have hmap : Function.Bijective ((TopCat.Presheaf.stalkFunctor (Type u) x).map e.inv) :=
    ConcreteCategory.bijective_of_isIso _
  exact (show Function.Bijective ev from ⟨hinj, hsurj⟩).comp hmap

/-- Evaluation identifies the actual discrete-function sheaf's stalk
with the value type, including when the value type is empty. -/
def discreteFunctionsStalkIso (X : TopCat.{u}) (A : Type u) (x : X) :
    TopCat.Presheaf.stalk (presheafToTop X (TopCat.discrete.obj A)) x ≅ A :=
  (Equiv.ofBijective (discreteFunctionsStalkEval X A x)
    (discreteFunctionsStalkEval_bijective X A x)).toIso

theorem discreteFunctionsStalkIso_hom (X : TopCat.{u}) (A : Type u) (x : X) :
    (discreteFunctionsStalkIso X A x).hom = discreteFunctionsStalkEval X A x := rfl

/-- The stalk isomorphism sends the germ of a continuous function to its
value at the point. -/
theorem discreteFunctionsStalkIso_germ (X : TopCat.{u}) (A : Type u) (x : X)
    (U : Opens X) (hx : x ∈ U)
    (s : (Opens.toTopCat X).obj U ⟶ TopCat.discrete.obj A) :
    (discreteFunctionsStalkIso X A x).hom
      (TopCat.Presheaf.germ (presheafToTop X (TopCat.discrete.obj A)) U x hx s) =
        s ⟨x, hx⟩ := by
  let L : LocalPredicate (fun _ : X => TopCat.discrete.obj A) :=
    continuousLocal X (TopCat.discrete.obj A)
  let Q : X.Presheaf (Type u) := (subsheafToTypes L).obj
  let P : X.Presheaf (Type u) := presheafToTop X (TopCat.discrete.obj A)
  let e : Q ≅ P := subpresheafContinuousPrelocalIsoPresheafToTop (TopCat.discrete.obj A)
  let ev : Q.stalk x ⟶ A := stalkToFiber L x
  change ev ((TopCat.Presheaf.stalkFunctor (Type u) x).map e.inv (P.germ U x hx s)) =
    s ⟨x, hx⟩
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx e.inv s
  exact (congrArg ev h).trans (stalkToFiber_germ L U x hx (e.inv.app (op U) s))

variable {X : TopCat.{u}}

/-- The actual pushforward of discrete-valued functions from a subset.
Closedness is only needed to calculate stalks outside the subset. -/
def closedDiscreteSheaf (C : Set X) (A : Type u) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) :=
  (TopCat.Sheaf.pushforward (Type u)
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(TopCat.of C, X)))).obj
      (sheafToTop (X := TopCat.of C) (TopCat.discrete.obj A))

/-- At a point of the support, the actual pushforward stalk is the value type. -/
def closedDiscreteStalkIso (C : Set X) (A : Type u) (x : C) :
    TopCat.Presheaf.stalk (closedDiscreteSheaf C A).obj x.1 ≅ A := by
  let Z : TopCat.{u} := TopCat.of C
  let i : Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let P : Z.Presheaf (Type u) := presheafToTop Z (TopCat.discrete.obj A)
  have hi : IsInducing i := IsInducing.subtypeVal
  let m : TopCat.Presheaf.stalk (closedDiscreteSheaf C A).obj x.1 ⟶ P.stalk x :=
    P.stalkPushforward (Type u) i x
  have hiso : IsIso m :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing (Type u) hi P x
  exact asIso m ≪≫ discreteFunctionsStalkIso Z A x

/-- The supported stalk comparison evaluates the represented function
at the corresponding point of the subset. -/
theorem closedDiscreteStalkIso_germ (C : Set X) (A : Type u) (x : C)
    (U : Opens X) (hx : x.1 ∈ U)
    (s : TopCat.of {z : C // z.1 ∈ U} ⟶ TopCat.discrete.obj A) :
    (closedDiscreteStalkIso C A x).hom
      (TopCat.Presheaf.germ (closedDiscreteSheaf C A).obj U x.1 hx s) =
        s ⟨x, hx⟩ := by
  let Z : TopCat.{u} := TopCat.of C
  let i : Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let P : Z.Presheaf (Type u) := presheafToTop Z (TopCat.discrete.obj A)
  let H : X.Presheaf (Type u) := (TopCat.Presheaf.pushforward (Type u) i).obj P
  let V : Opens Z := (Opens.map i).obj U
  have hxV : x ∈ V := hx
  change (discreteFunctionsStalkIso Z A x).hom
    (P.stalkPushforward (Type u) i x (H.germ U x.1 hx s)) = s ⟨x, hxV⟩
  have h := congrArg
    (fun f : H.obj (op U) ⟶ P.stalk x => f s)
    (TopCat.Presheaf.stalkPushforward_germ (Type u) i P U x hx)
  exact (congrArg (discreteFunctionsStalkIso Z A x).hom h).trans
    (discreteFunctionsStalkIso_germ Z A x V hxV s)

end SchemeTheory
