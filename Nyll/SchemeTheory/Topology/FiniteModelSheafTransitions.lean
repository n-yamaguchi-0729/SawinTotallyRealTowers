/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Sheaves.Functors

/-!
# Actual sheaf approximation maps under refinement of a space

For a continuous map `q`, the approximation to a sheaf `F` is the actual
inverse image of its direct image, with its adjunction counit to `F`.
Factoring a map through a finer space gives a map between these actual
approximations. It is the adjoint of the finer unit after direct image.
The triangle identities prove compatibility with the counits, and the
same Hom equivalence proves identity and composition under refinement.

These maps are used to construct the finite-model approximation diagram
in the proof of Stacks Project, tag 09ZG:
https://stacks.math.columbia.edu/tag/09ZG.
The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace SchemeTheory

variable {X Y Z W : TopCat.{u}}


private abbrev actualSheafPullback (q : X ⟶ Y) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u) ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) :=
  TopCat.Sheaf.pullback (Type u) q

private abbrev actualSheafPushforward (q : X ⟶ Y) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u) :=
  TopCat.Sheaf.pushforward (Type u) q

private abbrev actualSheafAdjunction (q : X ⟶ Y) :
    actualSheafPullback q ⊣ actualSheafPushforward q :=
  TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) q

/-- The actual inverse image of the direct image of a sheaf. -/
abbrev sheafApproximation (q : X ⟶ Y)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) :=
  (actualSheafPullback q).obj ((actualSheafPushforward q).obj F)

/-- Refinement acts on actual sheaf approximations by the adjoint of the
direct image of the finer adjunction unit. -/
def sheafApproximationTransition (q : X ⟶ Y) (p : Y ⟶ Z)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    sheafApproximation (q ≫ p) F ⟶ sheafApproximation q F := by
  let L : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u) ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) :=
    actualSheafPullback q
  let R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u) :=
    actualSheafPushforward q
  let P : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u) ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology Z) (Type u) :=
    actualSheafPushforward p
  let a : L ⊣ R := actualSheafAdjunction q
  let b : actualSheafPullback (q ≫ p) ⊣ R ⋙ P :=
    actualSheafAdjunction (q ≫ p)
  exact (b.homEquiv (P.obj (R.obj F)) (L.obj (R.obj F))).symm
    (P.map (a.unit.app (R.obj F)))

/-- Approximation refinement commutes with the actual adjunction counits. -/
theorem sheafApproximationTransition_counit (q : X ⟶ Y) (p : Y ⟶ Z)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    sheafApproximationTransition q p F ≫
        (actualSheafAdjunction q).counit.app F =
      (actualSheafAdjunction (q ≫ p)).counit.app F := by
  let R := actualSheafPushforward q
  let P := actualSheafPushforward p
  let a := actualSheafAdjunction q
  let b : actualSheafPullback (q ≫ p) ⊣ R ⋙ P :=
    actualSheafAdjunction (q ≫ p)
  let B := (R ⋙ P).obj F
  let H := sheafApproximation q F
  let v : B ⟶ (R ⋙ P).obj H := P.map (a.unit.app (R.obj F))
  let t : (actualSheafPullback (q ≫ p)).obj B ⟶ H :=
    (b.homEquiv B H).symm v
  have ht : b.homEquiv B H t = v := (b.homEquiv B H).apply_symm_apply v
  have hbc : b.homEquiv B F (b.counit.app F) = 𝟙 B :=
    (congrArg (b.homEquiv B F) (b.homEquiv_symm_id F)).symm.trans
      ((b.homEquiv B F).apply_symm_apply (𝟙 B))
  change t ≫ a.counit.app F = b.counit.app F
  apply (b.homEquiv B F).injective
  calc
    b.homEquiv B F (t ≫ a.counit.app F) =
        b.homEquiv B H t ≫ (R ⋙ P).map (a.counit.app F) :=
      b.homEquiv_naturality_right t (a.counit.app F)
    _ = v ≫ (R ⋙ P).map (a.counit.app F) :=
      congrArg (fun k : B ⟶ (R ⋙ P).obj H => k ≫ (R ⋙ P).map (a.counit.app F)) ht
    _ = 𝟙 B := by
      change P.map (a.unit.app (R.obj F)) ≫ P.map (R.map (a.counit.app F)) = 𝟙 B
      exact (P.map_comp _ _).symm.trans
        ((congrArg P.map (a.right_triangle_components F)).trans (P.map_id (R.obj F)))
    _ = b.homEquiv B F (b.counit.app F) := hbc.symm

/-- Refining by the identity map gives the identity approximation map. -/
theorem sheafApproximationTransition_id (q : X ⟶ Y)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    sheafApproximationTransition q (𝟙 Y) F = 𝟙 (sheafApproximation q F) := by
  let a := actualSheafAdjunction q
  change (a.homEquiv _ _).symm (a.unit.app _) = 𝟙 _
  exact a.homEquiv_symm_unit _

/-- The actual approximation maps compose when finite-space refinements compose. -/
theorem sheafApproximationTransition_comp (q : X ⟶ Y) (p : Y ⟶ Z) (r : Z ⟶ W)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    sheafApproximationTransition (q ≫ p) r F ≫ sheafApproximationTransition q p F =
      sheafApproximationTransition q (p ≫ r) F := by
  let R := actualSheafPushforward q
  let P := actualSheafPushforward p
  let Q := actualSheafPushforward r
  let a := actualSheafAdjunction q
  let b : actualSheafPullback (q ≫ p) ⊣ R ⋙ P :=
    actualSheafAdjunction (q ≫ p)
  let c : actualSheafPullback ((q ≫ p) ≫ r) ⊣ R ⋙ P ⋙ Q :=
    actualSheafAdjunction ((q ≫ p) ≫ r)
  let B := (R ⋙ P).obj F
  let C := (R ⋙ P ⋙ Q).obj F
  let H := sheafApproximation q F
  let K := sheafApproximation (q ≫ p) F
  let v : B ⟶ (R ⋙ P).obj H := P.map (a.unit.app (R.obj F))
  let t : K ⟶ H := (b.homEquiv B H).symm v
  let u : C ⟶ (R ⋙ P ⋙ Q).obj K := Q.map (b.unit.app B)
  let w : C ⟶ (R ⋙ P ⋙ Q).obj H := Q.map v
  let st : (actualSheafPullback ((q ≫ p) ≫ r)).obj C ⟶ K :=
    (c.homEquiv C K).symm u
  let direct : (actualSheafPullback ((q ≫ p) ≫ r)).obj C ⟶ H :=
    (c.homEquiv C H).symm w
  have ht : b.homEquiv B H t = v := (b.homEquiv B H).apply_symm_apply v
  have hη : b.unit.app B ≫ (R ⋙ P).map t = v :=
    (b.homEquiv_unit B H t).symm.trans ht
  have hst : c.homEquiv C K st = u := (c.homEquiv C K).apply_symm_apply u
  have hd : c.homEquiv C H direct = w := (c.homEquiv C H).apply_symm_apply w
  change st ≫ t = direct
  apply (c.homEquiv C H).injective
  calc
    c.homEquiv C H (st ≫ t) = c.homEquiv C K st ≫ (R ⋙ P ⋙ Q).map t :=
      c.homEquiv_naturality_right st t
    _ = u ≫ (R ⋙ P ⋙ Q).map t :=
      congrArg (fun k : C ⟶ (R ⋙ P ⋙ Q).obj K => k ≫ (R ⋙ P ⋙ Q).map t) hst
    _ = w := by
      change Q.map (b.unit.app B) ≫ Q.map ((R ⋙ P).map t) = Q.map v
      exact (Q.map_comp _ _).symm.trans (congrArg Q.map hη)
    _ = c.homEquiv C H direct := hd.symm

end SchemeTheory
