/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.Sheaves.Stalks
import Nyll.SchemeTheory.Topology.ClosedDiscreteSheaf
import Nyll.SchemeTheory.Topology.ClosedDiscreteStalkOutside
import Nyll.SchemeTheory.Topology.SheafPullbackGerms
import Nyll.SchemeTheory.Topology.SheafPullbackStalks

/-!
# Pullback of a skyscraper as discrete functions on its closed support

For an arbitrary continuous map, the inverse image of a skyscraper is
the direct image of discrete-valued continuous functions on the inverse
image of its closed support. The comparison is the actual adjoint of the
constant-section map. Its stalks are identified on the support by germ
evaluation, and both stalks are terminal away from the support.

This supplies the finite-stage closed-support comparison used in the
topological proof of Stacks Project, tag 09ZG.
Reference: https://stacks.math.columbia.edu/tag/09ZG.
The Lean constructions and proofs are original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopCat TopologicalSpace Topology Opposite

namespace SchemeTheory

attribute [local instance] Classical.propDecidable

variable {X Y : TopCat.{u}}

private def skyscraperClosedSupportSection (q : X ⟶ Y) (y : Y) (A : Type u)
    (U : Opens Y) (s : (skyscraperPresheaf y A).obj (op U)) :
    TopCat.of {z : (q ⁻¹' closure ({y} : Set Y) : Set X) // q z.1 ∈ U} ⟶
      TopCat.discrete.obj A := by
  let P : Y.Presheaf (Type u) := skyscraperPresheaf y A
  let D : TopCat.{u} :=
    TopCat.of {z : (q ⁻¹' closure ({y} : Set Y) : Set X) // q z.1 ∈ U}
  let ev : P.stalk y ⟶ A :=
    (skyscraperPresheafStalkOfSpecializes y A specializes_rfl).hom
  have hy (z : D) : y ∈ U :=
    (specializes_iff_mem_closure.mpr z.1.2).mem_open U.isOpen z.2
  let v : D → TopCat.discrete.obj A := fun z => ev (P.germ U y (hy z) s)
  have hv : Continuous v := continuous_of_const (fun _ _ => rfl)
  exact (TopCat.Hom.equivContinuousMap D (TopCat.discrete.obj A)).symm ⟨v, hv⟩

/-- The actual constant-section morphism from the skyscraper to the direct
image of discrete functions on the inverse image of its closed support. -/
def skyscraperToClosedDiscretePushforward (q : X ⟶ Y) (y : Y) (A : Type u) :
    skyscraperSheaf y A ⟶ (TopCat.Sheaf.pushforward (Type u) q).obj
      (closedDiscreteSheaf (q ⁻¹' closure ({y} : Set Y) : Set X) A) :=
  ⟨{ app := fun U => TypeCat.ofHom (skyscraperClosedSupportSection q y A U.unop)
     naturality := fun U V h => by
       let P : Y.Presheaf (Type u) := skyscraperPresheaf y A
       let ev : P.stalk y ⟶ A :=
         (skyscraperPresheafStalkOfSpecializes y A specializes_rfl).hom
       apply ConcreteCategory.hom_ext
       intro s
       apply TopCat.hom_ext
       apply ContinuousMap.ext
       intro z
       have hyV : y ∈ V.unop :=
         (specializes_iff_mem_closure.mpr z.1.2).mem_open V.unop.isOpen z.2
       change ev (P.germ V.unop y hyV (P.map h s)) =
         ev (P.germ U.unop y (h.unop.le hyV) s)
       exact congrArg ev (P.germ_res_apply' h y hyV s) }⟩

/-- The actual inverse-image adjoint of the constant-section morphism. -/
def pullbackSkyscraperToClosedDiscrete (q : X ⟶ Y) (y : Y) (A : Type u) :
    (TopCat.Sheaf.pullback (Type u) q).obj (skyscraperSheaf y A) ⟶
      closedDiscreteSheaf (q ⁻¹' closure ({y} : Set Y) : Set X) A :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) q).homEquiv _ _).symm
    (skyscraperToClosedDiscretePushforward q y A)

/-- On the closed support, the comparison carries the actual inverse-image
germ to the same value in the skyscraper fiber. -/
theorem pullbackSkyscraperToClosedDiscrete_stalk_onSupport
    (q : X ⟶ Y) (y : Y) (A : Type u)
    (x : (q ⁻¹' closure ({y} : Set Y) : Set X)) :
    (sheafStalkPullbackIso q (skyscraperSheaf y A) x.1).hom ≫
        (TopCat.Presheaf.stalkFunctor (Type u) x.1).map
          (pullbackSkyscraperToClosedDiscrete q y A).hom ≫
        (closedDiscreteStalkIso (q ⁻¹' closure ({y} : Set Y) : Set X) A x).hom =
      (skyscraperPresheafStalkOfSpecializes y A
        (specializes_iff_mem_closure.mpr x.2)).hom := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let L : CategoryTheory.Sheaf JY (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    TopCat.Sheaf.pullback (Type u) q
  let R : CategoryTheory.Sheaf JX (Type u) ⥤ CategoryTheory.Sheaf JY (Type u) :=
    TopCat.Sheaf.pushforward (Type u) q
  let adj : L ⊣ R := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) q
  let F : CategoryTheory.Sheaf JY (Type u) := skyscraperSheaf y A
  let C : Set X := q ⁻¹' closure ({y} : Set Y)
  let G : CategoryTheory.Sheaf JX (Type u) := closedDiscreteSheaf C A
  let P : Y.Presheaf (Type u) := F.obj
  let Q : X.Presheaf (Type u) := G.obj
  let H : X.Presheaf (Type u) := (L.obj F).obj
  let r : F ⟶ R.obj G := skyscraperToClosedDiscretePushforward q y A
  let δ : L.obj F ⟶ G := pullbackSkyscraperToClosedDiscrete q y A
  let η : P ⟶ (TopCat.Presheaf.pushforward (Type u) q).obj H := (adj.unit.app F).hom
  let e : P.stalk (q x.1) ≅ H.stalk x.1 := sheafStalkPullbackIso q F x.1
  let m : H.stalk x.1 ⟶ Q.stalk x.1 :=
    (TopCat.Presheaf.stalkFunctor (Type u) x.1).map δ.hom
  have hxy : y ⤳ q x.1 := specializes_iff_mem_closure.mpr x.2
  let evP : P.stalk (q x.1) ⟶ A :=
    (skyscraperPresheafStalkOfSpecializes y A hxy).hom
  let evY : P.stalk y ⟶ A :=
    (skyscraperPresheafStalkOfSpecializes y A specializes_rfl).hom
  let evQ : Q.stalk x.1 ⟶ A := (closedDiscreteStalkIso C A x).hom
  have hAdj : adj.unit.app F ≫ R.map δ = r :=
    (adj.homEquiv_unit F G δ).symm.trans ((adj.homEquiv F G).apply_symm_apply r)
  change e.hom ≫ m ≫ evQ = evP
  apply P.stalk_hom_ext
  intro U hx
  let V : Opens X := (Opens.map q).obj U
  have hxV : x.1 ∈ V := hx
  have hy : y ∈ U := hxy.mem_open U.isOpen hx
  let gP : P.obj (op U) ⟶ P.stalk (q x.1) := P.germ U (q x.1) hx
  let gY : P.obj (op U) ⟶ P.stalk y := P.germ U y hy
  let gH : H.obj (op V) ⟶ H.stalk x.1 := H.germ V x.1 hxV
  let gQ : Q.obj (op V) ⟶ Q.stalk x.1 := Q.germ V x.1 hxV
  let ηU : P.obj (op U) ⟶ H.obj (op V) := η.app (op U)
  let δV : H.obj (op V) ⟶ Q.obj (op V) := δ.hom.app (op V)
  let rU : P.obj (op U) ⟶ Q.obj (op V) := r.hom.app (op U)
  have he : gP ≫ e.hom = ηU ≫ gH := germ_sheafStalkPullbackIso_hom q F x.1 U hx
  have hm : gH ≫ m = δV ≫ gQ :=
    TopCat.Presheaf.stalkFunctor_map_germ V x.1 hxV δ.hom
  have hr : ηU ≫ δV = rU :=
    congrArg (fun k : F ⟶ R.obj G => k.hom.app (op U)) hAdj
  have hgm : (gP ≫ e.hom) ≫ m = rU ≫ gQ := by
    calc
      (gP ≫ e.hom) ≫ m = (ηU ≫ gH) ≫ m :=
        congrArg (fun k : P.obj (op U) ⟶ H.stalk x.1 => k ≫ m) he
      _ = ηU ≫ (gH ≫ m) := Category.assoc ηU gH m
      _ = ηU ≫ (δV ≫ gQ) :=
        congrArg (fun k : H.obj (op V) ⟶ Q.stalk x.1 => ηU ≫ k) hm
      _ = (ηU ≫ δV) ≫ gQ := (Category.assoc ηU δV gQ).symm
      _ = rU ≫ gQ :=
        congrArg (fun k : P.obj (op U) ⟶ Q.obj (op V) => k ≫ gQ) hr
  have hcomp : gP ≫ (e.hom ≫ m ≫ evQ) = rU ≫ gQ ≫ evQ := by
    calc
      gP ≫ (e.hom ≫ m ≫ evQ) = ((gP ≫ e.hom) ≫ m) ≫ evQ := by
        simp only [Category.assoc]
      _ = (rU ≫ gQ) ≫ evQ :=
        congrArg (fun k : P.obj (op U) ⟶ Q.stalk x.1 => k ≫ evQ) hgm
      _ = rU ≫ gQ ≫ evQ := Category.assoc rU gQ evQ
  have hSky : gY ≫ evY = gP ≫ evP := by
    exact (germ_skyscraperPresheafStalkOfSpecializes_hom y A specializes_rfl U hy).trans
      (germ_skyscraperPresheafStalkOfSpecializes_hom y A hxy U hx).symm
  change gP ≫ (e.hom ≫ m ≫ evQ) = gP ≫ evP
  apply hcomp.trans
  apply ConcreteCategory.hom_ext
  intro s
  let sQ : TopCat.of {z : C // z.1 ∈ V} ⟶ TopCat.discrete.obj A := rU s
  have hQ : evQ (gQ (rU s)) = sQ ⟨x, hxV⟩ :=
    closedDiscreteStalkIso_germ C A x V hxV (rU s)
  have hValue : sQ ⟨x, hxV⟩ = evY (gY s) := rfl
  have hSkyValue : evY (gY s) = evP (gP s) :=
    congrArg (fun k : P.obj (op U) ⟶ A => k s) hSky
  exact hQ.trans (hValue.trans hSkyValue)

/-- Every stalk of the actual comparison is an isomorphism. -/
theorem pullbackSkyscraperToClosedDiscrete_stalk_isIso
    (q : X ⟶ Y) (y : Y) (A : Type u) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map
      (pullbackSkyscraperToClosedDiscrete q y A).hom) := by
  let C : Set X := q ⁻¹' closure ({y} : Set Y)
  let F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u) :=
    skyscraperSheaf y A
  let H : X.Presheaf (Type u) := ((TopCat.Sheaf.pullback (Type u) q).obj F).obj
  let Q : X.Presheaf (Type u) := (closedDiscreteSheaf C A).obj
  let e : TopCat.Presheaf.stalk F.obj (q x) ≅ H.stalk x :=
    sheafStalkPullbackIso q F x
  let m : H.stalk x ⟶ Q.stalk x :=
    (TopCat.Presheaf.stalkFunctor (Type u) x).map
      (pullbackSkyscraperToClosedDiscrete q y A).hom
  change IsIso m
  by_cases hx : x ∈ C
  · let a : Q.stalk x ≅ A := closedDiscreteStalkIso C A ⟨x, hx⟩
    let b : TopCat.Presheaf.stalk F.obj (q x) ≅ A :=
      skyscraperPresheafStalkOfSpecializes y A (specializes_iff_mem_closure.mpr hx)
    have heq : e.hom ≫ m ≫ a.hom = b.hom :=
      pullbackSkyscraperToClosedDiscrete_stalk_onSupport q y A ⟨x, hx⟩
    have hi : IsIso (e.hom ≫ m ≫ a.hom) := heq.symm ▸ b.isIso_hom
    exact (isIso_comp_right_iff m a.hom).mp
      ((isIso_comp_left_iff e.hom (m ≫ a.hom)).mp hi)
  · have hxy : ¬ y ⤳ q x := fun h => hx (specializes_iff_mem_closure.mp h)
    have hSource : IsTerminal (H.stalk x) :=
      (skyscraperPresheafStalkOfNotSpecializesIsTerminal y A hxy).ofIso e
    have hC : IsClosed C := isClosed_closure.preimage q.hom.continuous
    have hTarget : IsTerminal (Q.stalk x) :=
      closedDiscreteStalkIsTerminal C hC A x hx
    exact isIso_of_isTerminal hSource hTarget m

/-- The inverse image of an actual skyscraper is the direct image of the
discrete-function sheaf on the inverse image of its closed support. -/
def pullbackSkyscraperClosedDiscreteIso (q : X ⟶ Y) (y : Y) (A : Type u) :
    (TopCat.Sheaf.pullback (Type u) q).obj (skyscraperSheaf y A) ≅
      closedDiscreteSheaf (q ⁻¹' closure ({y} : Set Y) : Set X) A := by
  let δ : (TopCat.Sheaf.pullback (Type u) q).obj (skyscraperSheaf y A) ⟶
      closedDiscreteSheaf (q ⁻¹' closure ({y} : Set Y) : Set X) A :=
    pullbackSkyscraperToClosedDiscrete q y A
  have hδ : IsIso δ := (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso δ).mpr
    (pullbackSkyscraperToClosedDiscrete_stalk_isIso q y A)
  exact asIso δ

end SchemeTheory
