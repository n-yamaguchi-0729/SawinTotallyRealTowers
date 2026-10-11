/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Topology.FiniteModelSheafTransitions
import Nyll.SchemeTheory.Topology.SheafPullbackGerms
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks

/-!
# Germs of actual sheaf approximation maps

The inverse-image stalk comparison identifies approximation counits
with direct-image stalk maps. Refinement acts on germs by restriction
between inverse images of open neighborhoods. Taking the neighborhoods
to be principal opens gives the stalk calculation for finite models.

The Lean proofs are original.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace SchemeTheory

variable {X Y Z : TopCat.{u}}

/-- Under the actual inverse-image stalk comparison, the counit is the
usual morphism from a direct-image stalk. -/
theorem sheafStalkPullbackIso_hom_counit (q : X ⟶ Y)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) (x : X) :
    (sheafStalkPullbackIso q ((TopCat.Sheaf.pushforward (Type u) q).obj F) x).hom ≫
        (TopCat.Presheaf.stalkFunctor (Type u) x).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) q).counit.app F).hom =
      TopCat.Presheaf.stalkPushforward (Type u) q F.obj x := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let L : CategoryTheory.Sheaf JY (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    TopCat.Sheaf.pullback (Type u) q
  let R : CategoryTheory.Sheaf JX (Type u) ⥤ CategoryTheory.Sheaf JY (Type u) :=
    TopCat.Sheaf.pushforward (Type u) q
  let a : L ⊣ R := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) q
  let G : CategoryTheory.Sheaf JY (Type u) := R.obj F
  let FP : X.Presheaf (Type u) := F.obj
  let GP : Y.Presheaf (Type u) := G.obj
  let AP : X.Presheaf (Type u) := (L.obj G).obj
  let ε : AP ⟶ FP := (a.counit.app F).hom
  let η : GP ⟶ (TopCat.Presheaf.pushforward (Type u) q).obj AP :=
    (a.unit.app G).hom
  let T : X.Presheaf (Type u) ⥤ Type u := TopCat.Presheaf.stalkFunctor (Type u) x
  let e : GP.stalk (q x) ≅ AP.stalk x := sheafStalkPullbackIso q G x
  let mε : AP.stalk x ⟶ FP.stalk x := T.map ε
  let c : GP.stalk (q x) ⟶ FP.stalk x := FP.stalkPushforward (Type u) q x
  have htri : η ≫ (TopCat.Presheaf.pushforward (Type u) q).map ε = 𝟙 GP :=
    congrArg (fun k : G ⟶ G => k.hom) (a.right_triangle_components F)
  change e.hom ≫ mε = c
  apply GP.stalk_hom_ext
  intro U hx
  let V : Opens X := (Opens.map q).obj U
  let gG : FP.obj (op V) ⟶ GP.stalk (q x) := GP.germ U (q x) hx
  let gA : AP.obj (op V) ⟶ AP.stalk x := AP.germ V x hx
  let gF : FP.obj (op V) ⟶ FP.stalk x := FP.germ V x hx
  let ηU : FP.obj (op V) ⟶ AP.obj (op V) := η.app (op U)
  let εV : AP.obj (op V) ⟶ FP.obj (op V) := ε.app (op V)
  have hg : gG ≫ e.hom = ηU ≫ gA := germ_sheafStalkPullbackIso_hom q G x U hx
  have hε : gA ≫ mε = εV ≫ gF :=
    TopCat.Presheaf.stalkFunctor_map_germ V x hx ε
  have htriU : ηU ≫ εV = 𝟙 (FP.obj (op V)) :=
    congrArg (fun k : GP ⟶ GP => k.app (op U)) htri
  have hpush : gG ≫ c = gF :=
    TopCat.Presheaf.stalkPushforward_germ (Type u) q FP U x hx
  change gG ≫ (e.hom ≫ mε) = gG ≫ c
  calc
    gG ≫ (e.hom ≫ mε) = ηU ≫ gA ≫ mε := by
      rw [← Category.assoc, hg, Category.assoc]
    _ = ηU ≫ εV ≫ gF := by rw [hε]
    _ = gF := by rw [← Category.assoc, htriU, Category.id_comp]
    _ = gG ≫ c := hpush.symm

/-- The approximation transition is the adjoint of the direct image
of the finer unit. -/
theorem sheafApproximationTransition_unit (q : X ⟶ Y) (p : Y ⟶ Z)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (q ≫ p)).unit.app
        ((TopCat.Sheaf.pushforward (Type u) (q ≫ p)).obj F) ≫
        (TopCat.Sheaf.pushforward (Type u) (q ≫ p)).map
          (sheafApproximationTransition q p F) =
      (TopCat.Sheaf.pushforward (Type u) p).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) q).unit.app
          ((TopCat.Sheaf.pushforward (Type u) q).obj F)) := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let JZ : GrothendieckTopology (Opens Z) := Opens.grothendieckTopology Z
  let L : CategoryTheory.Sheaf JY (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    TopCat.Sheaf.pullback (Type u) q
  let R : CategoryTheory.Sheaf JX (Type u) ⥤ CategoryTheory.Sheaf JY (Type u) :=
    TopCat.Sheaf.pushforward (Type u) q
  let P : CategoryTheory.Sheaf JY (Type u) ⥤ CategoryTheory.Sheaf JZ (Type u) :=
    TopCat.Sheaf.pushforward (Type u) p
  let L' : CategoryTheory.Sheaf JZ (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    TopCat.Sheaf.pullback (Type u) (q ≫ p)
  let a : L ⊣ R := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) q
  let b : L' ⊣ R ⋙ P := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (q ≫ p)
  let B : CategoryTheory.Sheaf JZ (Type u) := P.obj (R.obj F)
  let H : CategoryTheory.Sheaf JX (Type u) := L.obj (R.obj F)
  let v : B ⟶ (R ⋙ P).obj H := P.map (a.unit.app (R.obj F))
  let t : L'.obj B ⟶ H := sheafApproximationTransition q p F
  have ht : b.homEquiv B H t = v := (b.homEquiv B H).apply_symm_apply v
  change b.unit.app B ≫ (R ⋙ P).map t = v
  exact (b.homEquiv_unit B H t).symm.trans ht

/-- On germs, refinement of an actual approximation is restriction
between the two inverse-image neighborhoods. -/
theorem sheafApproximationTransition_germ (q : X ⟶ Y) (p : Y ⟶ Z)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) (x : X)
    (U : Opens Z) (V : Opens Y) (i : V ⟶ (Opens.map p).obj U) (hx : q x ∈ V) :
    TopCat.Presheaf.germ ((TopCat.Sheaf.pushforward (Type u) (q ≫ p)).obj F).obj
        U ((q ≫ p) x) (i.le hx) ≫
        (sheafStalkPullbackIso (q ≫ p)
          ((TopCat.Sheaf.pushforward (Type u) (q ≫ p)).obj F) x).hom ≫
        (TopCat.Presheaf.stalkFunctor (Type u) x).map
          (sheafApproximationTransition q p F).hom =
      ((TopCat.Sheaf.pushforward (Type u) q).obj F).obj.map i.op ≫
        TopCat.Presheaf.germ ((TopCat.Sheaf.pushforward (Type u) q).obj F).obj
          V (q x) hx ≫
        (sheafStalkPullbackIso q ((TopCat.Sheaf.pushforward (Type u) q).obj F) x).hom := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let JZ : GrothendieckTopology (Opens Z) := Opens.grothendieckTopology Z
  let G : CategoryTheory.Sheaf JY (Type u) := (TopCat.Sheaf.pushforward (Type u) q).obj F
  let H : CategoryTheory.Sheaf JZ (Type u) :=
    (TopCat.Sheaf.pushforward (Type u) (q ≫ p)).obj F
  let A : CategoryTheory.Sheaf JX (Type u) := sheafApproximation (q ≫ p) F
  let B : CategoryTheory.Sheaf JX (Type u) := sheafApproximation q F
  let GP : Y.Presheaf (Type u) := G.obj
  let HP : Z.Presheaf (Type u) := H.obj
  let AP : X.Presheaf (Type u) := A.obj
  let BP : X.Presheaf (Type u) := B.obj
  let V₀ : Opens Y := (Opens.map p).obj U
  let W : Opens X := (Opens.map (q ≫ p)).obj U
  let t : A ⟶ B := sheafApproximationTransition q p F
  let T : X.Presheaf (Type u) ⥤ Type u := TopCat.Presheaf.stalkFunctor (Type u) x
  let mt : AP.stalk x ⟶ BP.stalk x := T.map t.hom
  let eA : HP.stalk ((q ≫ p) x) ≅ AP.stalk x := sheafStalkPullbackIso (q ≫ p) H x
  let eB : GP.stalk (q x) ≅ BP.stalk x := sheafStalkPullbackIso q G x
  let gH : HP.obj (op U) ⟶ HP.stalk ((q ≫ p) x) := HP.germ U ((q ≫ p) x) (i.le hx)
  let gG₀ : HP.obj (op U) ⟶ GP.stalk (q x) := GP.germ V₀ (q x) (i.le hx)
  let gG : GP.obj (op V) ⟶ GP.stalk (q x) := GP.germ V (q x) hx
  let gA : AP.obj (op W) ⟶ AP.stalk x := AP.germ W x (i.le hx)
  let gB : BP.obj (op W) ⟶ BP.stalk x := BP.germ W x (i.le hx)
  let r : HP.obj (op U) ⟶ GP.obj (op V) := GP.map i.op
  let tW : AP.obj (op W) ⟶ BP.obj (op W) := t.hom.app (op W)
  let uA : HP.obj (op U) ⟶ AP.obj (op W) :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (q ≫ p)).unit.app H).hom.app
      (op U)
  let uB : HP.obj (op U) ⟶ BP.obj (op W) :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) q).unit.app G).hom.app (op V₀)
  have hgA : gH ≫ eA.hom = uA ≫ gA :=
    germ_sheafStalkPullbackIso_hom (q ≫ p) H x U (i.le hx)
  have hgB : gG₀ ≫ eB.hom = uB ≫ gB :=
    germ_sheafStalkPullbackIso_hom q G x V₀ (i.le hx)
  have ht : gA ≫ mt = tW ≫ gB :=
    TopCat.Presheaf.stalkFunctor_map_germ W x (i.le hx) t.hom
  have hu : uA ≫ tW = uB :=
    congrArg (fun k : H ⟶ (TopCat.Sheaf.pushforward (Type u) (q ≫ p)).obj B =>
      k.hom.app (op U)) (sheafApproximationTransition_unit q p F)
  have hr : r ≫ gG = gG₀ := GP.germ_res i (q x) hx
  change gH ≫ eA.hom ≫ mt = r ≫ gG ≫ eB.hom
  calc
    gH ≫ eA.hom ≫ mt = uA ≫ gA ≫ mt := by
      rw [← Category.assoc, hgA, Category.assoc]
    _ = uA ≫ tW ≫ gB := by rw [ht]
    _ = uB ≫ gB := by rw [← Category.assoc, hu]
    _ = gG₀ ≫ eB.hom := hgB.symm
    _ = r ≫ gG ≫ eB.hom := by rw [← hr, Category.assoc]

end SchemeTheory
