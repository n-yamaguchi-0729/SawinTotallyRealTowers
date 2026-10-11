/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Topology.SheafPullbackStalks
import Mathlib.Topology.Sheaves.Stalks

/-!
# Germs and the actual inverse-image adjunction

The stalk comparison for the chosen sheaf pullback intertwines germs
with the unit of its actual pullback-pushforward adjunction.

The Lean proofs are original.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace SchemeTheory

variable {X Y : TopCat.{u}}

/-- Taking a germ after restriction along a continuous map is the same
as applying the canonical comparison to the original germ. -/
theorem germ_sheafStalkPullbackIso_hom (f : X ⟶ Y)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u))
    (x : X) (U : Opens Y) (hx : f x ∈ U) :
    TopCat.Presheaf.germ F.obj U (f x) hx ≫ (sheafStalkPullbackIso f F x).hom =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom.app
        (op U)) ≫
      TopCat.Presheaf.germ ((TopCat.Sheaf.pullback (Type u) f).obj F).obj
        ((Opens.map f).obj U) x hx := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let FP : Y.Presheaf (Type u) := F.obj
  let P : X.Presheaf (Type u) := (TopCat.Presheaf.pullback (Type u) f).obj FP
  let H : X.Presheaf (Type u) := CategoryTheory.sheafify JX P
  let LP : X.Presheaf (Type u) := ((TopCat.Sheaf.pullback (Type u) f).obj F).obj
  let V : Opens X := (Opens.map f).obj U
  let T : X.Presheaf (Type u) ⥤ Type u := TopCat.Presheaf.stalkFunctor (Type u) x
  let τ : P ⟶ H := CategoryTheory.toSheafify JX P
  let e : LP ≅ H := (sheafToPresheaf JX (Type u)).mapIso
    ((TopCat.Sheaf.pullbackIso (Type u) f).app F)
  let η : FP ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj LP :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom
  let ηP : FP ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj P :=
    (TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app FP
  let k : FP.stalk (f x) ⟶ P.stalk x :=
    TopCat.Presheaf.stalkPullbackHom (Type u) f FP x
  let gF : FP.obj (op U) ⟶ FP.stalk (f x) := FP.germ U (f x) hx
  let gP : P.obj (op V) ⟶ P.stalk x := P.germ V x hx
  let gH : H.obj (op V) ⟶ H.stalk x := H.germ V x hx
  let gL : LP.obj (op V) ⟶ LP.stalk x := LP.germ V x hx
  let mτ : P.stalk x ⟶ H.stalk x := T.map τ
  let mi : H.stalk x ⟶ LP.stalk x := T.map e.inv
  let a : FP.stalk (f x) ⟶ LP.stalk x := (sheafStalkPullbackIso f F x).hom
  let ηU : FP.obj (op U) ⟶ LP.obj (op V) := η.app (op U)
  let ηPU : FP.obj (op U) ⟶ P.obj (op V) := ηP.app (op U)
  let τU : P.obj (op V) ⟶ H.obj (op V) := τ.app (op V)
  let ehU : LP.obj (op V) ⟶ H.obj (op V) := e.hom.app (op V)
  let eiU : H.obj (op V) ⟶ LP.obj (op V) := e.inv.app (op V)
  have hk : a = k ≫ mτ ≫ mi := rfl
  have hraw : gF ≫ k = ηPU ≫ gP :=
    TopCat.Presheaf.germ_stalkPullbackHom (Type u) f FP x U hx
  have hτ : gP ≫ mτ = τU ≫ gH :=
    TopCat.Presheaf.stalkFunctor_map_germ V x hx τ
  have he : gH ≫ mi = eiU ≫ gL :=
    TopCat.Presheaf.stalkFunctor_map_germ V x hx e.inv
  have hu : ηU ≫ ehU = ηPU ≫ τU :=
    congrArg (fun a : FP ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj H =>
      a.app (op U)) (sheafPullback_unit_comparison f F)
  have hei : ehU ≫ eiU = 𝟙 (LP.obj (op V)) := e.hom_inv_id_app (op V)
  have hτe : gP ≫ mτ ≫ mi = τU ≫ eiU ≫ gL := by
    rw [← Category.assoc, hτ, Category.assoc, he]
  change gF ≫ a = ηU ≫ gL
  calc
    gF ≫ a = (gF ≫ k) ≫ mτ ≫ mi := by rw [hk, Category.assoc]
    _ = ηPU ≫ (gP ≫ mτ ≫ mi) := by
      rw [hraw, Category.assoc]
    _ = (ηPU ≫ τU) ≫ eiU ≫ gL := by
      rw [hτe, Category.assoc]
    _ = (ηU ≫ ehU) ≫ eiU ≫ gL := by
      rw [← hu]
    _ = ηU ≫ gL := by
      rw [Category.assoc, ← Category.assoc ehU eiU gL, hei, Category.id_comp]

end SchemeTheory
