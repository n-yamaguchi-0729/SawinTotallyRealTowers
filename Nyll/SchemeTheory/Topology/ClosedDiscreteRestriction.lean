/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks
import Nyll.SchemeTheory.Topology.ClosedDiscreteSheaf
import Nyll.SchemeTheory.Topology.SheafPullbackGerms

/-!
# Actual restriction of discrete functions on a closed support

Precomposition restricts continuous functions on a support to its inverse
image. Its adjoint is a morphism from the actual sheaf pullback. At every
point of the support it agrees with the actual stalk evaluation maps.
These concrete maps supply the closed-support restriction square in the
proof of Stacks Project, tag 09ZG.

Reference: https://stacks.math.columbia.edu/tag/09ZG.
The Lean constructions and proofs are original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopCat TopologicalSpace Topology Opposite

namespace SchemeTheory

variable {X Y : TopCat.{u}}

private def supportOpenPreimageMap (f : X ⟶ Y) (C : Set Y) (U : Opens Y) :
    TopCat.of {x : (f ⁻¹' C : Set X) // f x.1 ∈ U} ⟶
      TopCat.of {y : C // y.1 ∈ U} :=
  TopCat.ofHom ⟨fun x => ⟨⟨f x.1.1, x.1.2⟩, x.2⟩,
    ((f.hom.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
      (fun x => x.1.2)).subtype_mk (fun x => x.2)⟩

/-- Restriction of supported continuous functions is a morphism of the
actual sheaves, with codomain the direct image from the inverse-image support. -/
def closedDiscreteRestriction (f : X ⟶ Y) (C : Set Y) (A : Type u) :
    closedDiscreteSheaf C A ⟶ (TopCat.Sheaf.pushforward (Type u) f).obj
      (closedDiscreteSheaf (f ⁻¹' C : Set X) A) :=
  ⟨{ app := fun U => TypeCat.ofHom
        (fun s => supportOpenPreimageMap f C U.unop ≫ s)
     naturality := fun U V h => by
       apply ConcreteCategory.hom_ext
       intro s
       apply TopCat.hom_ext
       apply ContinuousMap.ext
       intro x
       rfl }⟩

/-- The actual inverse-image adjoint of restriction of supported functions. -/
def closedDiscretePullbackMap (f : X ⟶ Y) (C : Set Y) (A : Type u) :
    (TopCat.Sheaf.pullback (Type u) f).obj (closedDiscreteSheaf C A) ⟶
      closedDiscreteSheaf (f ⁻¹' C : Set X) A :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv _ _).symm
    (closedDiscreteRestriction f C A)

/-- On the support the actual pullback comparison commutes with stalk
evaluation, so it identifies the same value in the discrete fiber. -/
theorem closedDiscretePullbackMap_stalk_onSupport
    (f : X ⟶ Y) (C : Set Y) (A : Type u) (x : (f ⁻¹' C : Set X)) :
    (sheafStalkPullbackIso f (closedDiscreteSheaf C A) x.1).hom ≫
        (TopCat.Presheaf.stalkFunctor (Type u) x.1).map
          (closedDiscretePullbackMap f C A).hom ≫
        (closedDiscreteStalkIso (f ⁻¹' C : Set X) A x).hom =
      (closedDiscreteStalkIso C A ⟨f x.1, x.2⟩).hom := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let L : CategoryTheory.Sheaf JY (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    TopCat.Sheaf.pullback (Type u) f
  let R : CategoryTheory.Sheaf JX (Type u) ⥤ CategoryTheory.Sheaf JY (Type u) :=
    TopCat.Sheaf.pushforward (Type u) f
  let adj : L ⊣ R := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f
  let F : CategoryTheory.Sheaf JY (Type u) := closedDiscreteSheaf C A
  let G : CategoryTheory.Sheaf JX (Type u) := closedDiscreteSheaf (f ⁻¹' C : Set X) A
  let P : Y.Presheaf (Type u) := F.obj
  let Q : X.Presheaf (Type u) := G.obj
  let H : X.Presheaf (Type u) := (L.obj F).obj
  let r : F ⟶ R.obj G := closedDiscreteRestriction f C A
  let δ : L.obj F ⟶ G := closedDiscretePullbackMap f C A
  let η : P ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj H := (adj.unit.app F).hom
  let e : P.stalk (f x.1) ≅ H.stalk x.1 := sheafStalkPullbackIso f F x.1
  let m : H.stalk x.1 ⟶ Q.stalk x.1 :=
    (TopCat.Presheaf.stalkFunctor (Type u) x.1).map δ.hom
  let evP : P.stalk (f x.1) ⟶ A := (closedDiscreteStalkIso C A ⟨f x.1, x.2⟩).hom
  let evQ : Q.stalk x.1 ⟶ A := (closedDiscreteStalkIso (f ⁻¹' C : Set X) A x).hom
  have hAdj : adj.unit.app F ≫ R.map δ = r :=
    (adj.homEquiv_unit F G δ).symm.trans ((adj.homEquiv F G).apply_symm_apply r)
  change e.hom ≫ m ≫ evQ = evP
  apply P.stalk_hom_ext
  intro U hx
  let V : Opens X := (Opens.map f).obj U
  have hxV : x.1 ∈ V := hx
  let gP : P.obj (op U) ⟶ P.stalk (f x.1) := P.germ U (f x.1) hx
  let gH : H.obj (op V) ⟶ H.stalk x.1 := H.germ V x.1 hxV
  let gQ : Q.obj (op V) ⟶ Q.stalk x.1 := Q.germ V x.1 hxV
  let ηU : P.obj (op U) ⟶ H.obj (op V) := η.app (op U)
  let δV : H.obj (op V) ⟶ Q.obj (op V) := δ.hom.app (op V)
  let rU : P.obj (op U) ⟶ Q.obj (op V) := r.hom.app (op U)
  have he : gP ≫ e.hom = ηU ≫ gH := germ_sheafStalkPullbackIso_hom f F x.1 U hx
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
  change gP ≫ (e.hom ≫ m ≫ evQ) = gP ≫ evP
  apply hcomp.trans
  apply ConcreteCategory.hom_ext
  intro s
  let sP : TopCat.of {y : C // y.1 ∈ U} ⟶ TopCat.discrete.obj A := s
  let sQ : TopCat.of {z : (f ⁻¹' C : Set X) // z.1 ∈ V} ⟶
      TopCat.discrete.obj A := rU s
  have hQ : evQ (gQ (rU s)) = sQ ⟨x, hxV⟩ :=
    closedDiscreteStalkIso_germ (f ⁻¹' C : Set X) A x V hxV (rU s)
  have hP : evP (gP s) = sP ⟨⟨f x.1, x.2⟩, hx⟩ :=
    closedDiscreteStalkIso_germ C A ⟨f x.1, x.2⟩ U hx s
  exact hQ.trans hP.symm

end SchemeTheory
