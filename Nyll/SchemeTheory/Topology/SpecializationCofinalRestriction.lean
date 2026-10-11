/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Topology.SheafPullbackGerms
import Nyll.SchemeTheory.Topology.SpecializationCofinalSections
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.Stalks

/-!
# Restriction to a specialization-cofinal image

For a continuous map whose image contains a specialization of every
point, global restriction through the actual inverse-image adjunction
is injective. Surjectivity of this restriction passes to subsheaves.
In particular these statements apply to the closed inclusions in the
subsheaf reduction of Stacks Project, tag 09ZG.

Reference: https://stacks.math.columbia.edu/tag/09ZG.
The Lean proofs are original.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite

namespace SchemeTheory

variable {X Y : TopCat.{u}}

/-- Naturality of the actual inverse-image stalk comparison. -/
theorem sheafStalkPullbackIso_hom_naturality (f : X ⟶ Y)
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u)}
    (m : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor (Type u) (f x)).map m.hom ≫
        (sheafStalkPullbackIso f G x).hom =
      (sheafStalkPullbackIso f F x).hom ≫
        (TopCat.Presheaf.stalkFunctor (Type u) x).map
          ((TopCat.Sheaf.pullback (Type u) f).map m).hom := by
  let FP : Y.Presheaf (Type u) := F.obj
  let GP : Y.Presheaf (Type u) := G.obj
  let FQ : X.Presheaf (Type u) := ((TopCat.Sheaf.pullback (Type u) f).obj F).obj
  let GQ : X.Presheaf (Type u) := ((TopCat.Sheaf.pullback (Type u) f).obj G).obj
  let mQ : FQ ⟶ GQ := ((TopCat.Sheaf.pullback (Type u) f).map m).hom
  let ηF : FP ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj FQ :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom
  let ηG : GP ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj GQ :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app G).hom
  let TY : Y.Presheaf (Type u) ⥤ Type u :=
    TopCat.Presheaf.stalkFunctor (Type u) (f x)
  let TX : X.Presheaf (Type u) ⥤ Type u := TopCat.Presheaf.stalkFunctor (Type u) x
  let eF : FP.stalk (f x) ≅ FQ.stalk x := sheafStalkPullbackIso f F x
  let eG : GP.stalk (f x) ≅ GQ.stalk x := sheafStalkPullbackIso f G x
  let mY : FP.stalk (f x) ⟶ GP.stalk (f x) := TY.map m.hom
  let mX : FQ.stalk x ⟶ GQ.stalk x := TX.map mQ
  have hn : m.hom ≫ ηG = ηF ≫ (TopCat.Presheaf.pushforward (Type u) f).map mQ :=
    congrArg (fun a : F ⟶ (TopCat.Sheaf.pushforward (Type u) f).obj
      ((TopCat.Sheaf.pullback (Type u) f).obj G) => a.hom)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.naturality m)
  change mY ≫ eG.hom = eF.hom ≫ mX
  apply FP.stalk_hom_ext
  intro U hx
  let V : Opens X := (Opens.map f).obj U
  let gF : FP.obj (op U) ⟶ FP.stalk (f x) := FP.germ U (f x) hx
  let gG : GP.obj (op U) ⟶ GP.stalk (f x) := GP.germ U (f x) hx
  let gFQ : FQ.obj (op V) ⟶ FQ.stalk x := FQ.germ V x hx
  let gGQ : GQ.obj (op V) ⟶ GQ.stalk x := GQ.germ V x hx
  let mU : FP.obj (op U) ⟶ GP.obj (op U) := m.hom.app (op U)
  let mQV : FQ.obj (op V) ⟶ GQ.obj (op V) := mQ.app (op V)
  let ηFU : FP.obj (op U) ⟶ FQ.obj (op V) := ηF.app (op U)
  let ηGU : GP.obj (op U) ⟶ GQ.obj (op V) := ηG.app (op U)
  have hm : gF ≫ mY = mU ≫ gG :=
    TopCat.Presheaf.stalkFunctor_map_germ U (f x) hx m.hom
  have hmQ : gFQ ≫ mX = mQV ≫ gGQ :=
    TopCat.Presheaf.stalkFunctor_map_germ V x hx mQ
  have hgF : gF ≫ eF.hom = ηFU ≫ gFQ :=
    germ_sheafStalkPullbackIso_hom f F x U hx
  have hgG : gG ≫ eG.hom = ηGU ≫ gGQ :=
    germ_sheafStalkPullbackIso_hom f G x U hx
  have hnU : mU ≫ ηGU = ηFU ≫ mQV :=
    congrArg (fun a : FP ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj GQ =>
      a.app (op U)) hn
  change gF ≫ (mY ≫ eG.hom) = gF ≫ (eF.hom ≫ mX)
  calc
    gF ≫ (mY ≫ eG.hom) = mU ≫ gG ≫ eG.hom := by
      rw [← Category.assoc, hm, Category.assoc]
    _ = mU ≫ ηGU ≫ gGQ := by rw [hgG]
    _ = ηFU ≫ mQV ≫ gGQ := by
      rw [← Category.assoc, hnU, Category.assoc]
    _ = ηFU ≫ gFQ ≫ mX := by rw [← hmQ]
    _ = gF ≫ (eF.hom ≫ mX) := by
      rw [← Category.assoc, ← hgF, Category.assoc]

/-- A specialization-cofinal image detects global sections through the
unit of the actual inverse-image adjunction. -/
theorem sheafPullback_globalSections_injective (f : X ⟶ Y)
    (hf : ∀ y : Y, ∃ x : X, y ⤳ f x)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u)) :
    Function.Injective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom.app
        (op (⊤ : Opens Y))) := by
  intro s t hst
  have hcofinal : ∀ y : Y, ∃ z ∈ Set.range f, y ⤳ z := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨f x, ⟨x, rfl⟩, hx⟩
  apply globalSection_eq_of_germs_on_specialization_cofinal hcofinal F s t
  intro z hz
  obtain ⟨x, rfl⟩ := hz
  let FP : Y.Presheaf (Type u) := F.obj
  let FQ : X.Presheaf (Type u) := ((TopCat.Sheaf.pullback (Type u) f).obj F).obj
  let V : Opens X := (Opens.map f).obj ⊤
  let e : FP.stalk (f x) ≅ FQ.stalk x := sheafStalkPullbackIso f F x
  apply e.toEquiv.injective
  have hg := germ_sheafStalkPullbackIso_hom f F x ⊤ trivial
  have hs := congrArg (fun a : FP.obj (op (⊤ : Opens Y)) ⟶ FQ.stalk x => a s) hg
  have ht := congrArg (fun a : FP.obj (op (⊤ : Opens Y)) ⟶ FQ.stalk x => a t) hg
  exact hs.trans ((congrArg (FQ.germ V x trivial) hst).trans ht.symm)

/-- Surjectivity of global restriction passes from a sheaf to a subsheaf
when the image of the continuous map is specialization-cofinal. -/
theorem sheafPullback_globalSections_surjective_of_mono (f : X ⟶ Y)
    (hf : ∀ y : Y, ∃ x : X, y ⤳ f x)
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u)}
    (m : F ⟶ G) [Mono m]
    (hG : Function.Surjective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app G).hom.app
        (op (⊤ : Opens Y)))) :
    Function.Surjective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom.app
        (op (⊤ : Opens Y))) := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let L : CategoryTheory.Sheaf JY (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    (Opens.map f).sheafPullback (Type u) JY JX
  let FP : Y.Presheaf (Type u) := F.obj
  let GP : Y.Presheaf (Type u) := G.obj
  let FQ : X.Presheaf (Type u) := (L.obj F).obj
  let GQ : X.Presheaf (Type u) := (L.obj G).obj
  let mQ : FQ ⟶ GQ := (L.map m).hom
  let V : Opens X := (Opens.map f).obj ⊤
  let ηF : FP ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj FQ :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom
  let ηG : GP ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj GQ :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app G).hom
  intro t
  obtain ⟨s, hs⟩ := hG (mQ.app (op V) t)
  have hcofinal : ∀ y : Y, ∃ z ∈ Set.range f, y ⤳ z := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨f x, ⟨x, rfl⟩, hx⟩
  have hlift : ∀ z ∈ Set.range f, ∃ a : FP.stalk z,
      (TopCat.Presheaf.stalkFunctor (Type u) z).map m.hom a =
        GP.germ ⊤ z trivial s := by
    intro z hz
    obtain ⟨x, rfl⟩ := hz
    let TY : Y.Presheaf (Type u) ⥤ Type u :=
      TopCat.Presheaf.stalkFunctor (Type u) (f x)
    let TX : X.Presheaf (Type u) ⥤ Type u := TopCat.Presheaf.stalkFunctor (Type u) x
    let eF : FP.stalk (f x) ≅ FQ.stalk x := sheafStalkPullbackIso f F x
    let eG : GP.stalk (f x) ≅ GQ.stalk x := sheafStalkPullbackIso f G x
    let mY : FP.stalk (f x) ⟶ GP.stalk (f x) := TY.map m.hom
    let mX : FQ.stalk x ⟶ GQ.stalk x := TX.map mQ
    let a : FP.stalk (f x) := eF.inv (FQ.germ V x trivial t)
    refine ⟨a, ?_⟩
    apply eG.toEquiv.injective
    have hn : eG.hom (mY a) = mX (eF.hom a) :=
      congrArg (fun k : FP.stalk (f x) ⟶ GQ.stalk x => k a)
        (sheafStalkPullbackIso_hom_naturality f m x)
    have ha : eF.hom a = FQ.germ V x trivial t := eF.toEquiv.apply_symm_apply _
    have hg : eG.hom (GP.germ ⊤ (f x) trivial s) =
        GQ.germ V x trivial (ηG.app (op ⊤) s) :=
      congrArg (fun k : GP.obj (op (⊤ : Opens Y)) ⟶ GQ.stalk x => k s)
        (germ_sheafStalkPullbackIso_hom f G x ⊤ trivial)
    calc
      eG.hom (mY a) = mX (eF.hom a) := hn
      _ = mX (FQ.germ V x trivial t) := congrArg mX ha
      _ = GQ.germ V x trivial (mQ.app (op V) t) :=
        TopCat.Presheaf.stalkFunctor_map_germ_apply V x trivial mQ t
      _ = GQ.germ V x trivial (ηG.app (op ⊤) s) :=
        congrArg (GQ.germ V x trivial) hs.symm
      _ = eG.hom (GP.germ ⊤ (f x) trivial s) := hg.symm
  obtain ⟨r, hr⟩ := exists_globalSection_lift_of_germs_on_specialization_cofinal
    hcofinal m s hlift
  refine ⟨r, ?_⟩
  have hReflects : ReflectsLimits (CategoryTheory.forget (Type u)) :=
    reflectsLimits_of_reflectsIsomorphisms
  have hLan : PreservesFiniteLimits
      ((Opens.map f).op.lan : ((Opens Y)ᵒᵖ ⥤ Type u) ⥤ (Opens X)ᵒᵖ ⥤ Type u) :=
    lan_preservesFiniteLimits_of_flat (E := Type u) (Opens.map f)
  have hL : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f) (Type u) JY JX
  have hmL : Mono (L.map m) := preserves_mono_of_preservesLimit L m
  have hmQ : Mono mQ := (sheafToPresheaf JX (Type u)).map_mono (L.map m)
  have hmV : Mono (mQ.app (op V)) := (NatTrans.mono_iff_mono_app mQ).mp hmQ _
  apply (CategoryTheory.mono_iff_injective (mQ.app (op V))).mp hmV
  have hn : m.hom ≫ ηG = ηF ≫ (TopCat.Presheaf.pushforward (Type u) f).map mQ :=
    congrArg (fun a : F ⟶ (TopCat.Sheaf.pushforward (Type u) f).obj (L.obj G) => a.hom)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.naturality m)
  have hnr : ηG.app (op ⊤) (m.hom.app (op ⊤) r) =
      mQ.app (op V) (ηF.app (op ⊤) r) :=
    congrArg (fun a : FP ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj GQ =>
      a.app (op ⊤) r) hn
  exact hnr.symm.trans ((congrArg (ηG.app (op ⊤)) hr).trans hs)

end SchemeTheory
