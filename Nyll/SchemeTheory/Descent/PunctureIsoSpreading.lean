/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.PunctureSectionSpreading
import Nyll.SchemeTheory.Descent.AffineTransitionHom
import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsoModels
import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsoDescent
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.Topology.Sheaves.Stalks

/-!
# Isomorphism spreading over a punctured neighborhood

A specified isomorphism of finite étale covers over the part of an actual
local spectrum lying in a retrocompact open descends to the intersection
with an actual open neighborhood. The original local isomorphism is retained
under the native pullback comparisons. This supplies the overlap comparison
needed to glue local extensions in Stacks Project, Lemma 58.21.6 (`0EY7`).
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryPunctureIso (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := instCategory X

local instance finiteEtaleHasPullbacksAlongPunctureIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongPunctureIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

private theorem pullbackComp_inv_coherence
    {L N M U : Scheme.{u}}
    (r : L ⟶ N) (t : N ⟶ M) (q : M ⟶ U)
    (p : L ⟶ M) (qn : N ⟶ U) (ql : L ⟶ U)
    (hp : p = r ≫ t) (hqn : qn = t ≫ q)
    (hql : ql = p ≫ q) (hql' : ql = r ≫ qn)
    (A : FiniteEtale U) :
    let E := MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) t q qn hqn
    let C := MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) r qn ql hql'
    let D := MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) r t p hp
    let F := MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) p q ql hql
    (pullback r).map (E.inv.app A) ≫ C.inv.app A =
      D.inv.app ((pullback q).obj A) ≫ F.inv.app A := by
  intro E C D F
  let f : A.left ⟶ U := A.hom
  let qt : Limits.pullback f q ⟶ M := Limits.pullback.snd f q
  let qtt : Limits.pullback qt t ⟶ N := Limits.pullback.snd qt t
  let qnA : Limits.pullback f qn ⟶ N := Limits.pullback.snd f qn
  let α : Limits.pullback qtt r ⟶ Limits.pullback qnA r :=
    ((pullback r).map (E.inv.app A)).left
  let β : Limits.pullback qnA r ⟶ Limits.pullback f ql := (C.inv.app A).left
  let δ : Limits.pullback qtt r ⟶ Limits.pullback qt p :=
    (D.inv.app ((pullback q).obj A)).left
  let ε : Limits.pullback qt p ⟶ Limits.pullback f ql := (F.inv.app A).left
  let v : Limits.pullback qt t ⟶ Limits.pullback f qn := (E.inv.app A).left
  have hα : α ≫ Limits.pullback.fst qnA r = Limits.pullback.fst qtt r ≫ v :=
    Limits.pullback.lift_fst _ _ _
  have hβ : β ≫ Limits.pullback.fst f ql =
      Limits.pullback.fst qnA r ≫ Limits.pullback.fst f qn :=
    pullbackComp_inv_app_left_fst r qn ql hql' A
  have hδ : δ ≫ Limits.pullback.fst qt p =
      Limits.pullback.fst qtt r ≫ Limits.pullback.fst qt t :=
    pullbackComp_inv_app_left_fst r t p hp ((pullback q).obj A)
  have hε : ε ≫ Limits.pullback.fst f ql =
      Limits.pullback.fst qt p ≫ Limits.pullback.fst f q :=
    pullbackComp_inv_app_left_fst p q ql hql A
  have hv : v ≫ Limits.pullback.fst f qn =
      Limits.pullback.fst qt t ≫ Limits.pullback.fst f q :=
    pullbackComp_inv_app_left_fst t q qn hqn A
  have hαs : α ≫ Limits.pullback.snd qnA r = Limits.pullback.snd qtt r :=
    MorphismProperty.Over.w ((pullback r).map (E.inv.app A))
  have hβs : β ≫ Limits.pullback.snd f ql = Limits.pullback.snd qnA r :=
    MorphismProperty.Over.w (C.inv.app A)
  have hδs : δ ≫ Limits.pullback.snd qt p = Limits.pullback.snd qtt r :=
    MorphismProperty.Over.w (D.inv.app ((pullback q).obj A))
  have hεs : ε ≫ Limits.pullback.snd f ql = Limits.pullback.snd qt p :=
    MorphismProperty.Over.w (F.inv.app A)
  apply MorphismProperty.Over.Hom.ext
  change α ≫ β = δ ≫ ε
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, hβ, ← Category.assoc, hα, Category.assoc, hv,
      Category.assoc, hε, ← Category.assoc δ, hδ, Category.assoc]
  · rw [Category.assoc, hβs, hαs, Category.assoc, hεs, hδs]

private theorem transport_recovered_iso
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (P : C ⥤ F) (Q : C ⥤ D) (R : C ⥤ E)
    (V : D ⥤ F) (W : D ⥤ E) (T : E ⥤ F)
    (e : P ≅ Q ⋙ V) (f : V ≅ W ⋙ T)
    (g : R ≅ Q ⋙ W) (h : P ≅ R ⋙ T)
    (hcomp : ∀ A : C, T.map (g.inv.app A) ≫ h.inv.app A =
      f.inv.app (Q.obj A) ≫ e.inv.app A)
    {A B : C} (a : P.obj A ≅ P.obj B)
    (b : (Q ⋙ W).obj A ≅ (Q ⋙ W).obj B)
    (hb : f.hom.app (Q.obj A) ≫ T.map b.hom =
      ((e.app A).symm ≪≫ a ≪≫ e.app B).hom ≫ f.hom.app (Q.obj B)) :
    h.hom.app A ≫ T.map ((g.app A ≪≫ b ≪≫ (g.app B).symm).hom) =
      a.hom ≫ h.hom.app B := by
  have hb' : T.map b.hom ≫ f.inv.app (Q.obj B) =
      f.inv.app (Q.obj A) ≫ e.inv.app A ≫ a.hom ≫ e.hom.app B := by
    apply (cancel_epi (f.hom.app (Q.obj A))).mp
    rw [← Category.assoc, hb]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
    exact congrArg (fun z => e.inv.app A ≫ a.hom ≫ z)
      (Category.comp_id (e.hom.app B))
  apply (cancel_mono (h.inv.app B)).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    T.map_comp, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [hcomp B, ← Category.assoc (T.map b.hom), hb']
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [← Category.assoc (f.inv.app (Q.obj A)), ← hcomp A,
    ← Category.assoc (T.map (g.hom.app A)),
    ← Category.assoc (T.map (g.hom.app A)),
    ← T.map_comp, Iso.hom_inv_id_app, T.map_id, Category.id_comp,
    ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- The native comparison from the actual stalk overlap to the overlap with
an open neighborhood. -/
def punctureIsoPullbackComparison
    (X : Scheme.{u}) (x : X) (U N : X.Opens) (hxN : x ∈ N) :
    pullback (Limits.pullback.snd (X.fromSpecStalk x) U.ι) ≅
      pullback (Limits.pullback.snd N.ι U.ι) ⋙
        pullback (Scheme.stalkOverlapToNeighborhood X x U N hxN) :=
  MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤)
    (Scheme.stalkOverlapToNeighborhood X x U N hxN)
    (Limits.pullback.snd N.ι U.ι)
    (Limits.pullback.snd (X.fromSpecStalk x) U.ι)
    (Limits.pullback.lift_snd _ _ _).symm

/-- A specified isomorphism over the stalk overlap descends to an actual
open-neighborhood overlap, with its original pullback retained. -/
theorem exists_open_overlap_iso_fromSpecStalk
    (X : Scheme.{u}) [IsAffine X]
    (U : X.Opens) [QuasiCompact U.ι] (x : X)
    (A B : FiniteEtale U.toScheme)
    (a : (pullback (Limits.pullback.snd (X.fromSpecStalk x) U.ι)).obj A ≅
      (pullback (Limits.pullback.snd (X.fromSpecStalk x) U.ι)).obj B) :
    ∃ (N : X.Opens) (hxN : x ∈ N)
      (b : (pullback (Limits.pullback.snd N.ι U.ι)).obj A ≅
        (pullback (Limits.pullback.snd N.ι U.ι)).obj B),
      (punctureIsoPullbackComparison X x U N hxN).hom.app A ≫
          (pullback (Scheme.stalkOverlapToNeighborhood X x U N hxN)).map b.hom =
        a.hom ≫ (punctureIsoPullbackComparison X x U N hxN).hom.app B := by
  let F : (OpenNhds x)ᵒᵖ ⥤ CommRingCat.{u} :=
    (OpenNhds.inclusion x).op ⋙ X.presheaf
  let D : (OpenNhds x)ᵒᵖᵒᵖ ⥤ Over X :=
    { obj i := Over.mk
        (Spec.map (X.presheaf.map (homOfLE (show i.unop.unop.1 ≤ ⊤ from le_top)).op) ≫
          X.isoSpec.inv)
      map h := Over.homMk (Spec.map (F.map h.unop)) (by
        change Spec.map (X.presheaf.map ((OpenNhds.inclusion x).map h.unop.unop).op) ≫
            (Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ X.isoSpec.inv) =
          Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ X.isoSpec.inv
        rw [← Category.assoc, ← Spec.map_comp, ← X.presheaf.map_comp]
        rfl)
      map_id i := by
        apply Over.OverMorphism.ext
        exact (F.op ⋙ Scheme.Spec).map_id i
      map_comp h k := by
        apply Over.OverMorphism.ext
        exact (F.op ⋙ Scheme.Spec).map_comp h k }
  let c : Cone D :=
    { pt := Over.mk (X.fromSpecStalk x)
      π :=
        { app i := Over.homMk
            (Spec.map (X.presheaf.germ i.unop.unop.1 x i.unop.unop.2)) (by
              change Spec.map (X.presheaf.germ i.unop.unop.1 x i.unop.unop.2) ≫
                  (Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ X.isoSpec.inv) =
                X.fromSpecStalk x
              rw [← Category.assoc, ← Spec.map_comp, TopCat.Presheaf.germ_res,
                ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc,
                Scheme.toSpecΓ_isoSpec_inv, Category.comp_id])
          naturality i j h := by
            apply Over.OverMorphism.ext
            exact (Scheme.Spec.mapCone (colimit.cocone F).op).π.naturality h } }
  have hc : IsLimit c :=
    isLimitOfReflects (Over.forget X)
      (isLimitOfPreserves Scheme.Spec (colimit.isColimit F).op)
  have : ∀ {i j : (OpenNhds x)ᵒᵖᵒᵖ} (h : i ⟶ j),
      IsAffineHom (D.map h).left :=
    fun h ↦ inferInstanceAs (IsAffineHom (Spec.map (F.map h.unop)))
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, CompactSpace (D.obj i).left :=
    fun i ↦ inferInstanceAs (CompactSpace (Spec (F.obj i.unop)))
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, QuasiSeparatedSpace (D.obj i).left :=
    fun i ↦ inferInstanceAs (QuasiSeparatedSpace (Spec (F.obj i.unop)))
  let E : (OpenNhds x)ᵒᵖᵒᵖ ⥤ Scheme.{u} := AffineTransitionHom.diagram D U.ι
  let s : Cone E := AffineTransitionHom.cone D c U.ι
  have hs : IsLimit s := AffineTransitionHom.coneIsLimit D c hc U.ι
  have : ∀ {i j : (OpenNhds x)ᵒᵖᵒᵖ} (h : i ⟶ j), IsAffineHom (E.map h) :=
    fun h ↦ AffineTransitionHom.diagram_map_isAffineHom D U.ι h
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, CompactSpace (E.obj i) :=
    AffineTransitionHom.diagram_obj_compactSpace D U.ι
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, QuasiSeparatedSpace (E.obj i) :=
    AffineTransitionHom.diagram_obj_quasiSeparatedSpace D U.ι
  let i : (OpenNhds x)ᵒᵖᵒᵖ := op (op ⟨⊤, trivial⟩)
  let q (i : (OpenNhds x)ᵒᵖᵒᵖ) : E.obj i ⟶ U.toScheme :=
    Limits.pullback.snd (D.obj i).hom U.ι
  let ql : s.pt ⟶ U.toScheme := Limits.pullback.snd (X.fromSpecStalk x) U.ι
  let ci (i : (OpenNhds x)ᵒᵖᵒᵖ) : pullback ql ≅
      pullback (q i) ⋙ pullback (s.π.app i) :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      (s.π.app i) (q i) ql (AffineTransitionHom.cone_map_snd D c U.ι i).symm
  let a' : (pullback (s.π.app i)).obj ((pullback (q i)).obj A) ≅
      (pullback (s.π.app i)).obj ((pullback (q i)).obj B) :=
    (ci i).symm.app A ≪≫ a ≪≫ (ci i).app B
  obtain ⟨j, hji, b, hb⟩ := exists_inverse_limit_stage_iso E s hs i
    ((pullback (q i)).obj A) ((pullback (q i)).obj B) a'
  have hq : q j = E.map hji ≫ q i :=
    (Over.w ((Over.pullback U.ι).map (D.map hji))).symm
  let cj : pullback (q j) ≅ pullback (q i) ⋙ pullback (E.map hji) :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      (E.map hji) (q i) (q j) hq
  let bj : (pullback (q j)).obj A ≅ (pullback (q j)).obj B :=
    cj.app A ≪≫ b ≪≫ (cj.app B).symm
  have hbj : (ci j).hom.app A ≫ (pullback (s.π.app j)).map bj.hom =
      a.hom ≫ (ci j).hom.app B := by
    apply transport_recovered_iso (pullback ql) (pullback (q i)) (pullback (q j))
      (pullback (s.π.app i)) (pullback (E.map hji)) (pullback (s.π.app j))
      (ci i) (inverseLimitPullbackComparison E s hji) cj (ci j) ?_ a b hb
    intro C
    exact pullbackComp_inv_coherence (s.π.app j) (E.map hji) (q i)
      (s.π.app i) (q j) ql (s.w hji).symm hq
      (AffineTransitionHom.cone_map_snd D c U.ι i).symm
      (AffineTransitionHom.cone_map_snd D c U.ι j).symm C
  let N : X.Opens := j.unop.unop.1
  have hxN : x ∈ N := j.unop.unop.2
  have hN : N.toSpecΓ ≫ (D.obj j).hom = N.ι := by
    change N.toSpecΓ ≫
      (Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ X.isoSpec.inv) = N.ι
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
      Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  let k : Limits.pullback N.ι U.ι ⟶ E.obj j :=
    Limits.pullback.lift (Limits.pullback.fst N.ι U.ι ≫ N.toSpecΓ)
      (Limits.pullback.snd N.ι U.ι)
      (by rw [Category.assoc, hN]; exact Limits.pullback.condition)
  let l : s.pt ⟶ Limits.pullback N.ι U.ι :=
    Scheme.stalkOverlapToNeighborhood X x U N hxN
  have hlfst : l ≫ Limits.pullback.fst N.ι U.ι =
      Limits.pullback.fst (X.fromSpecStalk x) U.ι ≫ N.fromSpecStalkOfMem x hxN :=
    Limits.pullback.lift_fst _ _ _
  have hlsnd : l ≫ Limits.pullback.snd N.ι U.ι =
      Limits.pullback.snd (X.fromSpecStalk x) U.ι := Limits.pullback.lift_snd _ _ _
  have hlk : s.π.app j = l ≫ k := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, ← Category.assoc,
        hlfst, Category.assoc,
        Scheme.Opens.fromSpecStalkOfMem_toSpecΓ]
      exact AffineTransitionHom.cone_map_fst D c U.ι j
    · rw [Category.assoc, Limits.pullback.lift_snd, hlsnd]
      exact AffineTransitionHom.cone_map_snd D c U.ι j
  let qn : Limits.pullback N.ι U.ι ⟶ U.toScheme := Limits.pullback.snd N.ι U.ι
  have hqn : qn = k ≫ q j := (Limits.pullback.lift_snd _ _ _).symm
  have hql : ql = l ≫ qn := (Limits.pullback.lift_snd _ _ _).symm
  let ck : pullback qn ≅ pullback (q j) ⋙ pullback k :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) k (q j) qn hqn
  let cl : pullback (s.π.app j) ≅ pullback k ⋙ pullback l :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      l k (s.π.app j) hlk
  let bn : (pullback qn).obj A ≅ (pullback qn).obj B :=
    ck.app A ≪≫ (pullback k).mapIso bj ≪≫ (ck.app B).symm
  refine ⟨N, hxN, bn, ?_⟩
  apply transport_recovered_iso (pullback ql) (pullback (q j)) (pullback qn)
    (pullback (s.π.app j)) (pullback k) (pullback l)
    (ci j) cl ck (punctureIsoPullbackComparison X x U N hxN) ?_ a
    ((pullback k).mapIso bj) ?_
  · intro C
    exact pullbackComp_inv_coherence l k (q j) (s.π.app j) qn ql hlk hqn
      (AffineTransitionHom.cone_map_snd D c U.ι j).symm hql C
  · have hbj' : (pullback (s.π.app j)).map bj.hom =
        ((ci j).symm.app A ≪≫ a ≪≫ (ci j).app B).hom := by
      apply (cancel_epi ((ci j).hom.app A)).mp
      rw [hbj]
      change a.hom ≫ (ci j).hom.app B =
        (ci j).hom.app A ≫ (ci j).inv.app A ≫ a.hom ≫ (ci j).hom.app B
      rw [Iso.hom_inv_id_app_assoc]
    have hnatural := cl.hom.naturality bj.hom
    change (pullback (s.π.app j)).map bj.hom ≫ cl.hom.app ((pullback (q j)).obj B) =
      cl.hom.app ((pullback (q j)).obj A) ≫
        (pullback l).map ((pullback k).map bj.hom) at hnatural
    rw [hbj'] at hnatural
    exact hnatural.symm

end AlgebraicGeometry.FiniteEtale
