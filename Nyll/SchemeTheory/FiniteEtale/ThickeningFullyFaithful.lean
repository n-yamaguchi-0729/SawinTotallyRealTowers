/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.AffineThickening
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Unique lifting to finite étale schemes across thickenings

Affine lifting supplies local maps on the directed cover by affine opens.
Affine uniqueness makes these maps compatible, so they glue to a unique
global map. In particular, pullback along any surjective closed immersion
is fully faithful on finite étale covers.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleInfStableUnderBaseChangeThickening :
    MorphismProperty.IsStableUnderBaseChange
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) :=
  MorphismProperty.IsStableUnderBaseChange.inf

private theorem affine_existsUnique_lift
    {X Y Z S : Scheme.{u}} [IsAffine Y]
    (i : X ⟶ Y) [IsClosedImmersion i] [Surjective i]
    (p : Z ⟶ S) [IsFinite p] [Etale p]
    (g : Y ⟶ S) (s : X ⟶ Z) (hs : s ≫ p = i ≫ g) :
    ∃! t : Y ⟶ Z, t ≫ p = g ∧ i ≫ t = s := by
  let : HasPullback p g := inferInstance
  let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale
  let A : P.Over ⊤ Y := MorphismProperty.Over.mk ⊤ (𝟙 Y) ⟨inferInstance, inferInstance⟩
  let B : P.Over ⊤ Y := MorphismProperty.Over.mk ⊤
    (pullback.snd p g) ⟨inferInstance, inferInstance⟩
  let F := MorphismProperty.Over.pullback P ⊤ i
  let : F.IsEquivalence :=
    pullback_isEquivalence_of_isAffine_of_surjective_closedImmersion i
  let inner : Limits.pullback (𝟙 Y) i ⟶ Limits.pullback p g :=
    pullback.lift (pullback.snd (𝟙 Y) i ≫ s) (pullback.snd (𝟙 Y) i ≫ i)
      (by rw [Category.assoc, hs, Category.assoc])
  have hinner : inner ≫ pullback.snd p g = pullback.snd (𝟙 Y) i ≫ i :=
    pullback.lift_snd _ _ _
  have hinner_fst : inner ≫ pullback.fst p g = pullback.snd (𝟙 Y) i ≫ s :=
    pullback.lift_fst _ _ _
  let outer : Limits.pullback (𝟙 Y) i ⟶ Limits.pullback (pullback.snd p g) i :=
    pullback.lift inner (pullback.snd (𝟙 Y) i) hinner
  have houter : outer ≫ pullback.snd (pullback.snd p g) i = pullback.snd (𝟙 Y) i :=
    pullback.lift_snd _ _ _
  have houter_fst : outer ≫ pullback.fst (pullback.snd p g) i = inner :=
    pullback.lift_fst _ _ _
  let σ : F.obj A ⟶ F.obj B := MorphismProperty.Over.homMk outer houter
  obtain ⟨m, hm⟩ := F.map_surjective σ
  let mleft : Y ⟶ Limits.pullback p g := m.left
  let t : Y ⟶ Z := mleft ≫ pullback.fst p g
  have hmw : mleft ≫ pullback.snd p g = 𝟙 Y := MorphismProperty.Over.w m
  have ht : t ≫ p = g := by
    change (mleft ≫ pullback.fst p g) ≫ p = g
    rw [Category.assoc, pullback.condition, ← Category.assoc, hmw, Category.id_comp]
  have hFst : pullback.fst (𝟙 Y) i = pullback.snd (𝟙 Y) i ≫ i :=
    (Category.comp_id _).symm.trans pullback.condition
  have hmap : pullback.fst (𝟙 Y) i ≫ mleft = inner := by
    have h := congrArg (fun k : F.obj A ⟶ F.obj B ↦
      (show Limits.pullback (𝟙 Y) i ⟶ Limits.pullback (pullback.snd p g) i from k.left) ≫
        pullback.fst (pullback.snd p g) i) hm
    exact (pullback.lift_fst _ _ _).symm.trans (h.trans houter_fst)
  have hit : i ≫ t = s := by
    apply (cancel_epi (pullback.snd (𝟙 Y) i)).mp
    change pullback.snd (𝟙 Y) i ≫ i ≫ mleft ≫ pullback.fst p g = _
    rw [← Category.assoc, ← hFst, ← Category.assoc, hmap, hinner_fst]
  refine ⟨t, ⟨ht, hit⟩, ?_⟩
  intro l hl
  let μleft : Y ⟶ Limits.pullback p g :=
    pullback.lift l (𝟙 Y) (hl.1.trans (Category.id_comp g).symm)
  have hμleft : μleft ≫ pullback.snd p g = 𝟙 Y := pullback.lift_snd _ _ _
  have hμleft_fst : μleft ≫ pullback.fst p g = l := pullback.lift_fst _ _ _
  let μ : A ⟶ B := MorphismProperty.Over.homMk μleft hμleft
  have hcomp : pullback.fst (𝟙 Y) i ≫ μleft = inner := by
    apply pullback.hom_ext
    · rw [Category.assoc, hμleft_fst, hFst, Category.assoc, hl.2, hinner_fst]
    · rw [Category.assoc, hμleft, Category.comp_id, hFst, hinner]
  have hμ : F.map μ = σ := by
    apply MorphismProperty.Over.Hom.ext
    change (show Limits.pullback (𝟙 Y) i ⟶ Limits.pullback (pullback.snd p g) i from
      (F.map μ).left) = outer
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (hcomp.trans houter_fst.symm)
    · exact (pullback.lift_snd _ _ _).trans houter.symm
  have hμm : μ = m := F.map_injective (hμ.trans hm.symm)
  exact hμleft_fst.symm.trans
    (congrArg (fun k : A ⟶ B ↦ (show Y ⟶ Limits.pullback p g from k.left) ≫
      pullback.fst p g) hμm)

/-- A map to a finite étale scheme lifts uniquely across a surjective closed immersion. -/
theorem existsUnique_lift_of_surjective_closedImmersion
    {X Y Z S : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] [Surjective i]
    (p : Z ⟶ S) [IsFinite p] [Etale p]
    (g : Y ⟶ S) (s : X ⟶ Z) (hs : s ≫ p = i ≫ g) :
    ∃! t : Y ⟶ Z, t ≫ p = g ∧ i ≫ t = s := by
  let 𝒰 := Y.directedAffineCover
  have hlocal (j : 𝒰.I₀) : ∃! t : 𝒰.X j ⟶ Z,
      t ≫ p = 𝒰.f j ≫ g ∧
        pullback.snd i (𝒰.f j) ≫ t = pullback.fst i (𝒰.f j) ≫ s := by
    let : IsAffine (𝒰.X j) := j.2
    apply affine_existsUnique_lift (pullback.snd i (𝒰.f j)) p (𝒰.f j ≫ g)
      (pullback.fst i (𝒰.f j) ≫ s)
    rw [Category.assoc, hs, ← Category.assoc, pullback.condition, Category.assoc]
  let t (j : 𝒰.I₀) : 𝒰.X j ⟶ Z := (hlocal j).choose
  have ht (j : 𝒰.I₀) : t j ≫ p = 𝒰.f j ≫ g ∧
      pullback.snd i (𝒰.f j) ≫ t j = pullback.fst i (𝒰.f j) ≫ s :=
    (hlocal j).choose_spec.1
  have htrans {j k : 𝒰.I₀} (hjk : j ⟶ k) : 𝒰.trans hjk ≫ t k = t j := by
    apply (hlocal j).choose_spec.2
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, (ht k).1, ← Category.assoc, 𝒰.trans_map]
    · let a : Limits.pullback i (𝒰.f j) ⟶ Limits.pullback i (𝒰.f k) :=
        pullback.map i (𝒰.f j) i (𝒰.f k) (𝟙 X) (𝒰.trans hjk) (𝟙 Y)
          (by simp only [Category.id_comp, Category.comp_id])
          (by simp only [𝒰.trans_map, Category.comp_id])
      have ha₁ : a ≫ pullback.fst i (𝒰.f k) = pullback.fst i (𝒰.f j) := by
        simp only [a, pullback.lift_fst, Category.comp_id]
      have ha₂ : a ≫ pullback.snd i (𝒰.f k) =
          pullback.snd i (𝒰.f j) ≫ 𝒰.trans hjk := by
        simp only [a, pullback.lift_snd]
      rw [← Category.assoc, ← ha₂, Category.assoc, (ht k).2, ← Category.assoc, ha₁]
  let l : Y ⟶ Z := 𝒰.glueMorphismsOfLocallyDirected t htrans
  have hl (j : 𝒰.I₀) : 𝒰.f j ≫ l = t j :=
    𝒰.map_glueMorphismsOfLocallyDirected t htrans j
  have hlp : l ≫ p = g := by
    apply 𝒰.hom_ext
    intro j
    rw [← Category.assoc, hl, (ht j).1]
  have hil : i ≫ l = s := by
    apply Scheme.Cover.hom_ext (𝒰.pullback₁ i)
    intro j
    change pullback.fst i (𝒰.f j) ≫ i ≫ l = pullback.fst i (𝒰.f j) ≫ s
    have hlj : 𝒰.f j ≫ l = t j := hl j
    rw [← Category.assoc, pullback.condition, Category.assoc, hlj, (ht j).2]
  refine ⟨l, ⟨hlp, hil⟩, ?_⟩
  intro m hm
  apply 𝒰.hom_ext
  intro j
  rw [hl]
  apply (hlocal j).choose_spec.2
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hm.1]
  · rw [← Category.assoc, ← pullback.condition, Category.assoc, hm.2]

/-- Pullback across a thickening preserves all maps into a finite étale object, even when the
source object is an arbitrary scheme over the base. -/
theorem pullback_map_bijective_to_finiteEtale
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] [Surjective i]
    (T V : CategoryTheory.Over Y) [IsFinite V.hom] [Etale V.hom] :
    Function.Bijective ((CategoryTheory.Over.pullback i).map (X := T) (Y := V)) := by
  constructor
  · intro f g hfg
    have hfg' : pullback.fst T.hom i ≫ f.left = pullback.fst T.hom i ≫ g.left := by
      have h := congrArg
        (fun k : (Over.pullback i).obj T ⟶ (Over.pullback i).obj V ↦
          k.left ≫ pullback.fst V.hom i) hfg
      simpa only [Over.pullback_map_left, pullback.lift_fst] using h
    obtain ⟨t, ht, huniq⟩ := existsUnique_lift_of_surjective_closedImmersion
      (pullback.fst T.hom i) V.hom T.hom (pullback.fst T.hom i ≫ f.left)
      (by rw [Category.assoc, Over.w f])
    apply Over.OverMorphism.ext
    exact (huniq f.left ⟨Over.w f, rfl⟩).trans
      (huniq g.left ⟨Over.w g, hfg'.symm⟩).symm
  · intro f
    have hs : (f.left ≫ pullback.fst V.hom i) ≫ V.hom =
        pullback.fst T.hom i ≫ T.hom := by
      calc
        _ = f.left ≫ pullback.snd V.hom i ≫ i := by
          rw [Category.assoc, pullback.condition]
        _ = pullback.snd T.hom i ≫ i := by
          have hw : f.left ≫ pullback.snd V.hom i = pullback.snd T.hom i := by
            simpa only [Over.pullback_obj_hom] using (Over.w f)
          rw [← Category.assoc, hw]
        _ = _ := pullback.condition.symm
    obtain ⟨t, ht, _⟩ := existsUnique_lift_of_surjective_closedImmersion
      (pullback.fst T.hom i) V.hom T.hom (f.left ≫ pullback.fst V.hom i) hs
    refine ⟨Over.homMk t ht.1, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.pullback_map_left, Over.homMk_left, pullback.lift_fst] using ht.2
    · simpa only [Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_snd]
        using (Over.w f).symm

/-- Finite étale pullback along a surjective closed immersion is full. -/
theorem pullback_full_of_surjective_closedImmersion
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] [Surjective i] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ i).Full := by
  constructor
  intro A B f
  let : IsFinite B.hom := B.prop.1
  let : Etale B.hom := B.prop.2
  obtain ⟨g, hg⟩ := (pullback_map_bijective_to_finiteEtale i A.toComma B.toComma).2 f.hom
  refine ⟨MorphismProperty.Over.homMk g.left (Over.w g), ?_⟩
  apply MorphismProperty.Over.Hom.ext
  exact congrArg Over.Hom.left hg

/-- Finite étale pullback along a surjective closed immersion is faithful. -/
theorem pullback_faithful_of_surjective_closedImmersion
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] [Surjective i] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ i).Faithful := by
  constructor
  intro A B f g hfg
  let : IsFinite B.hom := B.prop.1
  let : Etale B.hom := B.prop.2
  have h := (pullback_map_bijective_to_finiteEtale i A.toComma B.toComma).1
    (congrArg (fun k ↦ k.hom) hfg)
  apply MorphismProperty.Over.Hom.ext
  exact congrArg Over.Hom.left h

/-- The fully faithful structure on finite étale pullback along a thickening. -/
def pullback_fullyFaithful_of_surjective_closedImmersion
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] [Surjective i] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ i).FullyFaithful := by
  letI := pullback_full_of_surjective_closedImmersion i
  letI := pullback_faithful_of_surjective_closedImmersion i
  exact Functor.FullyFaithful.ofFullyFaithful _

end AlgebraicGeometry.FiniteEtale
