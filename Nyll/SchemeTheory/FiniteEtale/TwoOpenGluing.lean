/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Gluing finite étale covers over two open subschemes

An isomorphism over the actual intersection glues two finite étale covers.
The glued scheme is the pushout of their open overlap; the Cartesian squares
over the two base opens prove that its structural morphism is finite étale.
This supplies the two-open gluing step in Stacks Project, Tag 0EY7.
-/

noncomputable section

open CategoryTheory Limits
namespace AlgebraicGeometry.FiniteEtale
universe u

private theorem pushout_jointly_surjective
    {W A B : Scheme.{u}} (f : W ⟶ A) (g : W ⟶ B)
    [IsOpenImmersion f] [IsOpenImmersion g] (x : ↑(pushout f g)) :
    (∃ a, pushout.inl f g a = x) ∨ (∃ b, pushout.inr f g b = x) := by
  obtain ⟨i, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) x
  rcases i with _ | (_ | _)
  · left
    refine ⟨f y, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun h ↦ h y) (colimit.w (span f g) WalkingSpan.Hom.fst)
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

private theorem range_of_two_open_gluing
    {S U V O A B W Z : Scheme.{u}}
    (u : U ⟶ S) (v : V ⟶ S) (iU : O ⟶ U) (iV : O ⟶ V)
    (hO : IsPullback iU iV u v)
    (a : A ⟶ U) (b : B ⟶ V) (f : W ⟶ A) (g : W ⟶ B) (l : W ⟶ O)
    (hB : IsPullback g l b iV)
    (ia : A ⟶ Z) (ib : B ⟶ Z) (q : Z ⟶ S)
    (hab : f ≫ ia = g ≫ ib)
    (ha : ia ≫ q = a ≫ u) (hb : ib ≫ q = b ≫ v)
    (hc : ∀ z : Z, (∃ x, ia x = z) ∨ (∃ y, ib y = z)) :
    q ⁻¹' Set.range u = Set.range ia := by
  ext z
  constructor
  · rintro ⟨s, hs⟩
    rcases hc z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨x, rfl⟩
    · have hsy : u s = v (b y) := by
        rw [← Scheme.Hom.comp_apply, ← hb, Scheme.Hom.comp_apply]
        exact hs
      obtain ⟨o, _, ho⟩ := Scheme.exists_preimage_of_isPullback hO s (b y) hsy
      obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback hB y o ho.symm
      refine ⟨f w, ?_⟩
      rw [← Scheme.Hom.comp_apply, hab, Scheme.Hom.comp_apply, hw]
  · rintro ⟨x, rfl⟩
    refine ⟨a x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ha]

/-- Two finite étale covers with an isomorphism over a Cartesian overlap glue
over a jointly surjective pair of open immersions. -/
theorem exists_glued_of_isPullback
    {S U V O : Scheme.{u}} (u : U ⟶ S) (v : V ⟶ S)
    [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ s : S, (∃ x, u x = s) ∨ (∃ y, v y = s))
    (iU : O ⟶ U) (iV : O ⟶ V) (hO : IsPullback iU iV u v)
    (A : FiniteEtale U) (B : FiniteEtale V)
    (e : (pullback iU).obj A ≅ (pullback iV).obj B) :
    ∃ Z : FiniteEtale S,
      Nonempty ((pullback u).obj Z ≅ A) ∧
      Nonempty ((pullback v).obj Z ≅ B) := by
  have : IsOpenImmersion iU :=
    MorphismProperty.of_isPullback hO.flip (inferInstance : IsOpenImmersion v)
  have : IsOpenImmersion iV :=
    MorphismProperty.of_isPullback hO (inferInstance : IsOpenImmersion u)
  let W : Scheme.{u} := Limits.pullback A.hom iU
  let f : W ⟶ A.left := Limits.pullback.fst A.hom iU
  let l : W ⟶ O := Limits.pullback.snd A.hom iU
  let e₀ : W ≅ Limits.pullback B.hom iV :=
    (FiniteEtale.forget O ⋙ Over.forget O).mapIso e
  let g : W ⟶ B.left := e₀.hom ≫ Limits.pullback.fst B.hom iV
  have hel : e₀.hom ≫ Limits.pullback.snd B.hom iV = l := e.hom.w
  have hA : IsPullback f l A.hom iU := IsPullback.of_hasPullback A.hom iU
  have hB : IsPullback g l B.hom iV := by
    apply IsPullback.of_iso_pullback _ e₀ rfl hel
    constructor
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hel]
  have : IsOpenImmersion f := inferInstanceAs
    (IsOpenImmersion (Limits.pullback.fst A.hom iU))
  have : IsOpenImmersion g := inferInstanceAs
    (IsOpenImmersion (e₀.hom ≫ Limits.pullback.fst B.hom iV))
  have hw : f ≫ (A.hom ≫ u) = g ≫ (B.hom ≫ v) := by
    rw [← Category.assoc, hA.w, Category.assoc, hO.w,
      ← Category.assoc, ← hB.w, Category.assoc]
  let q : pushout f g ⟶ S := pushout.desc (A.hom ≫ u) (B.hom ≫ v) hw
  have hqa : pushout.inl f g ≫ q = A.hom ≫ u := pushout.inl_desc _ _ _
  have hqb : pushout.inr f g ≫ q = B.hom ≫ v := pushout.inr_desc _ _ _
  have hra : q ⁻¹' Set.range u = Set.range (pushout.inl f g) :=
    range_of_two_open_gluing u v iU iV hO A.hom B.hom f g l hB
      (pushout.inl f g) (pushout.inr f g) q pushout.condition hqa hqb
      (pushout_jointly_surjective f g)
  have hrb : q ⁻¹' Set.range v = Set.range (pushout.inr f g) :=
    range_of_two_open_gluing v u iV iU hO.flip B.hom A.hom g f l hA
      (pushout.inr f g) (pushout.inl f g) q pushout.condition.symm hqb hqa
      (fun z ↦ (pushout_jointly_surjective f g z).symm)
  have hpa : IsPullback A.hom (pushout.inl f g) u q :=
    IsOpenImmersion.isPullback A.hom (pushout.inl f g) u q hqa
      (TopologicalSpace.Opens.ext hra)
  have hpb : IsPullback B.hom (pushout.inr f g) v q :=
    IsOpenImmersion.isPullback B.hom (pushout.inr f g) v q hqb
      (TopologicalSpace.Opens.ext hrb)
  let C : S.OpenCover :=
    { I₀ := Bool
      X := fun j ↦ match j with | false => U | true => V
      f := fun j ↦ match j with | false => u | true => v
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        constructor
        · intro s
          rcases hc s with ⟨x, hx⟩ | ⟨y, hy⟩
          · exact ⟨false, x, hx⟩
          · exact ⟨true, y, hy⟩
        · intro j
          cases j <;> infer_instance }
  have hLocal : IsZariskiLocalAtTarget (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    ((HasAffineProperty.iff
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (Q := affineAnd RingHom.FiniteEtale)).mp inferInstance).1
  have : MorphismProperty.RespectsIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    hLocal.toRespects
  have hq : IsFiniteEtale q := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsFiniteEtale) C
    intro j
    cases j
    · change IsFiniteEtale (Limits.pullback.snd q u)
      rw [← hpa.flip.isoPullback_inv_snd]
      exact (MorphismProperty.cancel_left_of_respectsIso
        (@IsFiniteEtale : MorphismProperty Scheme.{u})
        hpa.flip.isoPullback.inv A.hom).mpr inferInstance
    · change IsFiniteEtale (Limits.pullback.snd q v)
      rw [← hpb.flip.isoPullback_inv_snd]
      exact (MorphismProperty.cancel_left_of_respectsIso
        (@IsFiniteEtale : MorphismProperty Scheme.{u})
        hpb.flip.isoPullback.inv B.hom).mpr inferInstance
  refine ⟨FiniteEtale.mk q, ⟨?_⟩, ⟨?_⟩⟩
  · exact MorphismProperty.Over.isoMk (P := @IsFiniteEtale)
      (Q := (⊤ : MorphismProperty Scheme.{u})) hpa.flip.isoPullback.symm
      hpa.flip.isoPullback_inv_snd
  · exact MorphismProperty.Over.isoMk (P := @IsFiniteEtale)
      (Q := (⊤ : MorphismProperty Scheme.{u})) hpb.flip.isoPullback.symm
      hpb.flip.isoPullback_inv_snd

/-- Finite étale covers on two opens glue over their union from an isomorphism
between their restrictions to the intersection. -/
theorem exists_glued_over_sup
    (X : Scheme.{u}) (U N : X.Opens)
    (A : FiniteEtale U.toScheme) (B : FiniteEtale N.toScheme)
    (e : (pullback (X.homOfLE (inf_le_left : U ⊓ N ≤ U))).obj A ≅
      (pullback (X.homOfLE (inf_le_right : U ⊓ N ≤ N))).obj B) :
    ∃ Z : FiniteEtale (U ⊔ N).toScheme,
      Nonempty ((pullback (X.homOfLE (le_sup_left : U ≤ U ⊔ N))).obj Z ≅ A) ∧
      Nonempty ((pullback (X.homOfLE (le_sup_right : N ≤ U ⊔ N))).obj Z ≅ B) := by
  refine exists_glued_of_isPullback
    (X.homOfLE (le_sup_left : U ≤ U ⊔ N))
    (X.homOfLE (le_sup_right : N ≤ U ⊔ N)) ?_
    (X.homOfLE (inf_le_left : U ⊓ N ≤ U))
    (X.homOfLE (inf_le_right : U ⊓ N ≤ N))
    (isPullback_opens_inf_le le_sup_left le_sup_right) A B e
  intro x
  rcases x.2 with hx | hx
  · exact Or.inl ⟨⟨x.1, hx⟩, X.homOfLE_apply' le_sup_left x.1 hx⟩
  · exact Or.inr ⟨⟨x.1, hx⟩, X.homOfLE_apply' le_sup_right x.1 hx⟩

end AlgebraicGeometry.FiniteEtale
