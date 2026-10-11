/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.UniversalHomeomorphismSections
public import Nyll.SchemeTheory.Morphisms.UnramifiedHomExt
public import Nyll.SchemeTheory.FiniteEtale.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Fully faithful finite étale pullback along universal homeomorphisms

Étale sections descend along integral, universally injective, surjective
morphisms. Applying section descent after pullback by the source object
gives fullness. Relative maps into a separated unramified scheme are
determined after a surjective morphism, giving faithfulness.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleInfStableUnderBaseChangeUniversalHomeomorphism :
    MorphismProperty.IsStableUnderBaseChange
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) :=
  MorphismProperty.IsStableUnderBaseChange.inf

local instance finiteEtaleInfStableUnderBaseChangeAlongUniversalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale)) h hf⟩

/-- Pullback along a universal homeomorphism is surjective on maps into any
étale object of the slice, with an arbitrary source object. -/
theorem pullback_map_surjective_of_integral_universallyInjective_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (T V : CategoryTheory.Over Y) [Etale V.hom] :
    Function.Surjective ((CategoryTheory.Over.pullback f).map (X := T) (Y := V)) := by
  let : UniversallyInjective (Limits.pullback.fst T.hom f) :=
    MorphismProperty.of_isPullback
      (P := (@UniversallyInjective : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback T.hom f).flip inferInstance
  intro a
  have hwa : a.left ≫ Limits.pullback.snd V.hom f =
      Limits.pullback.snd T.hom f := by
    simpa only [Over.pullback_obj_hom] using Over.w a
  have ha : (a.left ≫ Limits.pullback.fst V.hom f) ≫ V.hom =
      Limits.pullback.fst T.hom f ≫ T.hom := by
    calc
      _ = a.left ≫ Limits.pullback.snd V.hom f ≫ f := by
        rw [Category.assoc, Limits.pullback.condition]
      _ = Limits.pullback.snd T.hom f ≫ f := congrArg (· ≫ f) hwa
      _ = _ := Limits.pullback.condition.symm
  obtain ⟨r, hr⟩ := Etale.exists_lift_of_integral_universallyInjective_surjective
    (Limits.pullback.fst T.hom f) V.hom T.hom (a.left ≫ Limits.pullback.fst V.hom f) ha
  refine ⟨Over.homMk r hr.1, ?_⟩
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · simpa only [Over.pullback_map_left, Over.homMk_left, Limits.pullback.lift_fst] using hr.2
  · simpa only [Over.pullback_map_left, Limits.pullback.lift_snd] using hwa.symm

/-- Maps into a separated étale object are invariant under universal
homeomorphisms, even when the source object is arbitrary. -/
theorem pullback_map_bijective_of_integral_universallyInjective_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (T V : CategoryTheory.Over Y) [Etale V.hom] [IsSeparated V.hom] :
    Function.Bijective ((CategoryTheory.Over.pullback f).map (X := T) (Y := V)) := by
  refine ⟨?_, pullback_map_surjective_of_integral_universallyInjective_surjective f T V⟩
  intro a b hab
  let j : Over.mk (Limits.pullback.fst T.hom f ≫ T.hom) ⟶ T :=
    Over.homMk (Limits.pullback.fst T.hom f) rfl
  let : IsDominant j.left := inferInstanceAs (IsDominant (Limits.pullback.fst T.hom f))
  have hab' : Limits.pullback.fst T.hom f ≫ a.left =
      Limits.pullback.fst T.hom f ≫ b.left := by
    have h := congrArg
      (fun k : (Over.pullback f).obj T ⟶ (Over.pullback f).obj V ↦
        k.left ≫ Limits.pullback.fst V.hom f) hab
    simpa only [Over.pullback_map_left, Limits.pullback.lift_fst] using h
  apply AlgebraicGeometry.Over.hom_ext_of_isDominant_of_unramified a b j
  exact Over.OverMorphism.ext hab'

/-- Finite étale pullback along a universal homeomorphism is full. -/
theorem pullback_full_of_integral_universallyInjective_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ f).Full := by
  constructor
  intro A B a
  let : Etale B.hom := B.prop.2
  obtain ⟨b, hb⟩ :=
    pullback_map_surjective_of_integral_universallyInjective_surjective f A.toComma B.toComma a.hom
  refine ⟨MorphismProperty.Over.homMk b.left (Over.w b), ?_⟩
  apply MorphismProperty.Over.Hom.ext
  exact congrArg Over.Hom.left hb

/-- Finite étale pullback along a universal homeomorphism is faithful. -/
theorem pullback_faithful_of_integral_universallyInjective_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ f).Faithful := by
  constructor
  intro A B a b hab
  let : IsFinite B.hom := B.prop.1
  let : Etale B.hom := B.prop.2
  have h := (pullback_map_bijective_of_integral_universallyInjective_surjective
    f A.toComma B.toComma).1 (congrArg (fun k ↦ k.hom) hab)
  apply MorphismProperty.Over.Hom.ext
  exact congrArg Over.Hom.left h

/-- The fully faithful structure for finite étale pullback along a universal
homeomorphism. -/
def pullback_fullyFaithful_of_integral_universallyInjective_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ f).FullyFaithful := by
  letI := pullback_full_of_integral_universallyInjective_surjective f
  letI := pullback_faithful_of_integral_universallyInjective_surjective f
  exact Functor.FullyFaithful.ofFullyFaithful _

end AlgebraicGeometry.FiniteEtale
