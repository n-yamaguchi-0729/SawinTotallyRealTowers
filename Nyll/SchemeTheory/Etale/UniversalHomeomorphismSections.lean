/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.EtaleRadicial
public import Nyll.SchemeTheory.Morphisms.RadicialDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Maps.Basic

/-!
# Descending étale sections along universal homeomorphisms

A section of the base-changed étale morphism is an open immersion. The
homeomorphism on the total spaces carries its image to an open subscheme
of the original étale scheme. The projection of this open subscheme is
étale, surjective, and universally injective, hence an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Etale

/-- A section after a universal homeomorphism descends to an actual section
of the original étale morphism. -/
theorem exists_section_of_integral_universallyInjective_surjective
    {X Y V : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (p : V ⟶ Y) [Etale p] (w : X ⟶ V) (hw : w ≫ p = f) :
    ∃ r : Y ⟶ V, r ≫ p = 𝟙 Y ∧ f ≫ r = w := by
  let h : pullback p f ⟶ V := pullback.fst p f
  let : UniversallyInjective h :=
    UniversallyInjective.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback p f).flip inferInstance
  let q : pullback p f ⟶ X := pullback.snd p f
  let s : X ⟶ pullback p f :=
    pullback.lift w (𝟙 X) (hw.trans (Category.id_comp f).symm)
  have hsq : s ≫ q = 𝟙 X := pullback.lift_snd _ _ _
  have hsh : s ≫ h = w := pullback.lift_fst _ _ _
  let : Etale (s ≫ q) := hsq.symm ▸ inferInstanceAs (Etale (𝟙 X))
  let : Etale s := Etale.of_comp s q
  let : Mono s := mono_of_mono_fac hsq
  let : IsOpenImmersion s := IsOpenImmersion.of_flat_of_mono s
  have hopen : IsOpenMap h :=
    ((Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      h.continuous h.injective h.isClosedMap).isEmbedding.isOpenEmbedding_of_surjective
        h.surjective).isOpenMap
  let D : V.Opens := ⟨h '' Set.range s, hopen _ (IsOpenImmersion.isOpen_range s)⟩
  have hwD : Set.range w ⊆ Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine ⟨s x, ⟨x, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, hsh]
  let t : X ⟶ D := IsOpenImmersion.lift D.ι w hwD
  have ht : t ≫ D.ι = w := IsOpenImmersion.lift_fac D.ι w hwD
  let : Surjective t := ⟨fun z ↦ by
    obtain ⟨v, ⟨x, rfl⟩, hx⟩ := z.property
    refine ⟨x, D.ι.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ht]
    exact (congrArg (fun a : X ⟶ V ↦ a x) hsh).symm.trans hx⟩
  let g : (D : Scheme.{u}) ⟶ Y := D.ι ≫ p
  have htg : t ≫ g = f := by
    change t ≫ D.ι ≫ p = f
    rw [← Category.assoc, ht, hw]
  let : UniversallyInjective (t ≫ g) := htg.symm ▸ inferInstanceAs (UniversallyInjective f)
  let : UniversallyInjective g := UniversallyInjective.of_comp_surjective t g
  let : Surjective (t ≫ g) := htg.symm ▸ inferInstanceAs (Surjective f)
  let : Surjective g := Surjective.of_comp t g
  let : IsIso g := isIso_of_universallyInjective_of_surjective g
  refine ⟨inv g ≫ D.ι, ?_, ?_⟩
  · rw [Category.assoc]
    exact IsIso.inv_hom_id g
  · rw [← htg, Category.assoc, IsIso.hom_inv_id_assoc, ht]

/-- Relative maps into an étale scheme descend along a universal
homeomorphism, without a finiteness assumption on either scheme. -/
theorem exists_lift_of_integral_universallyInjective_surjective
    {X Y Z S : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (p : Z ⟶ S) [Etale p] (g : Y ⟶ S) (w : X ⟶ Z)
    (hw : w ≫ p = f ≫ g) :
    ∃ r : Y ⟶ Z, r ≫ p = g ∧ f ≫ r = w := by
  let l : X ⟶ pullback p g := pullback.lift w f hw
  obtain ⟨r, hr, hfr⟩ := exists_section_of_integral_universallyInjective_surjective
    f (pullback.snd p g) l (pullback.lift_snd _ _ _)
  refine ⟨r ≫ pullback.fst p g, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hr, Category.id_comp]
  · rw [← Category.assoc, hfr]
    exact pullback.lift_fst _ _ _

end AlgebraicGeometry.Etale
