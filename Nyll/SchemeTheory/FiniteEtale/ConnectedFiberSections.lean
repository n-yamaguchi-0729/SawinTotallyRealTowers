/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The clopen-section construction adapts the construction in:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing.lean
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.Connected.Clopen

/-!
# Descent of finite etale sections through connected fibres

An open surjection with connected fibres descends every clopen subset.
Applied to the image of a section of a finite etale cover after base change,
this constructs a clopen subscheme of the original cover. Its degree is one
because degree one is detected after surjective base change. Its inverse
therefore gives the actual descended section. No connectedness assumption
on either scheme is needed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- Clopen subsets descend along an open map with connected geometric fibres. -/
theorem exists_isClopen_preimage_eq_of_universallyOpen_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyOpen f] [GeometricallyConnected f]
    (V : Set X) (hV : IsClopen V) :
    ∃ U : Set S, IsClopen U ∧ f ⁻¹' U = V := by
  have hSaturated : ∀ x : X, f x ∈ f '' V ↔ x ∈ V := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hSubset : f ⁻¹' {f x} ⊆ V :=
        (f.isConnected_preimage_singleton (f x)).isPreconnected.subset_isClopen hV
          ⟨y, hyx, hy⟩
      exact hSubset rfl
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hComplement : (f '' V)ᶜ = f '' Vᶜ := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := f.surjective y
      exact ⟨x, fun hx => hy ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩ hy
      exact hx ((hSaturated x).mp hy)
  refine ⟨f '' V, ⟨?_, f.isOpenMap V hV.isOpen⟩, ?_⟩
  · rw [← isOpen_compl_iff, hComplement]
    exact f.isOpenMap Vᶜ hV.isClosed.isOpen_compl
  · exact Set.ext hSaturated

private theorem isIso_of_isIso_pullback_of_surjective
    {X Y S : Scheme.{u}} (f : X ⟶ S) [Surjective f]
    (π : Y ⟶ S) [IsFinite π] [Etale π]
    (h : IsIso (pullback.snd π f)) : IsIso π := by
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  funext s
  obtain ⟨x, rfl⟩ := f.surjective s
  have hrank := Scheme.Hom.finrank_pullback_snd π f x
  rw [Scheme.Hom.finrank_eq_one_of_isIso] at hrank
  exact hrank.symm

/-- Every section of a finite etale cover after a universally open base
change with connected geometric fibres descends to the original base. -/
theorem exists_section_descent_of_universallyOpen_geometricallyConnected
    {X Y S : Scheme.{u}} (f : X ⟶ S) [UniversallyOpen f] [GeometricallyConnected f]
    (π : Y ⟶ S) [IsFinite π] [Etale π]
    (a : X ⟶ Y) (ha : a ≫ π = f) :
    ∃ t : S ⟶ Y, t ≫ π = 𝟙 S ∧ f ≫ t = a := by
  let b : X ⟶ pullback π f := pullback.lift a (𝟙 X) (by rw [ha, Category.id_comp])
  have hb : b ≫ pullback.snd π f = 𝟙 X := pullback.lift_snd _ _ _
  have hba : b ≫ pullback.fst π f = a := pullback.lift_fst _ _ _
  have hEtale : Etale b := by
    have hComp : Etale (b ≫ pullback.snd π f) := by rw [hb]; infer_instance
    exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale)
      b (pullback.snd π f) inferInstance hComp
  have hSplit : IsSplitMono b := IsSplitMono.mk' ⟨pullback.snd π f, hb⟩
  have hOpen : IsOpenImmersion b := IsOpenImmersion.of_flat_of_mono b
  have hClosed : IsClosedImmersion b := by
    have hComp : IsClosedImmersion (b ≫ pullback.snd π f) := by
      rw [hb]
      infer_instance
    exact IsClosedImmersion.of_comp b (pullback.snd π f)
  let V : (pullback π f).Opens := b.opensRange
  have hV : IsClopen (V : Set ↥(pullback π f)) :=
    ⟨b.isClosedEmbedding.isClosed_range, V.isOpen⟩
  obtain ⟨Uset, hU, hPreimage⟩ :=
    exists_isClopen_preimage_eq_of_universallyOpen_geometricallyConnected
      (pullback.fst π f) V hV
  let U : Y.Opens := ⟨Uset, hU.isOpen⟩
  have hUClosed : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion U.ι (by rw [Scheme.Opens.range_ι]; exact hU.isClosed)
  have hURange : Set.range a ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : b x ∈ (V : Set ↥(pullback π f)) := ⟨x, rfl⟩
    rw [← hPreimage] at hx
    change (b ≫ pullback.fst π f) x ∈ Uset at hx
    rw [hba] at hx
    exact hx
  let c : X ⟶ U.toScheme := IsOpenImmersion.lift U.ι a hURange
  have hc : c ≫ U.ι = a := IsOpenImmersion.lift_fac U.ι a hURange
  let j : U.toScheme ⟶ S := U.ι ≫ π
  have hcj : c ≫ j = f := by
    change c ≫ (U.ι ≫ π) = f
    rw [← Category.assoc, hc, ha]
  let d : X ⟶ pullback j f := pullback.lift c (𝟙 X) (by rw [hcj, Category.id_comp])
  have hd : d ≫ pullback.snd j f = 𝟙 X := pullback.lift_snd _ _ _
  let m : pullback j f ⟶ pullback π f :=
    pullback.map j f π f U.ι (𝟙 X) (𝟙 S)
      (Category.comp_id j) ((Category.comp_id f).trans (Category.id_comp f).symm)
  have hm₁ : m ≫ pullback.fst π f = pullback.fst j f ≫ U.ι :=
    pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd π f = pullback.snd j f := by
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hdm : d ≫ m = b := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm₁, ← Category.assoc, pullback.lift_fst, hc, hba]
    · rw [Category.assoc, hm₂, hd, hb]
  have hRange : Set.range m ⊆ Set.range b := by
    rw [← Scheme.Hom.coe_opensRange b, ← hPreimage]
    rintro _ ⟨z, rfl⟩
    change (m ≫ pullback.fst π f) z ∈ Uset
    rw [hm₁]
    exact (pullback.fst j f z).property
  let e : pullback j f ⟶ X := IsOpenImmersion.lift b m hRange
  have he : e ≫ b = m := IsOpenImmersion.lift_fac b m hRange
  have heSnd : e = pullback.snd j f := by
    rw [← Category.comp_id e, ← hb, ← Category.assoc, he, hm₂]
  have hmMono : Mono m := by
    have : IsOpenImmersion m := inferInstance
    infer_instance
  have hdLeft : pullback.snd j f ≫ d = 𝟙 (pullback j f) := by
    apply (cancel_mono m).mp
    rw [Category.assoc, hdm, Category.id_comp, ← heSnd, he]
  have hIsoPullback : IsIso (pullback.snd j f) :=
    ⟨⟨d, hdLeft, hd⟩⟩
  have hIso : IsIso j := isIso_of_isIso_pullback_of_surjective f j hIsoPullback
  refine ⟨inv j ≫ U.ι, ?_, ?_⟩
  · rw [Category.assoc, IsIso.inv_hom_id]
  · rw [← hcj, Category.assoc, ← Category.assoc j, IsIso.hom_inv_id,
      Category.id_comp, hc]

end AlgebraicGeometry
