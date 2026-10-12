/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.FiniteEtale.ClopenPullback
import Nyll.SchemeTheory.Topology.ConnectedComponentsMap
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
import Mathlib.Topology.Sets.Closeds

/-!
# Clopen descent from fullness of finite étale pullback

A clopen subset is represented by its characteristic section of the trivial
cover with two sheets. Fullness descends that section, without any hypothesis
that arbitrary finite étale covers descend. Lifting inclusions of clopen
subschemes proves uniqueness. For quasi-compact quasi-separated schemes,
this gives a homeomorphism on connected components.

This proves, in particular, the connected-component consequence of full
faithfulness discussed in Stacks Project, Section 58.19, Tag `0BLE`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.FiniteEtale

private theorem section_descent_of_pullback_full
    {X Y : Scheme.{u}} (f : X ⟶ Y) [(FiniteEtale.pullback f).Full]
    (W : FiniteEtale Y) (a : X ⟶ W.left) (ha : a ≫ W.hom = f) :
    ∃ s : Y ⟶ W.left, s ≫ W.hom = 𝟙 Y ∧ f ≫ s = a := by
  let : IsFiniteEtale (𝟙 Y) := .mk
  let T : FiniteEtale Y := FiniteEtale.mk (𝟙 Y)
  let F := FiniteEtale.pullback f
  let p : Limits.pullback (𝟙 Y) f ⟶ X := Limits.pullback.snd (𝟙 Y) f
  have hp : (p ≫ a) ≫ W.hom = p ≫ f := by
    rw [Category.assoc, ha]
  let kLeft : Limits.pullback (𝟙 Y) f ⟶ Limits.pullback W.hom f :=
    Limits.pullback.lift (p ≫ a) p hp
  have hkFst : kLeft ≫ Limits.pullback.fst W.hom f = p ≫ a :=
    Limits.pullback.lift_fst _ _ _
  let k : F.obj T ⟶ F.obj W :=
    MorphismProperty.Over.homMk kLeft (Limits.pullback.lift_snd _ _ _)
  let b : T ⟶ W := F.preimage k
  have hb : F.map b = k := F.map_preimage k
  let s : Y ⟶ W.left := b.left
  have hs : s ≫ W.hom = 𝟙 Y := MorphismProperty.Over.w b
  let bPullback : Limits.pullback (𝟙 Y) f ⟶ Limits.pullback W.hom f :=
    (F.map b).left
  have hbLeft : bPullback = kLeft :=
    congrArg (fun z : F.obj T ⟶ F.obj W =>
      (show Limits.pullback (𝟙 Y) f ⟶ Limits.pullback W.hom f from z.left)) hb
  have hbFst : bPullback ≫ Limits.pullback.fst W.hom f =
      Limits.pullback.fst (𝟙 Y) f ≫ s :=
    Limits.pullback.lift_fst _ _ _
  have hb₁ : Limits.pullback.fst (𝟙 Y) f ≫ s = p ≫ a :=
    hbFst.symm.trans ((congrArg
      (fun z : Limits.pullback (𝟙 Y) f ⟶ Limits.pullback W.hom f =>
        z ≫ Limits.pullback.fst W.hom f) hbLeft).trans hkFst)
  let t : X ⟶ Limits.pullback (𝟙 Y) f :=
    Limits.pullback.lift f (𝟙 X) (by rw [Category.comp_id, Category.id_comp])
  have ht₁ : t ≫ Limits.pullback.fst (𝟙 Y) f = f :=
    Limits.pullback.lift_fst _ _ _
  have ht₂ : t ≫ p = 𝟙 X := Limits.pullback.lift_snd _ _ _
  refine ⟨s, hs, ?_⟩
  calc
    f ≫ s = (t ≫ Limits.pullback.fst (𝟙 Y) f) ≫ s := by rw [ht₁]
    _ = t ≫ (p ≫ a) := by rw [Category.assoc, hb₁]
    _ = a := by rw [← Category.assoc, ht₂, Category.id_comp]

private theorem exists_characteristic_morphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Clopens X) :
    ∃ a : X ⟶ Y ⨿ Y,
      a ≫ coprod.desc (𝟙 Y) (𝟙 Y) = f ∧
        a ⁻¹' Set.range (coprod.inl : Y ⟶ Y ⨿ Y) = (U : Set X) := by
  classical
  have hcompl : IsCompl (Scheme.Opens.ι U.toOpens).opensRange
      (Scheme.Opens.ι (Uᶜ).toOpens).opensRange := by
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    apply IsCompl.of_eq
    · apply Opens.ext
      exact Set.inter_compl_self (U : Set X)
    · apply Opens.ext
      exact Set.union_compl_self (U : Set X)
  obtain ⟨h⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl
    (Scheme.Opens.ι U.toOpens) (Scheme.Opens.ι (Uᶜ).toOpens) hcompl
  let c := BinaryCofan.mk
    ((Scheme.Opens.ι U.toOpens) ≫ f ≫ (coprod.inl : Y ⟶ Y ⨿ Y))
    ((Scheme.Opens.ι (Uᶜ).toOpens) ≫ f ≫ (coprod.inr : Y ⟶ Y ⨿ Y))
  let a : X ⟶ Y ⨿ Y := h.desc c
  have haU : (Scheme.Opens.ι U.toOpens) ≫ a = (Scheme.Opens.ι U.toOpens) ≫ f ≫ coprod.inl :=
    h.fac c ⟨WalkingPair.left⟩
  have haV : (Scheme.Opens.ι (Uᶜ).toOpens) ≫ a = (Scheme.Opens.ι (Uᶜ).toOpens) ≫ f ≫ coprod.inr :=
    h.fac c ⟨WalkingPair.right⟩
  refine ⟨a, ?_, ?_⟩
  · apply BinaryCofan.IsColimit.hom_ext h
    · rw [BinaryCofan.mk_inl, ← Category.assoc, haU, Category.assoc, Category.assoc,
        coprod.inl_desc, Category.comp_id]
    · rw [BinaryCofan.mk_inr, ← Category.assoc, haV, Category.assoc, Category.assoc,
        coprod.inr_desc, Category.comp_id]
  · ext x
    by_cases hx : x ∈ U
    · have hax : a x = (coprod.inl : Y ⟶ Y ⨿ Y) (f x) :=
        congrArg (fun g : (Scheme.Opens.toScheme U.toOpens) ⟶ Y ⨿ Y => g ⟨x, hx⟩) haU
      constructor
      · intro _
        exact hx
      · intro _
        exact ⟨f x, hax.symm⟩
    · have hax : a x = (coprod.inr : Y ⟶ Y ⨿ Y) (f x) :=
        congrArg (fun g : (Scheme.Opens.toScheme (Uᶜ).toOpens) ⟶ Y ⨿ Y => g ⟨x, hx⟩) haV
      constructor
      · rintro ⟨y, hy⟩
        exact False.elim (inl_ne_inr Y Y y (f x) (hy.trans hax))
      · intro hx'
        exact False.elim (hx hx')

private theorem isFiniteEtale_double (Y : Scheme.{u}) :
    IsFiniteEtale (coprod.desc (𝟙 Y) (𝟙 Y)) := by
  have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have : Etale (coprod.desc (𝟙 Y) (𝟙 Y)) := by
    apply IsZariskiLocalAtSource.of_openCover (coprodOpenCover.{u, 0} Y Y)
    rintro (⟨⟩ | ⟨⟩)
    · change Etale ((coprod.inl : Y ⟶ Y ⨿ Y) ≫ coprod.desc (𝟙 Y) (𝟙 Y))
      rw [coprod.inl_desc]
      infer_instance
    · change Etale ((coprod.inr : Y ⟶ Y ⨿ Y) ≫ coprod.desc (𝟙 Y) (𝟙 Y))
      rw [coprod.inr_desc]
      infer_instance
  exact .mk

private theorem isClopen_range_inl (Y : Scheme.{u}) :
    IsClopen (Set.range (coprod.inl : Y ⟶ Y ⨿ Y)) := by
  constructor
  · rw [← isOpen_compl_iff]
    rw [(isCompl_range_inl_inr Y Y).compl_eq]
    exact IsOpenImmersion.isOpen_range (coprod.inr : Y ⟶ Y ⨿ Y)
  · exact IsOpenImmersion.isOpen_range (coprod.inl : Y ⟶ Y ⨿ Y)

/-- Fullness alone descends every clopen subset uniquely. The cover used to
construct the descent is the trivial two-sheeted cover. -/
theorem existsUnique_clopen_preimage_of_pullback_full
    {X Y : Scheme.{u}} (f : X ⟶ Y) [(FiniteEtale.pullback f).Full]
    (U : Clopens X) :
    ∃! V : Clopens Y, f ⁻¹' (V : Set Y) = (U : Set X) := by
  obtain ⟨a, ha, hU⟩ := exists_characteristic_morphism f U
  let : IsFiniteEtale (coprod.desc (𝟙 Y) (𝟙 Y)) := isFiniteEtale_double Y
  let W : FiniteEtale Y := FiniteEtale.mk (coprod.desc (𝟙 Y) (𝟙 Y))
  obtain ⟨s, _, hs⟩ := section_descent_of_pullback_full f W a ha
  let V : Clopens Y :=
    ⟨s ⁻¹' Set.range (coprod.inl : Y ⟶ Y ⨿ Y),
      (isClopen_range_inl Y).preimage s.continuous⟩
  have hV : f ⁻¹' (V : Set Y) = (U : Set X) := by
    change (f ≫ s) ⁻¹' Set.range (coprod.inl : Y ⟶ Y ⨿ Y) = (U : Set X)
    rw [hs]
    exact hU
  refine ⟨V, hV, ?_⟩
  intro T hT
  apply Clopens.ext
  exact Set.Subset.antisymm
    (clopen_subset_of_preimage_subset f T V (hT.trans hV.symm).subset)
    (clopen_subset_of_preimage_subset f V T (hV.trans hT.symm).subset)

/-- Fullness of finite étale pullback gives a bijection on clopen subsets. -/
theorem bijective_clopen_preimage_of_pullback_full
    {X Y : Scheme.{u}} (f : X ⟶ Y) [(FiniteEtale.pullback f).Full] :
    Function.Bijective (fun U : Clopens Y =>
      (⟨f ⁻¹' (U : Set Y), U.isClopen.preimage f.continuous⟩ : Clopens X)) := by
  constructor
  · intro U V h
    have hpre : f ⁻¹' (U : Set Y) = f ⁻¹' (V : Set Y) :=
      congrArg (fun C : Clopens X => (C : Set X)) h
    apply Clopens.ext
    exact Set.Subset.antisymm
      (clopen_subset_of_preimage_subset f U V hpre.subset)
      (clopen_subset_of_preimage_subset f V U hpre.symm.subset)
  · intro U
    obtain ⟨V, hV, _⟩ := existsUnique_clopen_preimage_of_pullback_full f U
    exact ⟨V, Clopens.ext hV⟩

/-- Fullness of finite étale pullback preserves and reflects connectedness. -/
theorem connectedSpace_iff_of_pullback_full
    {X Y : Scheme.{u}} (f : X ⟶ Y) [(FiniteEtale.pullback f).Full] :
    ConnectedSpace X ↔ ConnectedSpace Y :=
  SchemeTheory.connectedSpace_iff_of_clopen_preimage f.continuous
    (bijective_clopen_preimage_of_pullback_full f)

/-- For qcqs schemes, fullness of finite étale pullback identifies their actual
spaces of connected components. Essential surjectivity is unnecessary. -/
theorem connectedComponentsMap_isHomeomorph_of_pullback_full
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [(FiniteEtale.pullback f).Full] :
    IsHomeomorph f.continuous.connectedComponentsMap :=
  SchemeTheory.connectedComponentsMap_isHomeomorph_of_clopen_preimage f.continuous
    (bijective_clopen_preimage_of_pullback_full f)

end AlgebraicGeometry.FiniteEtale
