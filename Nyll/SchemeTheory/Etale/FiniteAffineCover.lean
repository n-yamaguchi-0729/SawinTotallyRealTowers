/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Finite affine refinements of étale covers

An étale cover of a quasi-compact scheme has a finite affine refinement by
open subschemes of its members. Collapsing this finite cover to its disjoint
union gives a single surjective étale morphism with affine source.

The refinement morphism is retained on the finite family: the disjoint union
need not map to one fixed member of the original cover. Over an affine base,
its map on global sections is faithfully flat and étale, providing the ring
map needed for effective descent. No ground field, noetherianity, or
quasi-separatedness of the base is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme.Cover

/-- A finite affine refinement of an étale cover, together with its single
affine, surjective, étale total-space morphism. The component maps to the
original cover are open immersions. The underlying refinement hom allows
the indexing universe of the original cover to differ from the scheme universe. -/
theorem exists_finite_affine_etale_refinement {X : Scheme.{u}} [CompactSpace X]
    (𝒰 : X.Cover.{v} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale))) :
    ∃ (𝒱 : Scheme.AffineCover.{u} (show MorphismProperty Scheme.{u} from @Etale) X)
      (e : 𝒱.cover.toPreZeroHypercover.Hom 𝒰.toPreZeroHypercover),
      Finite 𝒱.I₀ ∧ (∀ i : 𝒱.I₀, IsOpenImmersion (e.h₀ i)) ∧
      IsAffine (∐ fun i : 𝒱.I₀ => Spec (𝒱.X i)) ∧
      Etale (Sigma.desc 𝒱.f) ∧ Surjective (Sigma.desc 𝒱.f) := by
  let 𝒰' := 𝒰.ulift
  let a : 𝒰'.toPreZeroHypercover.Hom 𝒰.toPreZeroHypercover :=
    { s₀ := 𝒰.idx
      h₀ x := 𝟙 (𝒰.X (𝒰.idx x))
      w₀ x := Category.id_comp (𝒰.f (𝒰.idx x)) }
  let : QuasiCompactCover 𝒰'.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i => (𝒰'.f i).isOpenMap)
  obtain ⟨𝒱, e', hfinite, he'⟩ :
      ∃ (𝒱 : Scheme.AffineCover.{u} (show MorphismProperty Scheme.{u} from @Etale) X)
        (e : 𝒱.cover ⟶ 𝒰'), Finite 𝒱.I₀ ∧ ∀ i : 𝒱.I₀, IsOpenImmersion (e.h₀ i) :=
    QuasiCompactCover.exists_hom 𝒰'
  let e : 𝒱.cover.toPreZeroHypercover.Hom 𝒰.toPreZeroHypercover :=
    PreZeroHypercover.Hom.comp e' a
  have he (i : 𝒱.I₀) : IsOpenImmersion (e.h₀ i) := by
    have : IsOpenImmersion (e'.h₀ i) := he' i
    change IsOpenImmersion (e'.h₀ i ≫ 𝟙 _)
    infer_instance
  have : Finite 𝒱.I₀ := hfinite
  let : IsZariskiLocalAtSource (show MorphismProperty Scheme.{u} from @Etale) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨𝒱, e, hfinite, he, inferInstance, 𝒱.cover.sigma.map_prop default, ?_⟩
  constructor
  intro x
  obtain ⟨y, hy⟩ := 𝒱.covers x
  refine ⟨Sigma.ι (fun i : 𝒱.I₀ => Spec (𝒱.X i)) (𝒱.idx x) y, ?_⟩
  rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  exact hy

/-- Over an affine base the finite refinement supplies a faithfully flat
étale map on actual global section rings, ready for affine algebra descent. -/
theorem exists_finite_affine_etale_refinement_faithfullyFlat
    {X : Scheme.{u}} [IsAffine X]
    (𝒰 : X.Cover.{v} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale))) :
    ∃ (𝒱 : Scheme.AffineCover.{u} (show MorphismProperty Scheme.{u} from @Etale) X)
      (e : 𝒱.cover.toPreZeroHypercover.Hom 𝒰.toPreZeroHypercover),
      Finite 𝒱.I₀ ∧ (∀ i : 𝒱.I₀, IsOpenImmersion (e.h₀ i)) ∧
      (Sigma.desc 𝒱.f).appTop.hom.FaithfullyFlat ∧
      (Sigma.desc 𝒱.f).appTop.hom.Etale := by
  obtain ⟨𝒱, e, hfinite, he, hAffine, hEtale, hSurjective⟩ :=
    exists_finite_affine_etale_refinement 𝒰
  have : IsAffine (∐ fun i : 𝒱.I₀ => Spec (𝒱.X i)) := hAffine
  have : Etale (Sigma.desc 𝒱.f) := hEtale
  have : Surjective (Sigma.desc 𝒱.f) := hSurjective
  exact ⟨𝒱, e, hfinite, he,
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (Sigma.desc 𝒱.f)).mp
      ⟨inferInstance, hSurjective⟩,
    HasRingHomProperty.appTop (P := @Etale) (Sigma.desc 𝒱.f) hEtale⟩

end AlgebraicGeometry.Scheme.Cover
