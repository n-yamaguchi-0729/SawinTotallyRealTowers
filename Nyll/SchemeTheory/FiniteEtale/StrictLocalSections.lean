/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.HenselianLocalSection
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Inseparable

/-!
# Extending finite étale sections over a strictly local spectrum

A morphism from a nonempty connected scheme into a finite étale scheme over
a strictly Henselian local ring factors uniquely through a global section.
In particular a section on a connected punctured spectrum extends uniquely.

Starting from one point of the connected source, finiteness lifts its
specialization to the closed point of the base. The existing Henselian
lifting theorem supplies a section through this closed-fiber point. The
section has clopen image; connectedness puts the whole source in that image.
No assumption on the dimension, normality, or Noetherianity of the ring is
used, and the source need not be quasi-compact or an open subscheme.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

private theorem comp_section_eq_of_range_subset
    {S X T : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) [IsOpenImmersion σ]
    (hσ : σ ≫ f = 𝟙 S) (j : T ⟶ S) (s : T ⟶ X) (hs : s ≫ f = j)
    (hrange : Set.range s ⊆ Set.range σ) : j ≫ σ = s := by
  let l : T ⟶ S := IsOpenImmersion.lift σ s hrange
  have hl : l ≫ σ = s := IsOpenImmersion.lift_fac σ s hrange
  have hlj : l = j := by
    calc
      l = l ≫ (σ ≫ f) := by rw [hσ, Category.comp_id]
      _ = (l ≫ σ) ≫ f := (Category.assoc l σ f).symm
      _ = s ≫ f := congrArg (fun a : T ⟶ X => a ≫ f) hl
      _ = j := hs
  exact hlj ▸ hl

/-- Every finite étale section over a nonempty connected scheme mapping to a
strictly local spectrum is the restriction of exactly one global section.
This applies to the actual punctured spectrum without a quasi-compactness
assumption. -/
theorem existsUnique_section_of_connected_of_strictHenselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {X T : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f] [Etale f]
    [ConnectedSpace T] (j : T ⟶ Spec (.of R)) (s : T ⟶ X) (hs : s ≫ f = j) :
    ∃! σ : Spec (.of R) ⟶ X, σ ≫ f = 𝟙 _ ∧ j ≫ σ = s := by
  let u : T := Classical.choice inferInstance
  obtain ⟨x, hxspecializes, hfx⟩ := f.isClosedMap.specializingMap
    (IsLocalRing.specializes_closedPoint (f (s u)))
  let r : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hr : r default = IsLocalRing.closedPoint R := by
    change Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) default = _
    rw [Spec.map_apply]
    exact IsLocalRing.PrimeSpectrum.comap_residue R
      (default : Spec (.of (IsLocalRing.ResidueField R)))
  obtain ⟨p, hp, hpx⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f r x
    (hfx.trans hr.symm)
  obtain ⟨σ, hσ, hresidue⟩ := Etale.exists_section_of_henselianLocalRing R f p hp
  have hσclosed : IsClosedImmersion σ := by
    have : IsClosedImmersion (σ ≫ f) := by rw [hσ]; infer_instance
    exact IsClosedImmersion.of_comp σ f
  have hσopen : IsOpenImmersion σ := by
    have : MorphismProperty.HasOfPostcompProperty
        (@IsOpenImmersion : MorphismProperty Scheme.{u}) @Etale := by
      apply MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
      intro Y Z g hg
      have : Etale g := hg
      exact inferInstanceAs (IsOpenImmersion (CategoryTheory.Limits.pullback.diagonal g))
    have hcomp : IsOpenImmersion (σ ≫ f) := by rw [hσ]; infer_instance
    exact MorphismProperty.of_postcomp (@IsOpenImmersion : MorphismProperty Scheme.{u})
      (W' := @Etale) σ f (inferInstance : Etale f) hcomp
  have hxrange : x ∈ Set.range σ := by
    refine ⟨IsLocalRing.closedPoint R, ?_⟩
    have h := congrArg
      (fun a : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X => a default) hresidue
    change σ (r default) = p default at h
    rw [hr, hpx] at h
    exact h
  have hsu : s u ∈ Set.range σ :=
    hxspecializes.mem_open (IsOpenImmersion.isOpen_range σ) hxrange
  have hclopen : IsClopen (s ⁻¹' Set.range σ) :=
    ⟨σ.isClosedEmbedding.isClosed_range.preimage s.continuous,
      (IsOpenImmersion.isOpen_range σ).preimage s.continuous⟩
  have hfull : s ⁻¹' Set.range σ = Set.univ := hclopen.eq_univ ⟨u, hsu⟩
  have hrange : Set.range s ⊆ Set.range σ := by
    rintro _ ⟨t, rfl⟩
    have ht : t ∈ s ⁻¹' Set.range σ := by rw [hfull]; exact Set.mem_univ t
    exact ht
  have hrestrict : j ≫ σ = s := comp_section_eq_of_range_subset f σ hσ j s hs hrange
  refine ⟨σ, ⟨hσ, hrestrict⟩, ?_⟩
  intro τ hτ
  have hpoint : τ (j u) ∈ Set.range σ := by
    refine ⟨j u, ?_⟩
    exact congrArg (fun a : T ⟶ X => a u) (hrestrict.trans hτ.2.symm)
  have hclosed : IsClosed (τ ⁻¹' Set.range σ) :=
    σ.isClosedEmbedding.isClosed_range.preimage τ.continuous
  have hclosedPoint : IsLocalRing.closedPoint R ∈ τ ⁻¹' Set.range σ :=
    (IsLocalRing.specializes_closedPoint (j u)).mem_closed hclosed hpoint
  have hτrange : Set.range τ ⊆ Set.range σ := by
    rintro _ ⟨q, rfl⟩
    exact (IsLocalRing.specializes_closedPoint q).mem_open
      ((IsOpenImmersion.isOpen_range σ).preimage τ.continuous) hclosedPoint
  have hτeq : (𝟙 (Spec (.of R))) ≫ σ = τ :=
    comp_section_eq_of_range_subset f σ hσ (𝟙 _) τ hτ.1 hτrange
  exact hτeq.symm.trans (Category.id_comp σ)

end AlgebraicGeometry.FiniteEtale
