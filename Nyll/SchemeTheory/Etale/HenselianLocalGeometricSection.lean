/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.HenselianLocalSection
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Étale sections through arbitrary closed field points

An arbitrary field-valued point over the closed point of a strictly local
spectrum extends uniquely to an étale section. The residue-field point lifts
by Henselianity. Its section is an open immersion; its image contains the
given field-valued point and determines the section uniquely.

The open-section argument is adapted from
`SchemeTheory/FiniteEtale/StrictLocalSections.lean` by the same authors.
Here the closed-point hypothesis removes the need for the étale morphism
to be finite, and no change of field or algebraization is needed.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Etale

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

/-- Every field-valued point over the closed point of a strictly local
spectrum lies on exactly one global section of an arbitrary étale scheme. -/
theorem existsUnique_section_of_closedFieldPoint
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Etale f]
    {Ω : Type u} [Field Ω] (j : Spec (.of Ω) ⟶ Spec (.of R))
    (hj : j default = IsLocalRing.closedPoint R)
    (s : Spec (.of Ω) ⟶ X) (hs : s ≫ f = j) :
    ∃! σ : Spec (.of R) ⟶ X, σ ≫ f = 𝟙 _ ∧ j ≫ σ = s := by
  let r : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hr : r default = IsLocalRing.closedPoint R := by
    change Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) default = _
    rw [Spec.map_apply]
    exact IsLocalRing.PrimeSpectrum.comap_residue R
      (default : Spec (.of (IsLocalRing.ResidueField R)))
  have hx : f (s default) = r default := by
    have h := congrArg
      (fun a : Spec (.of Ω) ⟶ Spec (.of R) => a default) hs
    change f (s default) = j default at h
    exact h.trans (hj.trans hr.symm)
  obtain ⟨p, hp, hpx⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f r (s default) hx
  obtain ⟨σ, hσ, hresidue⟩ := exists_section_of_henselianLocalRing R f p hp
  have hσopen : IsOpenImmersion σ := by
    have : MorphismProperty.HasOfPostcompProperty
        (@IsOpenImmersion : MorphismProperty Scheme.{u}) @Etale := by
      apply MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
      intro Y Z g hg
      have : Etale g := hg
      exact inferInstanceAs
        (IsOpenImmersion (CategoryTheory.Limits.pullback.diagonal g))
    have hcomp : IsOpenImmersion (σ ≫ f) := by rw [hσ]; infer_instance
    exact MorphismProperty.of_postcomp (@IsOpenImmersion : MorphismProperty Scheme.{u})
      (W' := @Etale) σ f (inferInstance : Etale f) hcomp
  have hxrange : s default ∈ Set.range σ := by
    refine ⟨IsLocalRing.closedPoint R, ?_⟩
    have h := congrArg
      (fun a : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X => a default) hresidue
    change σ (r default) = p default at h
    rw [hr, hpx] at h
    exact h
  have hrange : Set.range s ⊆ Set.range σ := by
    rintro _ ⟨t, rfl⟩
    rw [Subsingleton.elim t default]
    exact hxrange
  have hrestrict : j ≫ σ = s :=
    comp_section_eq_of_range_subset f σ hσ j s hs hrange
  refine ⟨σ, ⟨hσ, hrestrict⟩, ?_⟩
  intro τ hτ
  have hclosedPoint : IsLocalRing.closedPoint R ∈ τ ⁻¹' Set.range σ := by
    refine ⟨IsLocalRing.closedPoint R, ?_⟩
    have h := congrArg (fun a : Spec (.of Ω) ⟶ X => a default)
      (hrestrict.trans hτ.2.symm)
    change σ (j default) = τ (j default) at h
    rw [hj] at h
    exact h
  have hτrange : Set.range τ ⊆ Set.range σ := by
    rintro _ ⟨q, rfl⟩
    exact (IsLocalRing.specializes_closedPoint q).mem_open
      ((IsOpenImmersion.isOpen_range σ).preimage τ.continuous) hclosedPoint
  have hτeq : (𝟙 (Spec (.of R))) ≫ σ = τ :=
    comp_section_eq_of_range_subset f σ hσ (𝟙 _) τ hτ.1 hτrange
  exact hτeq.symm.trans (Category.id_comp σ)

end AlgebraicGeometry.Etale
