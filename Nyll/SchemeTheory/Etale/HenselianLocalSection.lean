/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianEtaleSection
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Spectrum.Prime.Topology


/-!
# Sections of étale morphisms over Henselian local spectra

A rational point of the closed fiber of an arbitrary étale scheme over a
Henselian local ring lifts to a section. An affine open neighborhood of the
point reduces this statement to étale algebra section lifting over a
Henselian pair. The étale scheme need not be affine or finite over the base.

For a separably closed residue field, a point over the closed point supplies
the rational point, so every étale cover of a strictly local spectrum splits.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem exists_affine_section_of_henselian
    (R B : Type u) [CommRing R] [CommRing B]
    (I : Ideal R) [HenselianRing R I]
    (f : Spec (.of B) ⟶ Spec (.of R)) [Etale f]
    (p : Spec (.of (R ⧸ I)) ⟶ Spec (.of B))
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ∃ s : Spec (.of R) ⟶ Spec (.of B), s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s = p := by
  obtain ⟨r, rfl⟩ := Spec.map_surjective f
  obtain ⟨a, rfl⟩ := Spec.map_surjective p
  let : Algebra R B := r.hom.toAlgebra
  have : Algebra.Etale R B :=
    RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp
      (show Etale (Spec.map r) from inferInstance))
  have hcomp : r ≫ a = CommRingCat.ofHom (Ideal.Quotient.mk I) :=
    Spec.map_injective ((Spec.map_comp r a).trans hp)
  let σ : B →ₐ[R] R ⧸ I :=
    { a.hom with
      commutes' x := congrArg
        (fun h : CommRingCat.of R ⟶ CommRingCat.of (R ⧸ I) => h.hom x) hcomp }
  obtain ⟨τ, hτ⟩ :=
    (Algebra.Etale.bijective_comp_quotient_of_henselian (B := B) I).surjective σ
  have hsection : r ≫ CommRingCat.ofHom τ.toRingHom = 𝟙 (CommRingCat.of R) := by
    apply CommRingCat.hom_ext
    exact τ.comp_algebraMap
  have hresidue : CommRingCat.ofHom τ.toRingHom ≫
      CommRingCat.ofHom (Ideal.Quotient.mk I) = a := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom hτ
  refine ⟨Spec.map (CommRingCat.ofHom τ.toRingHom), ?_, ?_⟩
  · rw [← Spec.map_comp, hsection, Spec.map_id]
  · rw [← Spec.map_comp, hresidue]

/-- Every residue-field point of an étale scheme over a Henselian local ring
lifts to an actual section, with its closed-fiber restriction prescribed. -/
theorem exists_section_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Etale f]
    (p : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ s : Spec (.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = p := by
  obtain ⟨B, j, hj, hmem, _⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset
      (x := p default) (U := ⊤) (show p default ∈ (⊤ : X.Opens) from trivial)
  let : IsOpenImmersion j := hj
  have hrange : Set.range p ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x default]
    exact hmem
  let q : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec B :=
    IsOpenImmersion.lift j p hrange
  have hq : q ≫ (j ≫ f) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hp]
  obtain ⟨t, ht, htresidue⟩ := exists_affine_section_of_henselian
    R B (IsLocalRing.maximalIdeal R) (j ≫ f) q hq
  have htresidue' : Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ t = q :=
    htresidue
  refine ⟨t ≫ j, ?_, ?_⟩
  · rw [Category.assoc, ht]
  · rw [← Category.assoc, htresidue']
    exact IsOpenImmersion.lift_fac j p hrange

/-- An étale morphism to a strictly local spectrum has a section whenever its
image contains the closed point. Neither module-finiteness nor affineness of
the source is required. -/
theorem exists_section_of_isSepClosed_residueField
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Etale f]
    (x : X) (hx : f x =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) default) :
    ∃ s : Spec (.of R) ⟶ X, s ≫ f = 𝟙 _ := by
  obtain ⟨p, hp, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) x hx
  obtain ⟨s, hs, _⟩ := exists_section_of_henselianLocalRing R f p hp
  exact ⟨s, hs⟩


private theorem localSource_hom_ext_of_residue
    (R : Type u) [CommRing R] [IsLocalRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (a b : Spec (.of R) ⟶ X) (hab : a ≫ f = b ≫ f)
    (hresidue : Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ a =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ b) : a = b := by
  let r : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let pair : Spec (.of R) ⟶ pullback f f := pullback.lift a b hab
  let d : pullback pair (pullback.diagonal f) ⟶ Spec (.of R) :=
    pullback.fst pair (pullback.diagonal f)
  have hd : d ≫ a = d ≫ b := by
    have h₁ := congrArg (fun t => t ≫ pullback.fst f f)
      (pullback.condition (f := pair) (g := pullback.diagonal f))
    have h₂ := congrArg (fun t => t ≫ pullback.snd f f)
      (pullback.condition (f := pair) (g := pullback.diagonal f))
    simp only [pair, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at h₁ h₂
    exact h₁.trans h₂.symm
  let w : Spec (.of (IsLocalRing.ResidueField R)) ⟶
      pullback pair (pullback.diagonal f) :=
    pullback.lift r (r ≫ a) (by
      apply pullback.hom_ext
      · simp only [pair, Category.assoc, pullback.lift_fst,
          pullback.diagonal_fst, Category.comp_id]
      · simp only [pair, Category.assoc, pullback.lift_snd,
          pullback.diagonal_snd, Category.comp_id]
        exact hresidue.symm)
  have hw : w ≫ d = r := pullback.lift_fst _ _ _
  have hmem : IsLocalRing.closedPoint R ∈ d.opensRange := by
    change IsLocalRing.closedPoint R ∈ Set.range d
    refine ⟨w default, ?_⟩
    have hr : r default = IsLocalRing.closedPoint R := by
      change Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) default = _
      rw [Spec.map_apply]
      exact IsLocalRing.PrimeSpectrum.comap_residue R
        (default : Spec (.of (IsLocalRing.ResidueField R)))
    exact (congrArg
      (fun k : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) => k default) hw).trans hr
  have : IsIso d := isIso_of_isOpenImmersion_of_opensRange_eq_top d
    ((IsLocalRing.closedPoint_mem_iff d.opensRange).mp hmem)
  exact (cancel_epi d).mp hd

/-- A prescribed residue-field point of an étale scheme lifts uniquely over
any map from a Henselian local spectrum. The source of the étale morphism
need not be affine: existence uses the existing section theorem after base
change, and uniqueness uses its open diagonal over the local spectrum. -/
theorem existsUnique_lift_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (b : Spec (.of R) ⟶ Y)
    (p : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ b) :
    ∃! s : Spec (.of R) ⟶ X,
      s ≫ f = b ∧ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = p := by
  let r : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let p' : Spec (.of (IsLocalRing.ResidueField R)) ⟶ pullback f b :=
    pullback.lift p r hp
  obtain ⟨s, hs, hresidue⟩ := exists_section_of_henselianLocalRing R
    (pullback.snd f b) p' (pullback.lift_snd _ _ _)
  have hbase : (s ≫ pullback.fst f b) ≫ f = b := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  have hclosed : r ≫ (s ≫ pullback.fst f b) = p := by
    rw [← Category.assoc, hresidue]
    exact pullback.lift_fst _ _ _
  refine ⟨s ≫ pullback.fst f b, ⟨hbase, hclosed⟩, ?_⟩
  intro t ht
  exact localSource_hom_ext_of_residue R f t (s ≫ pullback.fst f b)
    (ht.1.trans hbase.symm) (ht.2.trans hclosed.symm)

end AlgebraicGeometry.Etale
