/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.OpenImmersionLocalization
public import Nyll.SchemeTheory.Morphisms.OpenImmersionQuotient
public import Nyll.SchemeTheory.RingTheory.FiniteOpenFactor
public import Nyll.SchemeTheory.RingTheory.IdempotentLiftSupport
public import Nyll.SchemeTheory.RingTheory.IdempotentQuotientFactor
public import Nyll.SchemeTheory.RingTheory.QuotientBaseChange
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Extracting a finite quotient factor inside an open immersion

A finite open factor of a closed fiber of an affine open immersion is an
actual factor of the target closed fiber. Its defining idempotent has a
representative whose principal open lies in the image of the immersion.
Localizing at that representative makes the original algebra map bijective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgHom

/-- A finite open quotient-fiber factor extends across an affine open immersion,
and a representative of its unit makes the original map an isomorphism after
principal localization. -/
theorem exists_quotient_factor_and_awayMap_bijective
    {R A B D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (I : Ideal R)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    [Algebra (R ⧸ I) D] [Module.Finite (R ⧸ I) D]
    (p : B ⧸ I.map (algebraMap R B) →ₐ[R ⧸ I] D)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom p.toRingHom))] :
    ∃ e : A ⧸ I.map (algebraMap R A), IsIdempotentElem e ∧
      ∃ E : (A ⧸ I.map (algebraMap R A)) ≃ₐ[R ⧸ I]
          D × ((A ⧸ I.map (algebraMap R A)) ⧸ Ideal.span {1 - e}),
        (∀ x, (E x).1 = p (f.quotientBaseChange I x)) ∧
        (∀ x, (E x).2 = Ideal.Quotient.mk (Ideal.span {1 - e}) x) ∧
        ∃ g : A, Ideal.Quotient.mk (I.map (algebraMap R A)) g = 1 - e ∧
          E (Ideal.Quotient.mk (I.map (algebraMap R A)) g) = (1, 0) ∧
          Function.Bijective (Localization.awayMap f.toRingHom g) := by
  let JA : Ideal A := I.map (algebraMap R A)
  let JB : Ideal B := I.map (algebraMap R B)
  let h : A ⧸ JA →ₐ[R ⧸ I] D := p.comp (f.quotientBaseChange I)
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (f.quotientBaseChange I).toRingHom)) :=
    isOpenImmersion_SpecMap_quotientBaseChange f I
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom h.toRingHom)) := by
    change IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (f.quotientBaseChange I).toRingHom ≫
        CommRingCat.ofHom p.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  have hsurj : Function.Surjective h := h.surjective_of_finite_of_isOpenImmersion
  obtain ⟨e, he, hker, E, hE₁, hE₂⟩ :=
    h.exists_prod_quotient_equiv_of_isOpenImmersion hsurj
  let U : Opens (PrimeSpectrum A) := (Spec.map (CommRingCat.ofHom f.toRingHom)).opensRange
  have hrange : Set.range (PrimeSpectrum.comap h.toRingHom) =
      (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum (A ⧸ JA))) := by
    rw [range_comap_of_surjective D h.toRingHom hsurj, hker,
      PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem e he]
  have hU : PrimeSpectrum.basicOpen (1 - e) ≤ Opens.comap
      ⟨PrimeSpectrum.comap (Ideal.Quotient.mk JA),
        PrimeSpectrum.continuous_comap (Ideal.Quotient.mk JA)⟩ U := by
    intro x hx
    have hxrange : x ∈ Set.range (PrimeSpectrum.comap h.toRingHom) := by
      rw [hrange]
      exact hx
    obtain ⟨y, hy⟩ := hxrange
    change PrimeSpectrum.comap (Ideal.Quotient.mk JA) x ∈
      Set.range (PrimeSpectrum.comap f.toRingHom)
    refine ⟨PrimeSpectrum.comap (Ideal.Quotient.mk JB)
      (PrimeSpectrum.comap p.toRingHom y), ?_⟩
    rw [← hy]
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro a
    change p (Ideal.Quotient.mk JB (f a)) ∈ y.asIdeal ↔
      h (Ideal.Quotient.mk JA a) ∈ y.asIdeal
    rfl
  obtain ⟨g, hg, hgU⟩ := PrimeSpectrum.exists_lift_idempotent_basicOpen_le
    JA (1 - e) he.one_sub U hU
  have hezero : h e = 0 := by
    have heker : e ∈ RingHom.ker h.toRingHom := by
      rw [hker]
      exact Ideal.subset_span (Set.mem_singleton_iff.mpr rfl)
    exact heker
  refine ⟨e, he, E, hE₁, hE₂, g, hg, ?_, ?_⟩
  · apply Prod.ext
    · rw [hE₁, hg, map_sub, map_one, hezero, sub_zero]
    · rw [hE₂, hg]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))
  · exact bijective_awayMap_of_basicOpen_le_opensRange
      (CommRingCat.ofHom f.toRingHom) g hgU

end AlgHom
