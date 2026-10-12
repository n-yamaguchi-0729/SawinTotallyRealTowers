/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.FiniteRadicialSplittingAlgebra
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Algebra.Splitting
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.TotallySplit

/-!
# A finite splitting cover over a finite radicial surjection

The pointwise splitting neighborhoods over the lower ring form an open cover
of its spectrum. Compactness selects finitely many of them. Their product is
faithfully flat over the lower ring, and the finite powers of the individual
neighborhood rings are actual finite étale models of the upper algebra there.

The degrees are allowed to vary, and zero degrees are included. No flatness
or finite-presentation condition is imposed on the finite radicial map.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- A finite affine étale covering of the lower spectrum carries explicit
split finite étale models of the given upper algebra. The product of the
covering algebras is faithfully flat. -/
theorem Etale.exists_finite_split_cover_of_finite_radicial
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Module.Finite R S]
    [Module.Finite S A] [Algebra.Etale S A]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    ∃ (ι : Type u) (_ : Fintype ι) (D : ι → Type u)
      (_ : ∀ i, CommRing (D i)) (_ : ∀ i, Algebra R (D i))
      (_ : ∀ i, Algebra.Etale R (D i)) (n : ι → ℕ),
      Module.FaithfullyFlat R (∀ i, D i) ∧
      (∀ p : PrimeSpectrum R, ∃ i,
        p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (D i)))) ∧
      Module.Finite (∀ i, D i) (∀ i, Fin (n i) → D i) ∧
      Algebra.Etale (∀ i, D i) (∀ i, Fin (n i) → D i) ∧
      (∀ i,
        let C := D i ⊗[R] S;
        let : Algebra S C := Algebra.TensorProduct.rightAlgebra;
        Nonempty ((C ⊗[D i] (Fin (n i) → D i)) ≃ₐ[C] (C ⊗[S] A))) := by
  classical
  choose D hD hRD hEtale hmem hsplit using
    (fun p : PrimeSpectrum R ↦
      Etale.exists_split_algebra_over_finite_radicial (R := R) (S := S) (A := A) p)
  let U (p : PrimeSpectrum R) : Set (PrimeSpectrum R) :=
    Set.range (PrimeSpectrum.comap (algebraMap R (D p)))
  have hopen (p : PrimeSpectrum R) : IsOpen (U p) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation.isOpen_range
  have hcover : Set.univ ⊆ ⋃ p, U p := by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p, hmem p⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  have hfaithful : Module.FaithfullyFlat R (∀ i : t, D i.val) := by
    apply Module.FaithfullyFlat.of_comap_surjective
    intro p
    obtain ⟨i, hi, q, hq⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
    refine ⟨PrimeSpectrum.comap
      (Pi.evalRingHom (fun i : t ↦ D i.val) ⟨i, hi⟩) q, ?_⟩
    exact hq
  have hmodels (i : t) :
      ∃ n : ℕ,
        let C := D i.val ⊗[R] S;
        let : Algebra S C := Algebra.TensorProduct.rightAlgebra;
        Nonempty ((C ⊗[D i.val] (Fin n → D i.val)) ≃ₐ[C] (C ⊗[S] A)) := by
    let C := D i.val ⊗[R] S
    let : Algebra S C := Algebra.TensorProduct.rightAlgebra
    have : Algebra.IsFiniteSplit C (C ⊗[S] A) := hsplit i.val
    obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun C (C ⊗[S] A)
    exact ⟨n, ⟨(Algebra.TensorProduct.piScalarRight (D i.val) C C (Fin n)).trans
      e.symm⟩⟩
  choose n hn using hmodels
  have hfinite : Module.Finite (∀ i : t, D i.val) (∀ i : t, Fin (n i) → D i.val) := by
    apply RingHom.finite_algebraMap.mp
    exact RingHom.finite_ofLocalizationSpan.pi RingHom.finite_respectsIso
      (fun i : t ↦ D i.val) (fun i : t ↦ Fin (n i) → D i.val)
      (fun i : t ↦ algebraMap (D i.val) (Fin (n i) → D i.val))
      (fun i : t ↦ RingHom.finite_algebraMap.mpr inferInstance)
  have hmodelEtale :
      Algebra.Etale (∀ i : t, D i.val) (∀ i : t, Fin (n i) → D i.val) := by
    apply RingHom.etale_algebraMap.mp
    exact RingHom.Etale.ofLocalizationSpan.pi RingHom.Etale.respectsIso
      (fun i : t ↦ D i.val) (fun i : t ↦ Fin (n i) → D i.val)
      (fun i : t ↦ algebraMap (D i.val) (Fin (n i) → D i.val))
      (fun i : t ↦ RingHom.etale_algebraMap.mpr inferInstance)
  refine ⟨t, inferInstance, (fun i : t ↦ D i.val), (fun i : t ↦ hD i.val),
    (fun i : t ↦ hRD i.val), (fun i : t ↦ hEtale i.val), n, hfaithful, ?_, hfinite, hmodelEtale, hn⟩
  intro p
  obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
  exact ⟨⟨i, hi⟩, hpi⟩

end AlgebraicGeometry
