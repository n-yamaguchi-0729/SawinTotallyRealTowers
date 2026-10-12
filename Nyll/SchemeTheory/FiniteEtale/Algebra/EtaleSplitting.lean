/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

/-
The construction refines Algebra.exists_isFiniteSplit in Christian Merten's pi1.
The upstream repository is Apache-2.0; its KerTensor file has no individual notice.
Source: https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/KerTensor.lean
The stronger etale-neighbourhood statement is a Nyll addition. Its proof adapts
the upstream localization and splitting argument; this is not wholly original code.
-/

module

public import Nyll.SchemeTheory.Pi1.FiniteEtale.Algebra.Equalizer
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TotallySplit

/-!
# Etale splitting neighbourhoods

A finite etale algebra splits over an etale neighbourhood of a prescribed prime.
-/

@[expose] public section

open TensorProduct
universe u
namespace Algebra
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- A finite étale algebra becomes a finite product of the base on an étale
neighbourhood of any prescribed prime. No constant-rank hypothesis is needed. -/
lemma exists_etale_isFiniteSplit [Module.Finite R A] [Algebra.Etale R A]
    (p : PrimeSpectrum R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.Etale R S ∧
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) ∧
      Algebra.IsFiniteSplit S (S ⊗[R] A) := by
  have : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation R A
  obtain ⟨r, hr, hn⟩ := Algebra.exists_cover_rankAtStalk_eq A p.asIdeal
  obtain ⟨p', hp'⟩ : p ∈ Set.range
      (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rwa [PrimeSpectrum.localization_away_comap_range _ r]
  obtain ⟨S, _, _, _, _, _, hS⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hn
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := S) p'
  let : Algebra R S := Algebra.compHom S (algebraMap R (Localization.Away r))
  have : IsScalarTower R (Localization.Away r) S := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨S, inferInstance, inferInstance,
    Algebra.Etale.comp R (Localization.Away r) S, ?_, ?_⟩
  · refine ⟨q, ?_⟩
    rw [IsScalarTower.algebraMap_eq R (Localization.Away r) S, PrimeSpectrum.comap_comp]
    exact (congrArg (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) hq).trans hp'
  · exact IsFiniteSplit.of_algEquiv
      (S := S ⊗[Localization.Away r] (Localization.Away r ⊗[R] A))
      (TensorProduct.cancelBaseChange R (Localization.Away r) S S A)

end Algebra
