/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.FiniteNormalizationModel
import Nyll.SchemeTheory.RingTheory.Descent.FiniteNormalizationNeighborhood
import Nyll.SchemeTheory.RingTheory.Descent.FiniteEtaleNeighborhood
import Nyll.SchemeTheory.RingTheory.Descent.EtalePrimeLocalization
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Spreading finite etale normalizations from base local rings

Finiteness at a point first produces an actual finite subalgebra model.
Its etale locus spreads around the whole fiber, and boundary normality
identifies that model with the integral closure on this neighborhood.
The resulting principal neighborhoods then give global finite generation.
-/

noncomputable section

namespace SchemeTheory

open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A finite etale normalization at one base prime spreads to a principal
neighborhood when the original base is normal along the boundary. -/
theorem exists_finite_etale_integralClosure_away
    {R : Type u} [CommRing R] [IsNoetherianRing R] (d : R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.Away d A]
    (T : Type u) [CommRing T] [Algebra R T] [Algebra A T]
    [IsScalarTower R A T] [Module.Finite A T]
    (p : PrimeSpectrum R)
    [Module.Finite (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R T)]
    [Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R T)]
    (hnormal : ∀ (q : Ideal R) [q.IsPrime], d ∈ q →
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∃ r : R, r ∉ p.asIdeal ∧
      Module.Finite (Localization.Away r)
        (Localization.Away r ⊗[R] integralClosure R T) ∧
      Algebra.Etale (Localization.Away r)
        (Localization.Away r ⊗[R] integralClosure R T) := by
  obtain ⟨C, hCfinite, hCloc, ⟨e⟩⟩ := exists_finite_normalization_model d A T p
  let : Module.Finite R C := hCfinite
  let : IsLocalization.Away (algebraMap R C d) T := hCloc
  let : Algebra.FinitePresentation R C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] C) := Algebra.Etale.of_equiv e.symm
  have hlocal : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl)) :=
    Algebra.Etale.of_equiv (Localization.tensorRightAlgEquiv p.asIdeal.primeCompl C)
  obtain ⟨r, hr, hetale⟩ := exists_etale_away_of_isEtaleAt_fiber p
    (isEtaleAt_of_localizedAlgebra_etale p hlocal)
  let : Algebra.Etale R (Localization.Away (algebraMap R C r)) := hetale
  exact ⟨r, hr, finite_etale_integralClosure_on_model_neighborhood C d r hnormal⟩

private theorem finite_of_finite_tensor_neighborhoods
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (h : ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
      Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] B)) :
    Module.Finite R B := by
  let s : Set R := {r | Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] B)}
  have hspan : Ideal.span s = ⊤ := by
    by_contra hnot
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (Ideal.span s) hnot
    let : p.IsMaximal := hp
    obtain ⟨r, hr, hfinite⟩ := h ⟨p, inferInstance⟩
    exact hr (hle (Ideal.subset_span hfinite))
  exact Module.Finite.of_localizationSpan' s hspan
    (Rₚ := fun r : s => Localization.Away r.val)
    (Mₚ := fun r : s => Localization.Away r.val ⊗[R] B)
    (fun r : s => TensorProduct.mk R (Localization.Away r.val) B 1)
    (fun r : s => r.property)

/-- Pointwise finite etale normalizations over the base local rings glue to
the actual finite etale integral closure. Normality is used only on `V(d)`.
In particular no global normality of the original base is required. -/
theorem finite_etale_integralClosure_of_local_finite_etale
    {R : Type u} [CommRing R] [IsNoetherianRing R] (d : R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.Away d A]
    (T : Type u) [CommRing T] [Algebra R T] [Algebra A T]
    [IsScalarTower R A T] [Module.Finite A T]
    (hnormal : ∀ (p : Ideal R) [p.IsPrime], d ∈ p →
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hlocal : ∀ p : PrimeSpectrum R,
      Module.Finite (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R T) ∧
        Algebra.Etale (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R T)) :
    Module.Finite R (integralClosure R T) ∧ Algebra.Etale R (integralClosure R T) := by
  have hfinite : Module.Finite R (integralClosure R T) := by
    apply finite_of_finite_tensor_neighborhoods
    intro p
    let : Module.Finite (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R T) := (hlocal p).1
    let : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R T) := (hlocal p).2
    obtain ⟨r, hr, hfinite, _⟩ := exists_finite_etale_integralClosure_away d A T p hnormal
    exact ⟨r, hr, hfinite⟩
  let : Module.Finite R (integralClosure R T) := hfinite
  let : Algebra.FinitePresentation R (integralClosure R T) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨hfinite, Algebra.etaleLocus_eq_univ_iff_etale.mp ?_⟩
  apply Set.eq_univ_iff_forall.mpr
  intro Q
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (integralClosure R T)) Q
  let : Algebra.Etale (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R T) := (hlocal p).2
  have hloc : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid (integralClosure R T) p.asIdeal.primeCompl)) :=
    Algebra.Etale.of_equiv
      (Localization.tensorRightAlgEquiv p.asIdeal.primeCompl (integralClosure R T))
  exact isEtaleAt_of_localizedAlgebra_etale p hloc Q rfl

end SchemeTheory
