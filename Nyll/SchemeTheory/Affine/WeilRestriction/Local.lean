/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.GlobalFiniteEtale
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Local finite étale internal Homs

A finite projective module becomes free after localizing at a suitable
element outside any prescribed prime. We express this freeness using tensor
products, so that the finite free Weil restriction construction applies.

For finite étale `R`-algebras `A` and `B`, this gives an actual finite étale
internal Hom over a principal neighborhood of every point of `Spec R`.
No global freeness assumption on `A` is needed.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

universe u

namespace SchemeTheory.Affine

/-- A finite projective module is free on a principal neighborhood of any
prime, expressed as a tensor product with the localized base ring. -/
lemma exists_free_tensor_away_of_projective
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧
      Module.Free (Localization.Away r) (Localization.Away r ⊗[R] M) := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (Localization.AtPrime p.asIdeal)
  let : Module.Free (Localization.Away r) (LocalizedModule.Away r M) := hfree
  refine ⟨r, hr, ?_⟩
  exact Module.Free.of_equiv
    (IsLocalizedModule.isBaseChange (Submonoid.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) M)).equiv.symm

/-- Around every prime of `R`, the relative internal Hom of finite étale
`R`-algebras is represented by a finite étale scheme over a principal
localization of `R`. The representing equivalence holds for every test
scheme over that localization. -/
theorem exists_finiteEtaleInternalHomRepresentable_away
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R B] [Algebra.Etale R B] (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧
      ∃ W : FiniteEtale (Spec (CommRingCat.of (Localization.Away r))),
        Nonempty ((globalInternalHomFunctor
          (R := Localization.Away r)
          (A := Localization.Away r ⊗[R] A)
          (B := Localization.Away r ⊗[R] B)).RepresentableBy
            ((FiniteEtale.forget (Spec (CommRingCat.of (Localization.Away r)))).obj W)) := by
  let : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation R A
  let : Module.Projective R A := Module.Flat.projective_of_finitePresentation
  obtain ⟨r, hr, hfree⟩ := exists_free_tensor_away_of_projective (M := A) p
  let : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] A) := hfree
  exact ⟨r, hr,
    finiteEtaleInternalHomRepresenter
      (R := Localization.Away r)
      (A := Localization.Away r ⊗[R] A)
      (B := Localization.Away r ⊗[R] B),
    ⟨finiteEtaleInternalHomRepresentable
      (R := Localization.Away r)
      (A := Localization.Away r ⊗[R] A)
      (B := Localization.Away r ⊗[R] B)⟩⟩

end SchemeTheory.Affine
