/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from LFPRingC.exists_ideal_range_comap and
LFPRingC.faithfullyFlat_baseChange_of_map_eq_top at pinned revision:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation.lean#L17-L61
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for copied notices and exact local changes.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Faithfully flat base change on an open spectral image

The spectral image of a flat finitely presented algebra is represented by an ideal. A
base change on which this ideal becomes the unit ideal makes the tensor-product algebra
faithfully flat.
-/

open TensorProduct PrimeSpectrum

/-- The image of a flat finitely presented algebra is the complement of the
zero locus of an ideal of the base. -/
theorem PrimeSpectrum.exists_ideal_range_comap_of_flat_of_finitePresentation
    {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀]
    [Module.Flat A₀ B₀] [Algebra.FinitePresentation A₀ B₀] :
    ∃ 𝔞 : Ideal A₀, ∀ p : PrimeSpectrum A₀,
      p ∈ Set.range (comap (algebraMap A₀ B₀)) ↔ ¬ 𝔞 ≤ p.asIdeal := by
  have hopen : IsOpen (Set.range (comap (algebraMap A₀ B₀))) :=
    (_root_.PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation).isOpen_range
  obtain ⟨𝔞, h𝔞⟩ := (isClosed_iff_zeroLocus_ideal _).mp hopen.isClosed_compl
  refine ⟨𝔞, fun p ↦ ?_⟩
  have hmem : p ∈ (Set.range (comap (algebraMap A₀ B₀)))ᶜ ↔ 𝔞 ≤ p.asIdeal := by
    rw [h𝔞, mem_zeroLocus, SetLike.coe_subset_coe]
  rw [← hmem, Set.mem_compl_iff, not_not]

/-- A flat algebra becomes faithfully flat after a base change whose spectrum
lands in the open image represented by the ideal `𝔞`. The image-containment
hypothesis is explicit; finite presentation is not needed for this step. -/
theorem Module.Flat.faithfullyFlat_baseChange_of_map_eq_top
    {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀]
    [Module.Flat A₀ B₀] (𝔞 : Ideal A₀)
    (h𝔞 : ∀ p : PrimeSpectrum A₀, ¬ 𝔞 ≤ p.asIdeal →
      p ∈ Set.range (comap (algebraMap A₀ B₀)))
    (A' : Type*) [CommRing A'] [Algebra A₀ A'] (htop : 𝔞.map (algebraMap A₀ A') = ⊤) :
    Module.FaithfullyFlat A' (A' ⊗[A₀] B₀) := by
  refine Module.FaithfullyFlat.of_comap_surjective fun q ↦ ?_
  let p : PrimeSpectrum A₀ := comap (algebraMap A₀ A') q
  have hp : p ∈ Set.range (comap (algebraMap A₀ B₀)) := by
    refine h𝔞 p fun hle ↦ q.2.ne_top ?_
    rw [eq_top_iff, ← htop, Ideal.map_le_iff_le_comap]
    exact hle
  rw [← Set.mem_range, ← nontrivial_iff_mem_rangeComap]
  let k := p.asIdeal.ResidueField
  let K := q.asIdeal.ResidueField
  have : Nontrivial (k ⊗[A₀] B₀) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mpr hp
  let φ : k →ₐ[A₀] K :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId A₀ A') rfl
  let : Algebra k K := φ.toRingHom.toAlgebra
  have : IsScalarTower A₀ k K :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  let e₁ : K ⊗[A'] (A' ⊗[A₀] B₀) ≃ₗ[K] K ⊗[A₀] B₀ :=
    _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ A' K K B₀
  let e₂ : K ⊗[k] (k ⊗[A₀] B₀) ≃ₗ[K] K ⊗[A₀] B₀ :=
    _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ k K K B₀
  have : Nontrivial (K ⊗[k] (k ⊗[A₀] B₀)) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right
      (R := k) (M := K) (N := k ⊗[A₀] B₀)).mpr inferInstance
  exact (e₂.toEquiv.trans e₁.symm.toEquiv).symm.nontrivial
