/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_isReduced_of_smooth_of_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.Basic

/-!
# Reducedness of smooth algebras over fields

The etale generic-fiber argument and local standard-etale presentations prove
reducedness directly. This is the reusable ring part of the pinned FLT proof
previously maintained in AlgebraicCurves.
-/

noncomputable section

open scoped TensorProduct


namespace Algebra.Etale
private theorem _root_.Algebra.Etale.isReduced_of_field
    {K B : Type*} [Field K] [CommRing B] [Algebra K B] [Algebra.Etale K B] :
    IsReduced B := by
  have : Algebra.FormallyUnramified K B :=
    ((Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth).mp
      Algebra.Etale.formallyEtale).1
  have : Algebra.EssFiniteType K B := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K B

end Algebra.Etale
/-- An etale algebra over a domain is reduced, by flat injection into its generic fiber. -/
theorem Algebra.Etale.isReduced_of_isDomain
    {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B] [Algebra.Etale R B] :
    IsReduced B := by
  let K := FractionRing R
  have : Algebra.Etale K (TensorProduct R K B) := inferInstance
  have : IsReduced (TensorProduct R K B) := Algebra.Etale.isReduced_of_field (K := K)
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R K B) := by
    have hRK : Function.Injective (Algebra.linearMap R K) := IsFractionRing.injective R K
    have hrT : Function.Injective (LinearMap.rTensor B (Algebra.linearMap R K)) :=
      Module.Flat.rTensor_preserves_injective_linearMap (Algebra.linearMap R K) hRK
    intro b₁ b₂ hb
    have key : ∀ b : B, (Algebra.TensorProduct.includeRight : B →ₐ[R] _) b
        = LinearMap.rTensor B (Algebra.linearMap R K) (1 ⊗ₜ[R] b) := by
      intro b
      simp only [Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul,
        Algebra.linearMap_apply, map_one]
    rw [key, key] at hb
    simpa only [TensorProduct.lid_tmul, one_smul] using
      congrArg (TensorProduct.lid R B) (hrT hb)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R K B) hinj

namespace Algebra.Smooth
/-- A smooth algebra over a field is reduced, by its standard-etale local presentations. -/
theorem _root_.Algebra.Smooth.isReduced_of_field
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Algebra.Smooth K A] :
    IsReduced A := by
  have hfp : Algebra.FinitePresentation K A := Algebra.Smooth.finitePresentation
  constructor
  intro a ha
  set J : Ideal A := (Ideal.span {a}).annihilator with hJ
  suffices h1 : (1 : A) ∈ J by
    have := (Submodule.mem_annihilator_span_singleton a 1).mp h1
    simpa only [one_smul] using this
  by_contra h1
  have hJne : J ≠ ⊤ := fun h => h1 (h ▸ Submodule.mem_top)
  obtain ⟨m, hm, hsub⟩ := Ideal.exists_le_maximal J hJne
  have : m.IsPrime := hm.isPrime
  have hsa : Algebra.IsSmoothAt K m := by
    have : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus K A := by
      rw [(Algebra.smoothLocus_eq_univ_iff).mpr Algebra.Smooth.formallySmooth]
      exact Set.mem_univ _
    exact this
  have := hsa
  obtain ⟨f, hfm, n, _, hST, hse⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (S := A) (p := m)
  have : Algebra.Etale (MvPolynomial (Fin n) K) (Localization.Away f) := inferInstance
  have hAf : IsReduced (Localization.Away f) :=
    Algebra.Etale.isReduced_of_isDomain (R := MvPolynomial (Fin n) K)
  have hzero : algebraMap A (Localization.Away f) a = 0 :=
    (ha.map (algebraMap A (Localization.Away f))).eq_zero
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ a).mp hzero
  have hfk : f ^ k ∈ J := by
    rw [hJ, Submodule.mem_annihilator_span_singleton]
    rw [smul_eq_mul, hk]
  exact hfm (hm.isPrime.mem_of_pow_mem k (hsub hfk))

end Algebra.Smooth
