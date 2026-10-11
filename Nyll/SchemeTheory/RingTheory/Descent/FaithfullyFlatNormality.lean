/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIntegrallyClosed_of_faithfullyFlat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.Ring.RingNF

/-!
# Faithfully flat descent of integral closure

An integral domain is integrally closed when a faithfully flat domain extension is
integrally closed. The proof descends an integral element through the original algebra
map.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.IsIntegrallyClosed_of_faithfullyFlat

theorem _root_.IsIntegrallyClosed.of_faithfullyFlat (A B : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.FaithfullyFlat A B] [IsIntegrallyClosed B] : IsIntegrallyClosed A := by
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  let K := FractionRing A
  let L := FractionRing B
  have hg : Function.Injective ((algebraMap B L).comp (algebraMap A B)) :=
    (IsFractionRing.injective B L).comp hinj
  let φ : K →+* L := IsFractionRing.lift hg
  have hφA : ∀ a : A, φ (algebraMap A K a) = algebraMap A L a := by
    intro a
    rw [IsFractionRing.lift_algebraMap, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  let φₐ : K →ₐ[A] L := { φ with commutes' := hφA }
  refine (isIntegrallyClosed_iff K).mpr ?_
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hy : IsIntegral A (φₐ (algebraMap A K a / algebraMap A K b)) := hx.map φₐ
  have hyB : IsIntegral B (φₐ (algebraMap A K a / algebraMap A K b)) := hy.tower_top
  obtain ⟨β, hβ⟩ := IsIntegrallyClosed.isIntegral_iff.mp hyB
  have hφx : φₐ (algebraMap A K a / algebraMap A K b) = algebraMap A L a / algebraMap A L b := by
    change φ _ = _
    rw [map_div₀, hφA, hφA]
  rw [hφx] at hβ
  have hbL : algebraMap A L b ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B L]
    exact (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr ((map_ne_zero_iff _ hinj).mpr hb0)
  have hβ' : algebraMap B L (β * algebraMap A B b) = algebraMap B L (algebraMap A B a) := by
    rw [map_mul, hβ, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      div_mul_cancel₀ _ hbL]
  have hmem : algebraMap A B a ∈ (Ideal.span {b}).map (algebraMap A B) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨β, by rw [← IsFractionRing.injective B L hβ']; ring⟩
  have ha : a ∈ Ideal.span {b} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (Ideal.span {b}), Ideal.mem_comap]
    exact hmem
  rw [Ideal.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  refine ⟨c, ?_⟩
  have hbK : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb0
  rw [map_mul, eq_div_iff hbK, mul_comm]

namespace COMP
end COMP
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.IsIntegrallyClosed_of_faithfullyFlat
end ProofImplementation
