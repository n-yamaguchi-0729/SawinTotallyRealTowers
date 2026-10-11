/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.RingTheory.Module_Finite_of_ker_le_range_of_isNoetherianRing
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_AffSES_exists_connectingHom

/-!
Cech finiteness of the right term of an affine short exact sequence from the other two terms.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_of_affSES_right

universe u
open AlgebraicGeometry _root_.AlgebraicGeometry.OModulePresheaf in
theorem _root_.AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_right {R : Type u} [CommRing
    R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K :
      V.OrderedAffineCover)
    (h₁ : F₁.CechFinite K) (h₂ : F₂.CechFinite K) : F₃.CechFinite K := by
  obtain ⟨δ₀, δ, h0, hS, -, -⟩ := S.exists_connectingHom K
  refine ⟨?_, fun i => ?_⟩
  · have := h₂.1; have := h₁.2 0
    exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.proj.H0Map K) δ₀ h0
  · have := h₂.2 i; have := h₁.2 (i + 1)
    exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.proj.HSuccMap K i) (δ i) (hS i)
end AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_of_affSES_right
end ProofImplementation
