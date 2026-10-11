/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_CoherentBaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
Finite free two-term complexes, their fibre dimensions and the canonical kernel base-change map.
-/

noncomputable section

open scoped TensorProduct

universe u v w

namespace CoherentBaseChange

/-- A two-term complex of finite free R-modules in degrees zero and one. -/
structure TwoTermComplex (R : Type u) [CommRing R] where
  /-- The underlying type of the degree-zero module. -/
  C0 : Type v
  /-- The additive commutative group structure on the degree-zero module. -/
  [C0_addCommGroup : AddCommGroup C0]
  /-- The R-module structure on the degree-zero module. -/
  [C0_module : Module R C0]
  /-- The degree-zero module is finitely generated over R. -/
  [C0_finite : Module.Finite R C0]
  /-- The degree-zero module is free over R. -/
  [C0_free : Module.Free R C0]
  /-- The underlying type of the degree-one module. -/
  C1 : Type v
  /-- The additive commutative group structure on the degree-one module. -/
  [C1_addCommGroup : AddCommGroup C1]
  /-- The R-module structure on the degree-one module. -/
  [C1_module : Module R C1]
  /-- The degree-one module is finitely generated over R. -/
  [C1_finite : Module.Finite R C1]
  /-- The degree-one module is free over R. -/
  [C1_free : Module.Free R C1]
  /-- The differential from degree zero to degree one. -/
  d : C0 →ₗ[R] C1

attribute [instance] TwoTermComplex.C0_addCommGroup TwoTermComplex.C0_module
  TwoTermComplex.C0_finite TwoTermComplex.C0_free TwoTermComplex.C1_addCommGroup
  TwoTermComplex.C1_module TwoTermComplex.C1_finite TwoTermComplex.C1_free

namespace TwoTermComplex

variable {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)

/-- The dimension of the kernel after base change to the residue field at the given prime. -/
def fibreH0 (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField
    (LinearMap.ker (G.d.baseChange 𝔭.asIdeal.ResidueField))

/-- The dimension of the cokernel after base change to the residue field at the given prime. -/
def fibreH1 (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField
    ((𝔭.asIdeal.ResidueField ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange 𝔭.asIdeal.ResidueField))

/-- The Euler characteristic given by the degree-zero rank minus the degree-one rank. -/
def chi : ℤ :=
  (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ)

/-- The kernel of the differential after base change to A. -/
abbrev H0 (A : Type w) [CommRing A] [Algebra R A] : Submodule A (A ⊗[R] G.C0) :=
  LinearMap.ker (G.d.baseChange A)

/-- The natural map from the base change of the original kernel to the kernel of the
base-changed differential. -/
def kerBaseChangeHom (A : Type w) [CommRing A] [Algebra R A] :
    A ⊗[R] (LinearMap.ker G.d) →ₗ[A] G.H0 A :=
  ((LinearMap.ker G.d).subtype.baseChange A).codRestrict (LinearMap.ker (G.d.baseChange A))
    (fun x => by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have h : G.d ∘ₗ (LinearMap.ker G.d).subtype = 0 := by
        ext ⟨y, hy⟩
        exact hy
      rw [h, LinearMap.baseChange_zero, LinearMap.zero_apply])

theorem kerBaseChangeHom_apply_coe (A : Type w) [CommRing A] [Algebra R A]
    (x : A ⊗[R] (LinearMap.ker G.d)) :
    (G.kerBaseChangeHom A x : A ⊗[R] G.C0) = (LinearMap.ker G.d).subtype.baseChange A x :=
  rfl

end TwoTermComplex

end CoherentBaseChange
