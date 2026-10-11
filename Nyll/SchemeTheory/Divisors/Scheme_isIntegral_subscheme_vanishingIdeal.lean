/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties

/-!
# The integral subscheme of an irreducible closed set

The vanishing ideal of an irreducible closed set defines an integral subscheme with that
closed set as its support.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_isIntegral_subscheme_vanishingIdeal

open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IntegralSubscheme
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry
universe u
section IntegralSubscheme

variable {V : Scheme.{u}}

theorem isReduced_vanishingIdeal (Z : Closeds V) :
    IsReduced (IdealSheafData.vanishingIdeal Z).subscheme := by
  have hchart : ∀ U : V.affineOpens,
      IsReduced ((IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X U) := by
    intro U
    change IsReduced (Spec (CommRingCat.of
      (Γ(V, U.1) ⧸ (IdealSheafData.vanishingIdeal Z).ideal U)))
    rw [affine_isReduced_iff]
    have hrad : ((IdealSheafData.vanishingIdeal Z).ideal U).IsRadical := by
      rw [IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    constructor
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨n, hn⟩ := hx
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrad ⟨n, hn⟩)
  have : ∀ U : (IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.I₀,
      IsReduced ((IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X U) :=
    fun U => hchart U
  exact AlgebraicGeometry.IsReduced.of_openCover
    (X := (IdealSheafData.vanishingIdeal Z).subscheme)
    (IdealSheafData.vanishingIdeal Z).subschemeCover.openCover

theorem support_vanishingIdeal (Z : Closeds V) :
    (IdealSheafData.vanishingIdeal Z).support = Z := by
  exact SetLike.coe_injective (IdealSheafData.coe_support_vanishingIdeal Z)

theorem irreducible_vanishingIdeal (Z : Closeds V)
    (hZ : IsIrreducible (Z : Set V)) :
    IrreducibleSpace (IdealSheafData.vanishingIdeal Z).subscheme := by
  exact Subtype.irreducibleSpace hZ

theorem isIntegral_vanishingIdeal (Z : Closeds V)
    (hZ : IsIrreducible (Z : Set V)) :
    IsIntegral (IdealSheafData.vanishingIdeal Z).subscheme := by
  have := isReduced_vanishingIdeal Z
  have := irreducible_vanishingIdeal Z hZ
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end IntegralSubscheme
end AlgebraicGeometry.Scheme.IntegralSubscheme

universe u
with_weak_namespace _root_.AlgebraicCurves.Geometry.Schemes.Proofs
open _root_.AlgebraicGeometry Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry
    TopologicalSpace in
with_weak_namespace Scheme_isIntegral_subscheme_vanishingIdeal
theorem _root_.AlgebraicGeometry.Scheme.isIntegral_subscheme_vanishingIdeal {V : Scheme.{u}} (Z
    : Closeds V) (hZ : IsIrreducible (Z : Set V)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  AlgebraicGeometry.Scheme.IntegralSubscheme.isIntegral_vanishingIdeal Z hZ
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_isIntegral_subscheme_vanishingIdeal
end ProofImplementation
