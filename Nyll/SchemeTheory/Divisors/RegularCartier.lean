/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.SubschemeStalk
import Nyll.SchemeTheory.RingTheory.RegularLocalQuotientLift
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Ambient regularity along a regular Cartier divisor

A regular effective Cartier divisor in a locally Noetherian scheme forces
the ambient local rings along its support to be regular. The proof uses the
actual quotient description of the divisor's stalk and the regularity
lifting theorem for a quotient by a non-zero-divisor.

This supplies the regular-local-ring step in the proof of
[Stacks Project, Tag 0EYE](https://stacks.math.columbia.edu/tag/0EYE), using
the one-element case of [Tag 00NU](https://stacks.math.columbia.edu/tag/00NU).
The stalk-generator lemma was moved here from
`EtaleFundamentalGroups.LocalGeometry.HeightOne.CartierComponentStalkDVR`
with its statement, proof, and authorship preserved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- An effective Cartier ideal has a regular generator in every stalk.
The affine Cartier equation remains regular because the germ map is a flat
localization; the defining affine ideal maps to the stalk ideal. -/
theorem IsEffectiveCartier.exists_regular_stalkIdeal_generator
    {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsEffectiveCartier)
    (x : X) :
    ∃ a : X.presheaf.stalk x, IsRegular a ∧ I.stalkIdeal x = Ideal.span {a} := by
  obtain ⟨U, hxU, f, hf, hIf⟩ := hI x
  let R := X.presheaf.stalk x
  let A := Γ(X, U.1)
  let a : R := X.presheaf.germ U.1 x hxU f
  let : Algebra A R := (X.presheaf.germ U.1 x hxU).hom.toAlgebra
  let P : Ideal A := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : P.IsPrime := (U.2.primeIdealOf ⟨x, hxU⟩).isPrime
  let : IsLocalization.AtPrime R P := U.2.isLocalization_stalk ⟨x, hxU⟩
  let : Module.Flat A R := IsLocalization.flat R P.primeCompl
  have hareg : IsSMulRegular R a := IsSMulRegular.of_flat (S := R) hf.left
  refine ⟨a, (Commute.isRegular_iff (Commute.all a)).mpr hareg, ?_⟩
  change I.stalkIdeal x = Ideal.span {X.presheaf.germ U.1 x hxU f}
  rw [I.stalkIdeal_eq_map_ideal x U hxU, hIf,
    Ideal.map_span, Set.image_singleton]

/-- If the closed subscheme of an effective Cartier ideal is regular,
then the ambient scheme is regular at each point of its support. -/
theorem IsEffectiveCartier.isAmbientRegularAlongSupport_of_regular_subscheme
    {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier)
    (hregular : ∀ z : I.subscheme,
      IsRegularLocalRing (I.subscheme.presheaf.stalk z)) :
    I.IsAmbientRegularAlongSupport := by
  intro x hx
  have hx' : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hx
  obtain ⟨z, rfl⟩ := hx'
  let R := X.presheaf.stalk (I.subschemeι z)
  have : IsRegularLocalRing (I.subscheme.presheaf.stalk z) := hregular z
  have : IsRegularLocalRing (R ⧸ I.stalkIdeal (I.subschemeι z)) :=
    IsRegularLocalRing.of_ringEquiv (I.subschemeStalkQuotientEquiv z).symm
  obtain ⟨a, ha, hIa⟩ := hI.exists_regular_stalkIdeal_generator (I.subschemeι z)
  have hquot : IsRegularLocalRing (R ⧸ Ideal.span {a}) := by
    rw [← hIa]
    infer_instance
  have hamem : a ∈ maximalIdeal R :=
    I.stalkIdeal_le_maximalIdeal_of_mem_support (I.subschemeι z)
      (by rw [← SetLike.mem_coe, ← I.range_subschemeι]; exact Set.mem_range_self z) (by
        rw [hIa]
        exact Ideal.mem_span_singleton_self a)
  exact SchemeTheory.isRegularLocalRing_of_quotient_span_singleton R a hamem ha.left

end AlgebraicGeometry.Scheme.IdealSheafData
