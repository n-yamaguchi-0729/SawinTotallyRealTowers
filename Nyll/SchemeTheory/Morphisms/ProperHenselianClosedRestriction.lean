/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.SchemeTheory.Morphisms.ProperIntegralHenselianConnectedFiber
import Nyll.SchemeTheory.Divisors.Reduced
import Nyll.SchemeTheory.Topology.SpectralClosedRestriction
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Irreducible

/-!
# Closed-fiber intersections and constant sections of arbitrary proper schemes

For every irreducible closed subset, its actual reduced induced subscheme is
integral and proper over the base. Applying connectedness to that scheme
supplies the point-closure condition in Stacks 09ZG. The existing spectral
restriction theorem then extends every locally constant function from the
closed fiber of an arbitrary proper scheme. No integrality assumption is
made on the ambient proper scheme, including finite refinements of it.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

/-- Every nonempty irreducible closed subset of an arbitrary proper scheme
meets the henselian closed fiber in a connected nonempty subset. -/
theorem isConnected_closedFiber_inter_of_isIrreducible
    (C : Set X) (hC : IsClosed C) (hIrreducible : IsIrreducible C) :
    _root_.IsConnected ((f ⁻¹' {IsLocalRing.closedPoint R}) ∩ C) := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩
  have : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact Subtype.irreducibleSpace hIrreducible
  have hReduced : I.IsReduced := by
    rw [Scheme.IdealSheafData.IsReduced]
    ext U : 2
    exact (PrimeSpectrum.isRadical_vanishingIdeal _).radical
  have : IsReduced I.subscheme := hReduced.subscheme
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced I.subscheme
  have h := (isConnected_preimage_closedPoint_of_isProper_of_isIntegral
    (I.subschemeι ≫ f)).image I.subschemeι I.subschemeι.continuous.continuousOn
  change _root_.IsConnected
    (I.subschemeι '' (I.subschemeι ⁻¹' (f ⁻¹' {IsLocalRing.closedPoint R}))) at h
  rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal] at h
  exact h

/-- The actual point-closure condition needed in the spectral restriction
theorem is supplied for every point of the original proper scheme. -/
theorem isConnected_closedFiber_inter_closure (x : X) :
    _root_.IsConnected
      ((f ⁻¹' {IsLocalRing.closedPoint R}) ∩ closure ({x} : Set X)) :=
  isConnected_closedFiber_inter_of_isIrreducible f (closure ({x} : Set X))
    isClosed_closure isIrreducible_singleton.closure

/-- Every locally constant function on the actual closed fiber extends
uniquely to the arbitrary proper scheme. The value type need not be finite. -/
theorem locallyConstant_closedFiber_restriction_bijective (S : Type*) :
    Function.Bijective (LocallyConstant.comap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(f ⁻¹' {IsLocalRing.closedPoint R}, X)) :
        LocallyConstant X S → LocallyConstant (f ⁻¹' {IsLocalRing.closedPoint R}) S) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : SpectralSpace X := {}
  exact SchemeTheory.locallyConstant_restriction_bijective
    ((IsLocalRing.isClosed_singleton_closedPoint (R := R)).preimage f.continuous)
    (isConnected_closedFiber_inter_closure f) S

end AlgebraicGeometry
