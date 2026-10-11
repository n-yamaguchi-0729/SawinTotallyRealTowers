/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.LocalComplement
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Principal affine charts of a divisor complement

The generator of the ideal on an affine chart identifies the actual inverse
image of the support complement with a principal open. The resulting map
from the principal localization forms a pullback square with that complement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)
  {U : X.Opens} (hU : IsAffineOpen U) (d : Γ(X, U))
  (hd : I.ideal ⟨U, hU⟩ = Ideal.span {d})

include hd

/-- Membership in the boundary on an affine principal chart is detected by
the actual generator in its coordinate-ring prime. -/
theorem fromSpec_mem_support_iff_of_ideal_eq_span
    (p : PrimeSpectrum Γ(X, U)) : hU.fromSpec p ∈ I.support ↔ d ∈ p.asIdeal := by
  have hpU : hU.fromSpec p ∈ U := (hU.isoSpec.inv p).property
  rw [I.mem_support_iff_of_mem (U := ⟨U, hU⟩) hpU]
  have hzero := Set.ext_iff.mp (hU.fromSpec_preimage_zeroLocus
    (I.ideal ⟨U, hU⟩ : Set Γ(X, U))) p
  change hU.fromSpec p ∈ X.zeroLocus (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) ↔
    p ∈ PrimeSpectrum.zeroLocus (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) at hzero
  rw [hzero, hd, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
    Ideal.span_le, Set.singleton_subset_iff]
  rfl

/-- The inverse image of a principal divisor complement is the matching
basic open in the spectrum of the affine chart. -/
theorem fromSpec_preimage_supportComplement_of_ideal_eq_span :
    hU.fromSpec ⁻¹ᵁ I.supportComplement = PrimeSpectrum.basicOpen d := by
  apply TopologicalSpace.Opens.ext
  ext p
  exact not_congr (fromSpec_mem_support_iff_of_ideal_eq_span I hU d hd p)

private theorem affineAway_range_subset_supportComplement :
    Set.range (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (Localization.Away d))) ≫ hU.fromSpec) ⊆
      Set.range I.supportComplement.ι := by
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  change Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Localization.Away d))) p ∈
    hU.fromSpec ⁻¹ᵁ I.supportComplement
  rw [fromSpec_preimage_supportComplement_of_ideal_eq_span I hU d hd,
    ← Scheme.Hom.opensRange_localizationAway (R := Γ(X, U)) d]
  exact ⟨p, rfl⟩

/-- The actual map from a principal affine localization into the original
divisor complement. -/
def affineAwayToSupportComplement :
    Spec (.of (Localization.Away d)) ⟶ I.supportComplement :=
  IsOpenImmersion.lift I.supportComplement.ι
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Localization.Away d))) ≫ hU.fromSpec)
    (affineAway_range_subset_supportComplement I hU d hd)

@[reassoc]
theorem affineAwayToSupportComplement_comp_ι :
    affineAwayToSupportComplement I hU d hd ≫ I.supportComplement.ι =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away d))) ≫
        hU.fromSpec :=
  IsOpenImmersion.lift_fac _ _ _

/-- The principal affine localization is the pullback of the original
complement, with its specified map rather than an arbitrary isomorphism. -/
theorem isPullback_affineAwayToSupportComplement :
    IsPullback (affineAwayToSupportComplement I hU d hd)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away d))))
      I.supportComplement.ι hU.fromSpec := by
  apply IsOpenImmersion.isPullback
  · exact (affineAwayToSupportComplement_comp_ι I hU d hd).symm
  · rw [Scheme.Opens.opensRange_ι,
      Scheme.Hom.opensRange_localizationAway (R := Γ(X, U)) d]
    exact fromSpec_preimage_supportComplement_of_ideal_eq_span I hU d hd

end AlgebraicGeometry.Scheme.IdealSheafData
