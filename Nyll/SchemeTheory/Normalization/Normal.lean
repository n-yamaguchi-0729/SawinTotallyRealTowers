/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Normal integral schemes

This file provides a focused normality interface for integral schemes.  The
definition is phrased on affine charts, and the basic stalk consequence is
recorded here so that normalization and divisor developments can share the
same notion without importing one another.
-/


noncomputable section

open TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- An integral scheme is normal when its nonempty affine charts are integrally closed. -/
class IsNormalIntegral (X : Scheme.{u}) [IsIntegral X] : Prop where
  /-- The section ring of every nonempty affine chart is integrally closed. -/
  isIntegrallyClosed (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U)

namespace IsNormalIntegral

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]

theorem affine_isIntegrallyClosed (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) :=
  IsNormalIntegral.isIntegrallyClosed U hU

/-- Every local ring of a normal integral scheme is integrally closed. -/
theorem stalk_isIntegrallyClosed (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) (by simp)
  let : Nonempty U := ⟨x, hxU⟩
  let : IsIntegrallyClosed Γ(X, U) :=
    IsNormalIntegral.affine_isIntegrallyClosed U hU
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact isIntegrallyClosed_of_isLocalization
    (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl_le_nonZeroDivisors

/-- A nonempty open subscheme of a normal integral scheme is normal. -/
instance {U : X.Opens} [Nonempty U] : IsNormalIntegral U where
  isIntegrallyClosed V hV := by
    intro hVnonempty
    let : Nonempty V := hVnonempty
    let W : X.Opens := U.ι ''ᵁ V
    have hW : IsAffineOpen W := hV.image_of_isOpenImmersion U.ι
    let : Nonempty W := by
      obtain ⟨v⟩ := (inferInstance : Nonempty V)
      exact ⟨⟨U.ι.base v.1, ⟨v.1, v.2, rfl⟩⟩⟩
    let : IsIntegrallyClosed Γ(X, W) :=
      IsNormalIntegral.affine_isIntegrallyClosed W hW
    exact IsIntegrallyClosed.of_equiv
      (U.ι.appIso V).commRingCatIsoToRingEquiv

end IsNormalIntegral

/-- An integral scheme is normal if all of its local rings are integrally
closed.  This is the stalkwise constructor for `IsNormalIntegral`. -/
theorem IsNormalIntegral.of_stalks
    (X : Scheme.{u}) [IsIntegral X]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsNormalIntegral X where
  isIntegrallyClosed U hU := by
    intro hUnonempty
    let : Nonempty U := hUnonempty
    apply IsIntegrallyClosed.of_isLocalization_maximal
      (fun P [_] ↦ Localization.AtPrime P)
    intro P hP
    let : P.IsMaximal := hP
    let : P.IsPrime := hP.isPrime
    let y : PrimeSpectrum Γ(X, U) := ⟨P, inferInstance⟩
    let x : X := hU.fromSpec y
    have hxU : x ∈ U := (hU.isoSpec.inv y).2
    let : IsIntegrallyClosed (X.presheaf.stalk x) := h x
    let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      (X.presheaf.germ U x hxU).hom.toAlgebra
    let : IsLocalization.AtPrime (X.presheaf.stalk x) P := by
      exact hU.isLocalization_stalk' y hxU
    let e : Localization.AtPrime P ≃ₐ[Γ(X, U)] X.presheaf.stalk x :=
      IsLocalization.algEquiv P.primeCompl
        (Localization.AtPrime P) (X.presheaf.stalk x)
    exact IsIntegrallyClosed.of_equiv e.symm.toRingEquiv

/-- An integral affine scheme whose ring of global sections is integrally
closed is normal.

For an affine open `U`, normality of `Γ(X, U)` is checked at maximal ideals.
The corresponding localizations are the stalks of `X`; those stalks are
localizations of the integrally closed ring `Γ(X, ⊤)`. -/
theorem IsNormalIntegral.of_isAffine
    (X : Scheme.{u}) [IsIntegral X] [IsAffine X]
    [IsIntegrallyClosed Γ(X, ⊤)] :
    IsNormalIntegral X where
  isIntegrallyClosed U hU := by
    intro hUnonempty
    let : Nonempty U := hUnonempty
    apply IsIntegrallyClosed.of_isLocalization_maximal
      (fun P [_] ↦ Localization.AtPrime P)
    intro P hP
    let : P.IsMaximal := hP
    let : P.IsPrime := hP.isPrime
    let y : PrimeSpectrum Γ(X, U) := ⟨P, inferInstance⟩
    let x : X := hU.fromSpec y
    have hxU : x ∈ U := (hU.isoSpec.inv y).2
    let xTop : (⊤ : X.Opens) := ⟨x, by simp⟩
    let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
      (X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
    let : IsLocalization.AtPrime (X.presheaf.stalk x)
        ((isAffineOpen_top X).primeIdealOf xTop).asIdeal :=
      (isAffineOpen_top X).isLocalization_stalk xTop
    have hxNormal : IsIntegrallyClosed (X.presheaf.stalk x) :=
      isIntegrallyClosed_of_isLocalization
        (X.presheaf.stalk x)
        ((isAffineOpen_top X).primeIdealOf xTop).asIdeal.primeCompl
        ((isAffineOpen_top X).primeIdealOf
          xTop).asIdeal.primeCompl_le_nonZeroDivisors
    let : IsIntegrallyClosed (X.presheaf.stalk x) := hxNormal
    let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      (X.presheaf.germ U x hxU).hom.toAlgebra
    let : IsLocalization.AtPrime (X.presheaf.stalk x) P := by
      exact hU.isLocalization_stalk' y hxU
    let e : Localization.AtPrime P ≃ₐ[Γ(X, U)] X.presheaf.stalk x :=
      IsLocalization.algEquiv P.primeCompl
        (Localization.AtPrime P) (X.presheaf.stalk x)
    exact IsIntegrallyClosed.of_equiv e.symm.toRingEquiv

/-- The spectrum of an integrally closed domain is a normal integral
scheme. -/
instance isNormalIntegral_spec (R : CommRingCat.{u})
    [IsDomain R] [IsIntegrallyClosed R] :
    IsNormalIntegral (Spec R) := by
  let : IsIntegrallyClosed Γ(Spec R, ⊤) :=
    IsIntegrallyClosed.of_equiv
      (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  exact IsNormalIntegral.of_isAffine (Spec R)

end AlgebraicGeometry
