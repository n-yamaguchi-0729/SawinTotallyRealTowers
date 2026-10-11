/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.JacobianLocalization
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.MvPolynomial.Tower
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Lifting étale algebras through a surjective base map

For a surjective map `R₀ → R` and an étale `R`-algebra `S`, we construct an
étale `R₀`-algebra whose base change is `S`. The construction uses mathlib's
relative-dimension-zero submersive presentation, lifts its polynomial
coefficients, and inverts the Jacobian of the resulting model.

The Jacobian maps to a unit in the original algebra, so this localization
does not change the base change. Both the étale property and the algebra
isomorphism are proved from the construction. No noetherian, field, or
nilpotence hypothesis is used. This is the affine lifting step needed for
comparing étale neighborhoods along a closed immersion.
-/

@[expose] public section

noncomputable section

universe u₀ u v w t

open Algebra TensorProduct

namespace Algebra.Etale

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t}
  [CommRing R] [CommRing S] [Algebra R S] [Finite σ]
  (P : PreSubmersivePresentation R S ι σ)

section Coefficients

variable (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S]
  [IsScalarTower R₀ R S] [P.HasCoeffs R₀]

/-- The Jacobian of the coefficient model becomes the original Jacobian after base change. -/
lemma tensorModel_jacobian :
    P.tensorModelOfHasCoeffsEquiv R₀
      (1 ⊗ₜ[R₀] (P.ofHasCoeffs R₀).jacobian) = P.jacobian := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  have hm : (MvPolynomial.map (algebraMap R₀ R)).mapMatrix (P.ofHasCoeffs R₀).jacobiMatrix =
      P.jacobiMatrix := by
    funext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      PreSubmersivePresentation.jacobiMatrix_apply,
      PreSubmersivePresentation.ofHasCoeffs_map,
      PreSubmersivePresentation.ofHasCoeffs_relation,
      ← MvPolynomial.pderiv_map, Presentation.map_relationOfHasCoeffs]
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  change P.tensorModelOfHasCoeffsEquiv R₀
    (1 ⊗ₜ[R₀] Ideal.Quotient.mk _ (P.ofHasCoeffs R₀).jacobiMatrix.det) = P.jacobian
  rw [Presentation.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul,
    ← MvPolynomial.aeval_map_algebraMap R, RingHom.map_det, hm]
  exact (P.toGenerators.algebraMap_apply P.jacobiMatrix.det).symm.trans
    P.jacobian_eq_jacobiMatrix_det.symm

end Coefficients

section Lift

variable (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S]
  [IsScalarTower R₀ R S] (Q : SubmersivePresentation R S ι σ)
  [Q.toPresentation.HasCoeffs R₀]

/-- The coefficient model, localized at its Jacobian, still recovers the given algebra. -/
def tensorJacobianModelEquiv :
    R ⊗[R₀] Localization.Away (Q.toPreSubmersivePresentation.ofHasCoeffs R₀).jacobian ≃ₐ[R] S := by
  let M := Q.toPresentation.ModelOfHasCoeffs R₀
  let g : M := (Q.toPreSubmersivePresentation.ofHasCoeffs R₀).jacobian
  let e : R ⊗[R₀] M ≃ₐ[R] S := Q.toPresentation.tensorModelOfHasCoeffsEquiv R₀
  have hg : IsUnit ((1 : R) ⊗ₜ[R₀] g) := by
    apply (MulEquiv.isUnit_map (f := e.toRingEquiv.toMulEquiv)).mp
    change IsUnit (Q.toPresentation.tensorModelOfHasCoeffsEquiv R₀
      (1 ⊗ₜ[R₀] (Q.toPreSubmersivePresentation.ofHasCoeffs R₀).jacobian))
    rw [tensorModel_jacobian]
    exact Q.jacobian_isUnit
  exact (IsLocalization.Away.tensorProductEquivTMulRight R₀ R g (Localization.Away g)).trans
    (((IsLocalization.atUnit (R ⊗[R₀] M) (Localization.Away ((1 : R) ⊗ₜ[R₀] g))
      ((1 : R) ⊗ₜ[R₀] g) hg).symm.restrictScalars R).trans e)

end Lift

/-- Every étale algebra over a quotient lifts to an étale algebra over the original ring. -/
lemma exists_etale_lift_of_surjective (R₀ : Type u₀) [CommRing R₀]
    [Algebra R₀ R]
    (h : Function.Surjective (algebraMap R₀ R)) [Algebra.Etale R S] :
    ∃ (T : Type u₀) (_ : CommRing T) (_ : Algebra R₀ T),
      Algebra.Etale R₀ T ∧ Nonempty (R ⊗[R₀] T ≃ₐ[R] S) := by
  let : Algebra R₀ S := ((algebraMap R S).comp (algebraMap R₀ R)).toAlgebra
  have : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' rfl
  have : IsStandardSmoothOfRelativeDimension 0 R S :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  obtain ⟨I, J, _, _, Q, hQ⟩ :=
    IsStandardSmoothOfRelativeDimension.out (n := 0) (R := R) (S := S)
  have : Q.toPresentation.HasCoeffs R₀ := ⟨fun r _ => h r⟩
  let Q₀ := Q.toPreSubmersivePresentation.ofHasCoeffs R₀
  refine ⟨Localization.Away Q₀.jacobian, inferInstance, inferInstance,
    PreSubmersivePresentation.jacobianLocalization_etale Q₀ ?_, ⟨tensorJacobianModelEquiv R₀ Q⟩⟩
  exact hQ

/-- Every étale algebra over an arbitrary quotient is the reduction of an étale algebra
over the original ring. The constructed lift need not be finite as a module. -/
@[stacks 04D1]
theorem exists_etale_lift_of_quotient
    {R A : Type u} [CommRing R] [CommRing A] (I : Ideal R)
    [Algebra (R ⧸ I) A] [Algebra.Etale (R ⧸ I) A] :
    ∃ C : CommAlgCat.{u} R, Algebra.Etale R C ∧
      Nonempty ((R ⧸ I) ⊗[R] C ≃ₐ[R ⧸ I] A) := by
  obtain ⟨T, _, _, hT, hEquiv⟩ :=
    exists_etale_lift_of_surjective (R := R ⧸ I) (S := A) R
      Ideal.Quotient.mk_surjective
  exact ⟨CommAlgCat.of R T, hT, hEquiv⟩

end Algebra.Etale
