/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.EtaleQuotientLift
public import Nyll.SchemeTheory.FiniteEtale.Algebra.IdempotentFactor
public import Nyll.SchemeTheory.Normalization.QuotientFiniteFactor
public import Nyll.SchemeTheory.RingTheory.HenselianIdempotents
public import Nyll.SchemeTheory.RingTheory.IdempotentFactorReduction
public import Nyll.SchemeTheory.RingTheory.JacobsonIdempotentFactor
public import Nyll.SchemeTheory.RingTheory.LocalizationIdempotentFactor
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Lifting finite étale algebras over Henselian pairs

First lift the étale presentation. Its finite special fiber selects a factor
of the integral closure on a principal neighborhood. Lift the corresponding
idempotent using the Henselian pair, and transport its factor through that
localization. The resulting factor of the étale lift is integral, hence finite,
and still has the prescribed special fiber.
-/

@[expose] public section

open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Algebra.FiniteEtale

/-- Every finite étale algebra over the quotient of a Henselian pair is the
reduction of a finite étale algebra over the original ring. -/
theorem exists_lift_of_quotient_of_henselian
    {R A : Type u} [CommRing R] [CommRing A] (I : Ideal R) [HenselianRing R I]
    [Algebra (R ⧸ I) A] [Module.Finite (R ⧸ I) A] [Algebra.Etale (R ⧸ I) A] :
    ∃ B : CommAlgCat.{u} R, Module.Finite R B ∧ Algebra.Etale R B ∧
      Nonempty ((R ⧸ I) ⊗[R] B ≃ₐ[R ⧸ I] A) := by
  obtain ⟨D, hD, ⟨α⟩⟩ := Algebra.Etale.exists_etale_lift_of_quotient (A := A) I
  let : Algebra.Etale R D := hD
  let JD : Ideal (D : Type u) := I.map (algebraMap R D)
  let p : @HasQuotient.Quotient (D : Type u) (Ideal (D : Type u)) inferInstance JD ≃ₐ[R ⧸ I] A :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor D I).trans α
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom p.toAlgHom.toRingHom)) := by
    let : CategoryTheory.IsIso (CommRingCat.ofHom p.toAlgHom.toRingHom) :=
      p.toRingEquiv.toCommRingCatIso.isIso_hom
    infer_instance
  let C := integralClosure R D
  let J : Ideal C := I.map (algebraMap R C)
  let qC : C →+* C ⧸ J := Ideal.Quotient.mk J
  let qD : D →+* @HasQuotient.Quotient (D : Type u) (Ideal (D : Type u)) inferInstance JD :=
    Ideal.Quotient.mk (I.map (algebraMap R D))
  let f : C →ₐ[R] D := (integralClosure R D).val
  obtain ⟨e₀, he₀, E, hE₁, _, g, hg, hEg, hlocal⟩ :=
    Algebra.exists_integralClosure_quotient_factor_and_awayMap_bijective I p.toAlgHom
  have hgidem : IsIdempotentElem (qC g) := by
    rw [hg]
    exact he₀.one_sub
  obtain ⟨e, he, heq⟩ := Algebra.exists_idempotent_lift_of_isIntegral I g hgidem
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {1 - e}) g) :=
    Algebra.isUnit_quotient_one_sub_of_eq_mod_extendedIdeal I
      (HenselianRing.jac (R := R) (I := I)) g e heq.symm
  have hpg : p (qD (f g)) = 1 := by
    have h := congrArg Prod.fst hEg
    rw [hE₁] at h
    exact h
  have hpe : p (qD (f e)) = 1 := by
    have h := congrArg (p.toAlgHom.comp (f.quotientBaseChange I)) heq
    change p (qD (f e)) = p (qD (f g)) at h
    exact h.trans hpg
  have hfe : qD (f e) = 1 := by
    apply p.injective
    rw [map_one]
    exact hpe
  let F := D ⧸ Ideal.span {1 - f e}
  let : Algebra.Etale R F :=
    Algebra.Etale.quotient_one_sub_of_isIdempotentElem (f e) (he.map f)
  let : Algebra.IsIntegral R F :=
    f.isIntegral_idempotentFactor_of_awayMap_bijective e he g hunit hlocal
  let : Module.Finite R F := Algebra.IsIntegral.finite
  refine ⟨CommAlgCat.of R F, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor F I).symm.trans
    ((Algebra.idempotentFactorReductionEquivOfEqOne I (f e) hfe).trans p)

end Algebra.FiniteEtale
