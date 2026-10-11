/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianEtaleMapLift
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Etale.Basic

/-!
# Specializing finite étale points through a normal Henselian local ring

For an integral algebra over the base, every point in a normal local ring's
fraction field has a unique factorization through that ring. This uses its
normal self-integral-closure structure, not integrality of the local ring
over the base. For an étale algebra, the existing Henselian section theorem
identifies local-ring points with residue-field points through its actual target-lifting
bijection. Their composite is the actual specialization equivalence, natural
in the finite étale algebra and equivariant for compatible actual actions.
-/

noncomputable section

namespace SchemeTheory

universe u v

section IntegralPoints

variable (H R : Type u) (L : Type v) (T : Type u)
  [CommRing H] [CommRing R] [IsIntegrallyClosed R] [Field L]
  [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]
  [CommRing T] [Algebra H T] [Algebra.IsIntegral H T]

/-- An integral algebra's fraction-field point factors through the actual
normal ring, by its native self-integral-closure constructor. -/
def integralPointLift (f : T →ₐ[H] L) : T →ₐ[H] R where
  toFun a := IsIntegralClosure.mk' R (f a)
    (((Algebra.IsIntegral.isIntegral (R := H) a).map f).tower_top (A := R))
  map_one' := by
    apply IsFractionRing.injective R L
    simp only [IsIntegralClosure.algebraMap_mk', map_one]
  map_zero' := by
    apply IsFractionRing.injective R L
    simp only [IsIntegralClosure.algebraMap_mk', map_zero]
  map_add' a b := by
    apply IsFractionRing.injective R L
    simp only [IsIntegralClosure.algebraMap_mk', map_add]
  map_mul' a b := by
    apply IsFractionRing.injective R L
    simp only [IsIntegralClosure.algebraMap_mk', map_mul]
  commutes' h := by
    apply IsFractionRing.injective R L
    exact (IsIntegralClosure.algebraMap_mk' R (f (algebraMap H T h))
      (((Algebra.IsIntegral.isIntegral (R := H)
        (algebraMap H T h)).map f).tower_top (A := R))).trans
        ((f.commutes h).trans (IsScalarTower.algebraMap_apply H R L h))

theorem integralPointLift_evaluation (f : T →ₐ[H] L) (a : T) :
    algebraMap R L (integralPointLift H R L T f a) = f a :=
  IsIntegralClosure.algebraMap_mk' R (f a)
    (((Algebra.IsIntegral.isIntegral (R := H) a).map f).tower_top (A := R))

/-- Composition with the actual fraction-field inclusion gives a bijection
on points of every integral algebra over the base. -/
def integralPointEquiv : (T →ₐ[H] R) ≃ (T →ₐ[H] L) where
  toFun f := (IsScalarTower.toAlgHom H R L).comp f
  invFun := integralPointLift H R L T
  left_inv f := by
    apply AlgHom.ext
    intro a
    apply IsFractionRing.injective R L
    exact integralPointLift_evaluation H R L T _ a
  right_inv f := by
    apply AlgHom.ext
    intro a
    exact integralPointLift_evaluation H R L T f a

theorem integralPointLift_naturality
    {U : Type u} [CommRing U] [Algebra H U] [Algebra.IsIntegral H U]
    (g : U →ₐ[H] T) (f : T →ₐ[H] L) :
    integralPointLift H R L U (f.comp g) = (integralPointLift H R L T f).comp g := by
  apply AlgHom.ext
  intro a
  apply IsFractionRing.injective R L
  exact (integralPointLift_evaluation H R L U (f.comp g) a).trans
    (integralPointLift_evaluation H R L T f (g a)).symm

end IntegralPoints

section HenselianReduction

variable (H R T : Type u) [CommRing H] [CommRing R] [HenselianLocalRing R]
  [Algebra H R] [CommRing T] [Algebra H T] [Algebra.Etale H T]

/-- The existing Henselian target-lifting bijection, expressed using the
native residue-field algebra and the original base algebra. -/
def henselianPointReductionEquiv :
    (T →ₐ[H] R) ≃ (T →ₐ[H] IsLocalRing.ResidueField R) := by
  let r : R →ₐ[H] IsLocalRing.ResidueField R :=
    IsScalarTower.toAlgHom H R (IsLocalRing.ResidueField R)
  let q : (T →ₐ[H] R) → (T →ₐ[H] IsLocalRing.ResidueField R) := r.comp
  exact Equiv.ofBijective q
    (Algebra.Etale.bijective_comp_quotient_of_henselian_target
      (A := H) (B := T) (S := R) (IsLocalRing.maximalIdeal R))

/-- This equivalence is actual reduction, evaluated on every algebra element. -/
theorem henselianPointReductionEquiv_apply (f : T →ₐ[H] R) (a : T) :
    henselianPointReductionEquiv H R T f a = IsLocalRing.residue R (f a) :=
  RingHom.congr_fun (IsLocalRing.ResidueField.algebraMap_eq (R := R)) (f a)

end HenselianReduction

section ResidueAction

variable (H R : Type u) [CommRing H] [CommRing R] [IsLocalRing R] [Algebra H R]

/-- The native residue-field equivalence of an actual base-linear local-ring
automorphism, with its inherited original base-algebra structure. -/
def residueAlgEquiv (τ : R ≃ₐ[H] R) :
    IsLocalRing.ResidueField R ≃ₐ[H] IsLocalRing.ResidueField R := by
  have : IsLocalHom τ.toRingHom :=
    isLocalHom_of_leftInverse τ.symm.toRingHom (fun r => τ.symm_apply_apply r)
  refine { IsLocalRing.ResidueField.mapEquiv τ.toRingEquiv with commutes' := ?_ }
  intro h
  change (IsLocalRing.ResidueField.mapEquiv τ.toRingEquiv)
    (IsLocalRing.residue R (algebraMap H R h)) =
      IsLocalRing.residue R (algebraMap H R h)
  exact (IsLocalRing.ResidueField.map_residue τ.toRingHom (algebraMap H R h)).trans
    (congrArg (IsLocalRing.residue R) (τ.commutes h))

theorem residueAlgEquiv_residue (τ : R ≃ₐ[H] R) (r : R) :
    residueAlgEquiv H R τ (IsLocalRing.residue R r) = IsLocalRing.residue R (τ r) := by
  have : IsLocalHom τ.toRingHom :=
    isLocalHom_of_leftInverse τ.symm.toRingHom (fun x => τ.symm_apply_apply x)
  exact IsLocalRing.ResidueField.map_residue τ.toRingHom r

end ResidueAction

section Specialization

variable (H R : Type u) (L : Type v) (T : Type u)
  [CommRing H] [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R] [Field L]
  [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]
  [CommRing T] [Algebra H T] [Module.Finite H T] [Algebra.Etale H T]

/-- The actual specialization equivalence from generic points to residue
points of a finite étale algebra, through the given normal Henselian ring. -/
def finiteEtalePointSpecialization :
    (T →ₐ[H] L) ≃ (T →ₐ[H] IsLocalRing.ResidueField R) :=
  (integralPointEquiv H R L T).symm.trans (henselianPointReductionEquiv H R T)

theorem finiteEtalePointSpecialization_apply (f : T →ₐ[H] L) (a : T) :
    finiteEtalePointSpecialization H R L T f a =
      IsLocalRing.residue R (integralPointLift H R L T f a) :=
  henselianPointReductionEquiv_apply H R T _ a

/-- Specialization commutes with the actual morphisms of finite étale algebras. -/
theorem finiteEtalePointSpecialization_naturality
    {U : Type u} [CommRing U] [Algebra H U] [Module.Finite H U] [Algebra.Etale H U]
    (g : U →ₐ[H] T) (f : T →ₐ[H] L) :
    finiteEtalePointSpecialization H R L U (f.comp g) =
      (finiteEtalePointSpecialization H R L T f).comp g := by
  apply AlgHom.ext
  intro a
  exact (finiteEtalePointSpecialization_apply H R L U (f.comp g) a).trans
    ((congrArg (IsLocalRing.residue R)
      (AlgHom.congr_fun (integralPointLift_naturality H R L T g f) a)).trans
        (finiteEtalePointSpecialization_apply H R L T f (g a)).symm)

/-- The same specialization is equivariant for compatible actual automorphisms
of the normal local ring and its fraction field. The residue action is the
native map of residue fields, with no action assumed on the point set. -/
theorem finiteEtalePointSpecialization_equivariant
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (f : T →ₐ[H] L) :
    finiteEtalePointSpecialization H R L T (σ.toAlgHom.comp f) =
      (residueAlgEquiv H R τ).toAlgHom.comp (finiteEtalePointSpecialization H R L T f) := by
  apply AlgHom.ext
  intro a
  have hlift : integralPointLift H R L T (σ.toAlgHom.comp f) a =
      τ (integralPointLift H R L T f a) := by
    apply IsFractionRing.injective R L
    exact (integralPointLift_evaluation H R L T (σ.toAlgHom.comp f) a).trans
      ((congrArg σ (integralPointLift_evaluation H R L T f a).symm).trans
        (hσ (integralPointLift H R L T f a)))
  exact (finiteEtalePointSpecialization_apply H R L T (σ.toAlgHom.comp f) a).trans
    ((congrArg (IsLocalRing.residue R) hlift).trans
      ((residueAlgEquiv_residue H R τ (integralPointLift H R L T f a)).symm.trans
        (congrArg (residueAlgEquiv H R τ)
          (finiteEtalePointSpecialization_apply H R L T f a).symm)))

end Specialization

end SchemeTheory
