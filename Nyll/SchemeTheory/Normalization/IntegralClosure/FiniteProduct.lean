/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Integral closure in a finite product

Completion of a finite separable field extension splits its generic fibre as
a finite product of completed fields.  To aggregate local normalization
statements one needs the corresponding integral closure to split coordinatewise.
This file proves that comparison directly from monic equations. For a reduced
Artinian algebra, its canonical product of maximal-ideal quotients then gives
the corresponding product decomposition of its integral closure.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uI uA

/-- An element of a finite product is integral exactly when all of its
coordinates are integral.  The reverse implication uses the product of one
monic annihilating polynomial for each coordinate. -/
theorem isIntegral_pi_iff
    {R : Type uR} {I : Type uI} {A : I → Type uA}
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [Finite I] (x : ∀ i, A i) :
    IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  constructor
  · intro hx i
    exact hx.map (Pi.evalAlgHom R A i)
  · intro hx
    classical
    let := Fintype.ofFinite I
    choose p hpMonic hpRoot using hx
    have hprodMonic : (∏ i, p i).Monic := by
      simpa using
        (Polynomial.monic_prod_of_monic Finset.univ p fun i _ => hpMonic i)
    refine ⟨∏ i, p i, hprodMonic, ?_⟩
    · apply funext
      intro i
      change (∏ j, p j).aeval x i = (0 : A i)
      rw [Polynomial.aeval_pi_apply₂]
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hpRoot i)

/-- Integral closure commutes with finite products, with the canonical
coordinate maps on the nose. -/
noncomputable def integralClosurePiAlgEquiv
    {R : Type uR} {I : Type uI} (A : I → Type uA)
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [Finite I] :
    integralClosure R (∀ i, A i) ≃ₐ[R]
      (∀ i, integralClosure R (A i)) := by
  let forward : integralClosure R (∀ i, A i) →ₐ[R]
      (∀ i, integralClosure R (A i)) :=
    AlgHom.pi fun i =>
      (Pi.evalAlgHom R A i).mapIntegralClosure
  let ambient : (∀ i, integralClosure R (A i)) →ₐ[R] (∀ i, A i) :=
    AlgHom.pi fun i =>
      (integralClosure R (A i)).val.comp
        (Pi.evalAlgHom R (fun i => integralClosure R (A i)) i)
  let backward : (∀ i, integralClosure R (A i)) →ₐ[R]
      integralClosure R (∀ i, A i) :=
    ambient.codRestrict (integralClosure R (∀ i, A i)) fun x =>
      (isIntegral_pi_iff (R := R) (A := A) (fun i => (x i : A i))).2
        fun i => (x i).property
  exact AlgEquiv.ofAlgHom forward backward
    (by
      ext x i
      rfl)
    (by
      ext x i
      rfl)

@[simp]
theorem integralClosurePiAlgEquiv_apply
    {R : Type uR} {I : Type uI} (A : I → Type uA)
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [Finite I] (x : integralClosure R (∀ i, A i)) (i : I) :
    ((integralClosurePiAlgEquiv A x i : integralClosure R (A i)) : A i) =
      (x : ∀ i, A i) i :=
  rfl

/-- If every completed field factor has étale normalization, then the
normalization in their finite product is étale as well. -/
theorem integralClosure_pi_etale
    {R : Type uR} {I : Type uI} (A : I → Type uA)
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [Finite I]
    [∀ i, Algebra.Etale R (integralClosure R (A i))] :
    Algebra.Etale R (integralClosure R (∀ i, A i)) := by
  let : Algebra.Etale R (∀ i, integralClosure R (A i)) := inferInstance
  exact Algebra.Etale.of_equiv (integralClosurePiAlgEquiv A).symm

end EtaleFundamentalGroups

namespace SchemeTheory

universe u v

/-- The normalization of a reduced Artinian algebra is the product of the
normalizations in its actual maximal-ideal quotients. The algebra structures
are the canonical quotient and coordinatewise structures, with scalars
restricted from the Artinian algebra to the original base ring. -/
def integralClosureFactorsEquiv
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [IsArtinianRing A] [IsReduced A] :
    integralClosure R A ≃ₐ[R]
      ∀ m : MaximalSpectrum A, integralClosure R (A ⧸ m.asIdeal) :=
  (((IsArtinianRing.equivPi A).restrictScalars R).mapIntegralClosure).trans
    (EtaleFundamentalGroups.integralClosurePiAlgEquiv
      (R := R) (fun m : MaximalSpectrum A => A ⧸ m.asIdeal))

end SchemeTheory

end
