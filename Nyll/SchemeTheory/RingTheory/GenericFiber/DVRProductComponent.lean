/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.GenericFiber.ChosenComponentFractionRing
import Nyll.SchemeTheory.Normalization.Products.DVRPrimeBelowCoordinate

/-!
# Chosen generic components of a product of DVRs

For a generic fibre of a product of DVRs, a maximal ideal whose contraction
lies strictly below a specified coordinate maximal prime selects the fraction
field of that same coordinate.  The kernel identification is produced by the
prime structure of the DVR factor, rather than supplied as an assumption.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uK uι uA

variable {R : Type uR} {K : Type uK} {ι : Type uι}
variable (A : ι → Type uA)
variable [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
variable [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)]
variable [∀ j, IsDiscreteValuationRing (A j)]
variable [∀ j, Algebra R (A j)]

/-- A chosen generic component lying strictly below the maximal prime of the
`i`-th DVR factor is canonically the fraction field of that factor. -/
noncomputable def genericFiberDVRProductComponentFractionRingEquiv
    (i : ι) (m : Ideal (K ⊗[R] (∀ j, A j))) [m.IsMaximal]
    (hNP : genericFiberComponentBaseIdeal m ≤
      productCoordinatePrime A i)
    (hNne : genericFiberComponentBaseIdeal m ≠
      productCoordinatePrime A i) :
    ((K ⊗[R] (∀ j, A j)) ⧸ m) ≃+* FractionRing (A i) := by
  let U := ∀ j, A j
  let G := K ⊗[R] U
  let N := genericFiberComponentBaseIdeal m
  let Ω := G ⧸ m
  let f : U →+* A i := Pi.evalRingHom A i
  letI : m.IsPrime :=
    Ideal.IsMaximal.isPrime (inferInstance : m.IsMaximal)
  letI : N.IsPrime := (inferInstance : m.IsPrime).comap
    (Algebra.TensorProduct.includeRight : U →ₐ[R] G).toRingHom
  have hker : N = RingHom.ker f :=
    prime_eq_ker_coordinateEval_of_le_of_ne A i N hNP hNne
  let eN : (U ⧸ N) ≃+* A i :=
    (Ideal.quotientEquivAlgOfEq ℤ hker).toRingEquiv.trans
      (RingHom.quotientKerEquivOfSurjective f.surjective)
  letI : Field Ω := Ideal.Quotient.field m
  letI : Algebra (U ⧸ N) Ω :=
    (genericFiberComponentQuotientRingHom m).toAlgebra
  letI : IsFractionRing (U ⧸ N) Ω :=
    genericFiberComponentQuotient_isFractionRing m
  exact IsFractionRing.ringEquivOfRingEquiv
    (K := Ω) (L := FractionRing (A i)) eN

/-- The coordinate identification sends the image of a tuple to the usual
image of its selected coordinate in the fraction field. -/
@[simp]
theorem genericFiberDVRProductComponentFractionRingEquiv_quotient_mk
    (i : ι) (m : Ideal (K ⊗[R] (∀ j, A j))) [m.IsMaximal]
    (hNP : genericFiberComponentBaseIdeal m ≤
      productCoordinatePrime A i)
    (hNne : genericFiberComponentBaseIdeal m ≠
      productCoordinatePrime A i)
    (x : ∀ j, A j) :
    genericFiberDVRProductComponentFractionRingEquiv A i m hNP hNne
        (genericFiberComponentQuotientRingHom m
          (Ideal.Quotient.mk (genericFiberComponentBaseIdeal m) x)) =
      algebraMap (A i) (FractionRing (A i)) (x i) := by
  let U := ∀ j, A j
  let G := K ⊗[R] U
  let N := genericFiberComponentBaseIdeal m
  let Ω := G ⧸ m
  let f : U →+* A i := Pi.evalRingHom A i
  let : m.IsPrime :=
    Ideal.IsMaximal.isPrime (inferInstance : m.IsMaximal)
  let : N.IsPrime := (inferInstance : m.IsPrime).comap
    (Algebra.TensorProduct.includeRight : U →ₐ[R] G).toRingHom
  have hker : N = RingHom.ker f :=
    prime_eq_ker_coordinateEval_of_le_of_ne A i N hNP hNne
  let eN : (U ⧸ N) ≃+* A i :=
    (Ideal.quotientEquivAlgOfEq ℤ hker).toRingEquiv.trans
      (RingHom.quotientKerEquivOfSurjective f.surjective)
  let : Field Ω := Ideal.Quotient.field m
  let : Algebra (U ⧸ N) Ω :=
    (genericFiberComponentQuotientRingHom m).toAlgebra
  let : IsFractionRing (U ⧸ N) Ω :=
    genericFiberComponentQuotient_isFractionRing m
  change IsFractionRing.ringEquivOfRingEquiv
      (K := Ω) (L := FractionRing (A i)) eN
      (algebraMap (U ⧸ N) Ω (Ideal.Quotient.mk N x)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change algebraMap (A i) (FractionRing (A i)) (eN (Ideal.Quotient.mk N x)) = _
  congr 1

/-- The chosen coordinate identification is compatible with the original
base ring.  This algebra form is what normalization and ramification
comparisons consume downstream. -/
noncomputable def genericFiberDVRProductComponentFractionRingAlgEquiv
    (i : ι) (m : Ideal (K ⊗[R] (∀ j, A j))) [m.IsMaximal]
    (hNP : genericFiberComponentBaseIdeal m ≤
      productCoordinatePrime A i)
    (hNne : genericFiberComponentBaseIdeal m ≠
      productCoordinatePrime A i) :
    ((K ⊗[R] (∀ j, A j)) ⧸ m) ≃ₐ[R] FractionRing (A i) :=
  AlgEquiv.ofRingEquiv
    (f := genericFiberDVRProductComponentFractionRingEquiv A i m hNP hNne)
    fun r => by
      let U := ∀ j, A j
      let G := K ⊗[R] U
      let N := genericFiberComponentBaseIdeal m
      have hbase : genericFiberComponentQuotientRingHom m
          (Ideal.Quotient.mk N (algebraMap R U r)) =
        Ideal.Quotient.mk m (algebraMap R G r) := by
        change Ideal.Quotient.mk m
            ((Algebra.TensorProduct.includeRight : U →ₐ[R] G)
              (algebraMap R U r)) =
          Ideal.Quotient.mk m (algebraMap R G r)
        congr 1
        exact (Algebra.TensorProduct.includeRight : U →ₐ[R] G).commutes r
      have hquot : algebraMap R (U ⧸ N) r =
          Ideal.Quotient.mk N (algebraMap R U r) := rfl
      have htower : algebraMap R (FractionRing (A i)) r =
          algebraMap (A i) (FractionRing (A i))
            (algebraMap R (A i) r) :=
        IsScalarTower.algebraMap_apply R (A i) (FractionRing (A i)) r
      change genericFiberDVRProductComponentFractionRingEquiv A i m hNP hNne
          (Ideal.Quotient.mk m (algebraMap R G r)) =
        algebraMap R (FractionRing (A i)) r
      rw [← hbase]
      simpa only [U, N, hquot, htower, Pi.algebraMap_apply] using
        (genericFiberDVRProductComponentFractionRingEquiv_quotient_mk
          A i m hNP hNne (algebraMap R (∀ j, A j) r))

@[simp]
theorem genericFiberDVRProductComponentFractionRingAlgEquiv_quotient_mk
    (i : ι) (m : Ideal (K ⊗[R] (∀ j, A j))) [m.IsMaximal]
    (hNP : genericFiberComponentBaseIdeal m ≤
      productCoordinatePrime A i)
    (hNne : genericFiberComponentBaseIdeal m ≠
      productCoordinatePrime A i)
    (x : ∀ j, A j) :
    genericFiberDVRProductComponentFractionRingAlgEquiv A i m hNP hNne
        (genericFiberComponentQuotientRingHom m
          (Ideal.Quotient.mk (genericFiberComponentBaseIdeal m) x)) =
      algebraMap (A i) (FractionRing (A i)) (x i) :=
  genericFiberDVRProductComponentFractionRingEquiv_quotient_mk
    A i m hNP hNne x

end EtaleFundamentalGroups

end
