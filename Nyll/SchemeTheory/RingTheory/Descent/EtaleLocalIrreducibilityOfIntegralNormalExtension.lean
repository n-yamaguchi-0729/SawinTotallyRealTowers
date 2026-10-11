/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.IntegralPurelyInseparableLocalTensor
import Nyll.SchemeTheory.RingTheory.FlatTensorNilpotentKernel
import Nyll.SchemeTheory.RingTheory.Descent.EtaleLocalDomainOfIntegralNormalExtension
import Nyll.SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Irreducibility of local étale neighborhoods from normalization data

The same actual normal base change used in the domain theorem also handles
nonreduced local rings. Flatness carries a nilpotent kernel to a nilpotent
kernel; embedding modulo that kernel into the constructed normal domain
proves that the nilradical of the original local étale neighborhood is prime.
-/

noncomputable section

open scoped TensorProduct
open IsLocalRing

namespace SchemeTheory

universe u

/-- A local étale neighborhood has a prime nilradical when the base maps
integrally and locally to a normal local domain with purely inseparable residue
field and a kernel consisting of nilpotents. -/
theorem nilradical_isPrime_atPrime_of_etale_of_integral_normal_extension
    (R N C : Type u)
    [CommRing R] [IsLocalRing R]
    [CommRing N] [IsLocalRing N] [IsDomain N] [IsIntegrallyClosed N]
    [Algebra R N] [Algebra.IsIntegral R N] [IsLocalHom (algebraMap R N)]
    [IsPurelyInseparable (ResidueField R) (ResidueField N)]
    (hker : RingHom.ker (algebraMap R N) ≤ nilradical R)
    [CommRing C] [Algebra R C] [Algebra.Etale R C]
    (q : Ideal C) [q.IsPrime]
    [IsLocalHom (algebraMap R (Localization.AtPrime q))] :
    (nilradical (Localization.AtPrime q)).IsPrime := by
  let T := Localization.AtPrime q
  let E := N ⊗[R] C
  let D := N ⊗[R] T
  let μ : E →ₐ[N] D :=
    Algebra.TensorProduct.map (AlgHom.id N N) (IsScalarTower.toAlgHom R C T)
  let : Algebra E D := μ.toRingHom.toAlgebra
  have : IsScalarTower N E D :=
    IsScalarTower.of_algebraMap_eq fun n => (μ.commutes n).symm
  have : IsLocalRing (T ⊗[R] N) :=
    isLocalRing_tensorProduct_of_integral_of_purelyInseparable_residue R N T
  have : IsLocalRing D :=
    (Algebra.TensorProduct.comm R T N).toRingEquiv.isLocalRing
  let M : Submonoid E := q.primeCompl.map
    (Algebra.TensorProduct.includeRight (R := R) (A := N))
  have : IsLocalization M D :=
    IsLocalization.tensorProduct_tensorProduct_right R N q.primeCompl T (by
      apply RingHom.ext
      intro c
      change μ ((1 : N) ⊗ₜ[R] c) = (1 : N) ⊗ₜ[R] algebraMap C T c
      rw [Algebra.TensorProduct.map_tmul]
      rfl)
  have : IsDomain D := isDomain_of_etale_of_local_localization N E D M
  have : Module.Flat R T := Module.Flat.trans R C T
  let ι : T →+* D := Algebra.TensorProduct.includeRight.toRingHom
  have hnilker : RingHom.ker ι ≤ nilradical T := by
    intro t ht
    apply ker_includeLeft_le_nilradical_of_flat R N T hker
    change t ⊗ₜ[R] (1 : N) = 0
    change (1 : N) ⊗ₜ[R] t = 0 at ht
    have h := congrArg (Algebra.TensorProduct.comm R N T) ht
    simpa only [Algebra.TensorProduct.comm_tmul, map_zero] using h
  have : (RingHom.ker ι).IsPrime := RingHom.ker_isPrime ι
  have heq : RingHom.ker ι = nilradical T :=
    le_antisymm hnilker (nilradical_le_prime (RingHom.ker ι))
  rw [← heq]
  exact RingHom.ker_isPrime ι

end SchemeTheory
