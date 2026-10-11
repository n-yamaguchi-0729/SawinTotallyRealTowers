/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.IntegralPurelyInseparableLocalTensor
import Nyll.SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Domains in local étale neighborhoods of a geometrically unibranch ring

The algebraic input is an actual injective integral local map into a normal
local domain, with purely inseparable residue field extension. Base change
of that extension along a local étale neighborhood is local. It is also a
localization of an étale algebra over the normal domain, hence a domain.
Flatness embeds the original local étale neighborhood into that domain.

For a reduced geometrically unibranch local ring, the integral closure in
its fraction field supplies exactly these inputs. No domain assertion about
the étale neighborhood or geometric stalk is assumed.
-/

noncomputable section

open scoped TensorProduct
open IsLocalRing

namespace SchemeTheory

universe u

/-- A localization of an étale algebra over a normal domain is a domain
whenever that localization is a local ring. -/
theorem isDomain_of_etale_of_local_localization
    (R C D : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing C] [Algebra R C] [Algebra.Etale R C]
    [CommRing D] [Algebra C D] [IsLocalRing D]
    (M : Submonoid C) [IsLocalization M D] : IsDomain D := by
  let q : Ideal C := (maximalIdeal D).under C
  have : q.IsPrime := Ideal.comap_isPrime (algebraMap C D) (maximalIdeal D)
  have hM : M ≤ q.primeCompl := by
    intro c hc
    change ¬ ¬ IsUnit (algebraMap C D c)
    exact fun hnonunit => hnonunit (IsLocalization.map_units D (⟨c, hc⟩ : M))
  have : IsLocalization.AtPrime D q :=
    IsLocalization.of_le M q.primeCompl hM (by
      intro c hc
      change ¬ ¬ IsUnit (algebraMap C D c) at hc
      exact Classical.not_not.mp hc)
  exact (Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    R C q D).1

/-- An actual local étale neighborhood is a domain if the local base embeds
integrally into a normal local domain with purely inseparable residue field. -/
theorem isDomain_atPrime_of_etale_of_integral_normal_extension
    (R N C : Type u)
    [CommRing R] [IsLocalRing R]
    [CommRing N] [IsLocalRing N] [IsDomain N] [IsIntegrallyClosed N]
    [Algebra R N] [Algebra.IsIntegral R N] [IsLocalHom (algebraMap R N)]
    [IsPurelyInseparable (ResidueField R) (ResidueField N)]
    (hinj : Function.Injective (algebraMap R N))
    [CommRing C] [Algebra R C] [Algebra.Etale R C]
    (q : Ideal C) [q.IsPrime]
    [IsLocalHom (algebraMap R (Localization.AtPrime q))] :
    IsDomain (Localization.AtPrime q) := by
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
  exact Function.Injective.isDomain
    (Algebra.TensorProduct.includeRight (R := R) (A := N) (B := T))
    (Algebra.TensorProduct.includeRight_injective hinj)

end SchemeTheory
