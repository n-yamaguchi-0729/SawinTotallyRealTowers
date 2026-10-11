/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Normalization.Affine
public import Nyll.SchemeTheory.RingTheory.OpenImmersionFiniteFactor

/-!
# Finite quotient factors in an affine normalization

For a quasi-finite algebra of finite type, a finite open factor of a quotient
fiber is a factor of the corresponding quotient of the integral closure.
The factor's unit has a representative in the integral closure whose
principal localization makes the integral-closure inclusion bijective.

The open immersion needed for the extraction is supplied by Zariski's main
theorem through the concrete affine normalization comparison.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Algebra

/-- A finite open factor in a quotient fiber extends to the integral closure,
and its unit lifts to a principal neighborhood on which the normalization
inclusion becomes an isomorphism. -/
theorem exists_integralClosure_quotient_factor_and_awayMap_bijective
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra.FiniteType R B] [Algebra.QuasiFinite R B]
    (I : Ideal R) [Algebra (R ⧸ I) D] [Module.Finite (R ⧸ I) D]
    (p : B ⧸ I.map (algebraMap R B) →ₐ[R ⧸ I] D)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom p.toRingHom))] :
    let C := integralClosure R B
    let J := I.map (algebraMap R C)
    ∃ e : C ⧸ J, IsIdempotentElem e ∧
      ∃ E : (C ⧸ J) ≃ₐ[R ⧸ I] D × ((C ⧸ J) ⧸ Ideal.span {1 - e}),
        (∀ x, (E x).1 = p ((integralClosure R B).val.quotientBaseChange I x)) ∧
        (∀ x, (E x).2 = Ideal.Quotient.mk (Ideal.span {1 - e}) x) ∧
        ∃ g : C, Ideal.Quotient.mk J g = 1 - e ∧
          E (Ideal.Quotient.mk J g) = (1, 0) ∧
          Function.Bijective (Localization.awayMap (integralClosure R B).val.toRingHom g) := by
  let : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom)) :=
    isOpenImmersion_spec_integralClosure R B
  exact (integralClosure R B).val.exists_quotient_factor_and_awayMap_bijective I p

end Algebra
