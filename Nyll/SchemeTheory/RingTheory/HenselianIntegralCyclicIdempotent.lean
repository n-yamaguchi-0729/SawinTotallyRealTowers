/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.HenselianCyclicIdempotent
public import Nyll.SchemeTheory.RingTheory.IdempotentLocalizationCyclicity
public import Nyll.SchemeTheory.RingTheory.IntegralLocalizationIdempotentModel
public import Nyll.SchemeTheory.RingTheory.QuotientBaseChange

/-!
# Cyclic quotient idempotents in integral algebras over a Henselian pair

A finite subalgebra can retain a quotient idempotent and its principal
localization. Cyclicity descends through that localization comparison, so the
finite-algebra lifting theorem applies. Mapping the resulting idempotent back
gives a lift in the original integral algebra.
-/

@[expose] public section

universe u v

namespace Algebra

/-- A cyclic quotient idempotent in an integral algebra lifts whenever its
principal localization is of finite type over the base. -/
theorem exists_idempotent_lift_of_integral_of_cyclic_quotient
    {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.IsIntegral R C] (I : Ideal R) [HenselianRing R I] (b : C)
    [Algebra.FiniteType R (Localization.Away b)]
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R C)) b))
    (hcyc : ∀ x : C ⧸ I.map (algebraMap R C), ∃ r : R,
      Ideal.Quotient.mk (I.map (algebraMap R C)) b * x =
        r • Ideal.Quotient.mk (I.map (algebraMap R C)) b) :
    ∃ e : C, IsIdempotentElem e ∧
      Ideal.Quotient.mk (I.map (algebraMap R C)) e =
        Ideal.Quotient.mk (I.map (algebraMap R C)) b := by
  obtain ⟨S, hfinite, hbS, hbid, hbij⟩ :=
    exists_finite_subalgebra_idempotent_awayMap_bijective I b hb
  let : Module.Finite R S := hfinite
  let bS : S := ⟨b, hbS⟩
  have hcycS : ∀ x : S ⧸ I.map (algebraMap R S), ∃ r : R,
      Ideal.Quotient.mk (I.map (algebraMap R S)) bS * x =
        r • Ideal.Quotient.mk (I.map (algebraMap R S)) bS :=
    cyclic_quotient_idempotent_of_awayMap_bijective S.val I bS hbid hbij hcyc
  obtain ⟨e, he, heq⟩ := exists_idempotent_lift_of_cyclic_quotient I bS hbid hcycS
  refine ⟨S.val e, he.map S.val, ?_⟩
  exact congrArg (S.val.quotientBaseChange I) heq

end Algebra
