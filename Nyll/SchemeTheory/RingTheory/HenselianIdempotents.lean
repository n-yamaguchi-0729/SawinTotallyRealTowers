/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.HenselianFiniteIdempotent
public import Nyll.SchemeTheory.RingTheory.IntegralLocalizationIdempotentModel
public import Nyll.SchemeTheory.RingTheory.JacobsonIdempotentRigidity
public import Nyll.SchemeTheory.RingTheory.JacobsonIntegral
public import Nyll.SchemeTheory.RingTheory.QuotientBaseChange

/-!
# Idempotents in integral algebras over Henselian pairs

Quotient idempotence uses only finitely many coefficients of the integral
algebra. A finite subalgebra containing these coefficients retains the
quotient idempotent. The finite-algebra theorem lifts it, and the canonical
subalgebra inclusion carries the lift back to the original algebra.
The extended ideal lies in the Jacobson radical, which gives uniqueness.
-/

@[expose] public section

universe u v

namespace Algebra

/-- Every quotient idempotent of an integral algebra over a Henselian pair
lifts, without a finite-type hypothesis on the algebra or any localization. -/
theorem exists_idempotent_lift_of_isIntegral
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] (I : Ideal R) [HenselianRing R I] (b : B)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R B)) b)) :
    ∃ e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk (I.map (algebraMap R B)) e =
        Ideal.Quotient.mk (I.map (algebraMap R B)) b := by
  obtain ⟨S, hfinite, hbS, hbid⟩ :=
    exists_finite_subalgebra_quotient_idempotent I b hb
  let : Module.Finite R S := hfinite
  obtain ⟨e, he, heq⟩ := exists_idempotent_lift_of_finite I (⟨b, hbS⟩ : S) hbid
  refine ⟨S.val e, he.map S.val, ?_⟩
  exact congrArg (S.val.quotientBaseChange I) heq

/-- Reduction gives a bijection on idempotents of every integral algebra over
a Henselian pair. This includes all finite algebras and does not require
locality, completeness, or finite presentation. -/
theorem bijective_idempotents_quotient_of_henselian
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] (I : Ideal R) [HenselianRing R I] :
    Function.Bijective (fun e : {e : B // IsIdempotentElem e} ↦
      (⟨Ideal.Quotient.mk (I.map (algebraMap R B)) e.1,
        e.2.map (Ideal.Quotient.mk (I.map (algebraMap R B)))⟩ :
          {e : B ⧸ I.map (algebraMap R B) // IsIdempotentElem e})) := by
  let J : Ideal B := I.map (algebraMap R B)
  have hJ : J ≤ Ideal.jacobson ⊥ :=
    Ideal.map_le_jacobson_bot_of_isIntegral (HenselianRing.jac (R := R) (I := I))
  constructor
  · intro e f h
    apply Subtype.ext
    exact IsIdempotentElem.eq_of_quotient_eq_of_le_jacobson J hJ e.2 f.2
      (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective a
    have hbid : IsIdempotentElem (Ideal.Quotient.mk J b) := by
      rw [hb]
      exact ha
    obtain ⟨e, he, heq⟩ := exists_idempotent_lift_of_isIntegral I b hbid
    exact ⟨⟨e, he⟩, Subtype.ext (heq.trans hb)⟩

end Algebra
