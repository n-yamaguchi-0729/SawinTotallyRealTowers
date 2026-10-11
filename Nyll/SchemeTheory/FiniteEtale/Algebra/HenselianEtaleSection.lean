/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.IdempotentFactor
public import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonRigidity
public import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonSection
public import Nyll.SchemeTheory.Normalization.HenselianSectionFactor
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Lifting étale sections over a Henselian pair

A section over the quotient selects an integral idempotent factor of the
étale algebra. This factor is finite étale, and its special fiber is generated
by the base. The section makes its structural map injective on the special
fiber, so Jacobson conservativity identifies the factor with the base itself.
The original section therefore lifts. Unramified rigidity gives uniqueness.

This proves the étale-section lifting implication used in Stacks Tag 09XI
for the native general `HenselianRing R I` class.
-/

@[expose] public section

universe u

namespace Algebra.Etale

/-- Reduction over a Henselian pair gives a bijection on sections of every
étale algebra. No finiteness as a module, locality, or completeness is assumed. -/
theorem bijective_comp_quotient_of_henselian
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [Algebra.Etale R B]
    (I : Ideal R) [HenselianRing R I] :
    Function.Bijective
      ((Ideal.Quotient.mkₐ R I).comp : (B →ₐ[R] R) → B →ₐ[R] R ⧸ I) := by
  refine ⟨Algebra.FormallyUnramified.comp_injective_of_le_jacobson I
    (HenselianRing.jac (R := R) (I := I)), ?_⟩
  intro σ
  obtain ⟨e, he, hσe, hintegral, hscalar⟩ :=
    Algebra.exists_integral_idempotent_factor_of_etale_quotientSection I σ
  let K : Ideal B := Ideal.span {1 - e}
  let F := B ⧸ K
  let q : B →ₐ[R] F := Ideal.Quotient.mkₐ R K
  let : Algebra.Etale R F := quotient_one_sub_of_isIdempotentElem e he
  let : Algebra.IsIntegral R F := hintegral
  let : Module.Finite R F := Algebra.IsIntegral.finite
  have hker : K ≤ RingHom.ker σ.toRingHom := by
    apply Ideal.span_le.mpr
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    change σ (1 - e) = 0
    rw [map_sub, map_one, hσe, sub_self]
  let σF : F →ₐ[R] R ⧸ I := Ideal.Quotient.liftₐ K σ (fun b hb ↦ hker hb)
  have hbij : Function.Bijective (algebraMap R F) :=
    Algebra.FiniteEtale.bijective_algebraMap_of_quotientSection I
      (HenselianRing.jac (R := R) (I := I)) σF hscalar
  let E : R ≃ₐ[R] F := AlgEquiv.ofBijective (Algebra.ofId R F) hbij
  refine ⟨E.symm.toAlgHom.comp q, ?_⟩
  apply AlgHom.ext
  intro b
  change Ideal.Quotient.mk I (E.symm (q b)) = σ b
  have h := σF.commutes (E.symm (q b))
  have hE : algebraMap R F (E.symm (q b)) = q b := E.apply_symm_apply (q b)
  rw [hE] at h
  exact h.symm

end Algebra.Etale
