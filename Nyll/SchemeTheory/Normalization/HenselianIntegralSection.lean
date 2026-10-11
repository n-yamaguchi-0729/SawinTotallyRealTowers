/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.EtaleSection
public import Nyll.SchemeTheory.FiniteEtale.Algebra.IdempotentFactor
public import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonSection
public import Nyll.SchemeTheory.Normalization.QuotientFiniteFactor
public import Nyll.SchemeTheory.RingTheory.CyclicIdempotentFactor
public import Nyll.SchemeTheory.RingTheory.HenselianIdempotents
public import Nyll.SchemeTheory.RingTheory.JacobsonIdempotentFactor
public import Nyll.SchemeTheory.RingTheory.JacobsonIntegral
public import Nyll.SchemeTheory.RingTheory.LocalizationIdempotentFactor
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Étale sections after integral extension of a Henselian pair

Normalization selects an idempotent in the special fiber. Its integral closure
is integral over the original Henselian base, so this idempotent lifts there.
The resulting factor is integral and étale over the new base, and Jacobson
conservativity identifies it with that base. No Henselian hypothesis on the
integral extension is used in the construction.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Algebra

private theorem exists_integral_factor_of_integral_henselian_base
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra.IsIntegral R B] [Algebra B D] [Algebra.Etale B D]
    (I : Ideal R) [HenselianRing R I]
    (σ : D →ₐ[B] B ⧸ I.map (algebraMap R B)) :
    ∃ e : D, IsIdempotentElem e ∧ σ e = 1 ∧
      Algebra.IsIntegral B (D ⧸ Ideal.span {1 - e}) ∧
      Function.Surjective (algebraMap (B ⧸ I.map (algebraMap R B))
        ((D ⧸ Ideal.span {1 - e}) ⧸
          (I.map (algebraMap R B)).map (algebraMap B (D ⧸ Ideal.span {1 - e})))) := by
  let J : Ideal B := I.map (algebraMap R B)
  have hJ : J ≤ Ideal.jacobson ⊥ :=
    Ideal.map_le_jacobson_bot_of_isIntegral (HenselianRing.jac (R := R) (I := I))
  let C := integralClosure B D
  let K : Ideal C := J.map (algebraMap B C)
  let : CommRing C := inferInstance
  let : CommRing (C ⧸ K) := inferInstance
  let : CommRing (B ⧸ J) := inferInstance
  let qC : C →+* C ⧸ K := Ideal.Quotient.mk K
  let f : C →ₐ[B] D := (integralClosure B D).val
  let p : D ⧸ J.map (algebraMap B D) →ₐ[B ⧸ J] B ⧸ J :=
    AlgHom.quotientSection J σ
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom p.toRingHom)) :=
    AlgHom.isOpenImmersion_SpecMap_quotientSection J σ
  obtain ⟨e₀, he₀, E, hE₁, _, g, hg, hEg, hlocal⟩ :=
    exists_integralClosure_quotient_factor_and_awayMap_bijective J p
  let : CommRing ((C ⧸ K) ⧸ Ideal.span {1 - e₀}) := inferInstance
  let : CommRing ((B ⧸ J) × ((C ⧸ K) ⧸ Ideal.span {1 - e₀})) := inferInstance
  have hgidem : IsIdempotentElem (qC g) := by
    rw [hg]
    exact he₀.one_sub
  let : Algebra R C := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra.IsIntegral R C := Algebra.IsIntegral.trans B
  have hK : K = I.map (algebraMap R C) := by
    dsimp only [K, J]
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R B C]
  have hgidem' : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R C)) g) := by
    rw [← hK]
    exact hgidem
  obtain ⟨e, he, heq'⟩ := exists_idempotent_lift_of_isIntegral I g hgidem'
  have heq : qC e = qC g := by
    change Ideal.Quotient.mk K e = Ideal.Quotient.mk K g
    rw [hK]
    exact heq'
  have hcyc : ∀ x : C ⧸ K, ∃ b : B, qC g * x = b • qC g := by
    intro x
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (E x).1
    refine ⟨b, E.injective ?_⟩
    rw [← IsScalarTower.algebraMap_smul (B ⧸ J) b (qC g),
      map_smul, map_mul, hEg]
    apply Prod.ext
    · change 1 * (E x).1 = Ideal.Quotient.mk J b * 1
      rw [one_mul, mul_one, hb]
    · change 0 * (E x).2 = (Ideal.Quotient.mk J b) • 0
      rw [zero_mul, smul_zero]
  have hcyce : ∀ x : C ⧸ K, ∃ b : B, qC e * x = b • qC e := by
    rw [heq]
    exact hcyc
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {1 - e}) g) :=
    isUnit_quotient_one_sub_of_eq_mod_extendedIdeal J hJ g e heq.symm
  have hfactor := f.bijective_idempotentFactorMap_of_awayMap_bijective e he g hunit hlocal
  have hintegral : Algebra.IsIntegral B (D ⧸ Ideal.span {1 - f e}) :=
    f.isIntegral_idempotentFactor_of_awayMap_bijective e he g hunit hlocal
  have hσg : σ (f g) = 1 := by
    have h := congrArg Prod.fst hEg
    rw [hE₁] at h
    exact h
  have hσe : σ (f e) = 1 := by
    have h := congrArg (p.comp (f.quotientBaseChange J)) heq
    change σ (f e) = σ (f g) at h
    exact h.trans hσg
  refine ⟨f e, he.map f, hσe, hintegral, ?_⟩
  let C' := C ⧸ Ideal.span {1 - e}
  let D' := D ⧸ Ideal.span {1 - f e}
  let : CommRing C' := inferInstance
  let : CommRing (C' ⧸ J.map (algebraMap B C')) := inferInstance
  let : CommRing D' := inferInstance
  let ψ : C' →ₐ[B] D' := f.idempotentFactorMap e
  have hscalar : Function.Surjective (algebraMap (B ⧸ J)
      (C' ⧸ J.map (algebraMap B C'))) :=
    surjective_algebraMap_quotient_idempotentFactor_of_cyclic J e hcyce
  intro y
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨w, rfl⟩ := hfactor.surjective v
  obtain ⟨b, hb⟩ := hscalar (Ideal.Quotient.mk (J.map (algebraMap B C')) w)
  refine ⟨b, ?_⟩
  have h := congrArg (ψ.quotientBaseChange J) hb
  simpa only [AlgHom.commutes, AlgHom.quotientBaseChange_mk] using h

namespace Etale

/-- Étale sections lift after any integral extension of a Henselian pair.
The integral extension need not be finite, local, or complete. -/
theorem exists_lift_section_of_isIntegral_henselian_base
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra.IsIntegral R B] [Algebra B D] [Algebra.Etale B D]
    (I : Ideal R) [HenselianRing R I]
    (σ : D →ₐ[B] B ⧸ I.map (algebraMap R B)) :
    ∃ τ : D →ₐ[B] B,
      (Ideal.Quotient.mkₐ B (I.map (algebraMap R B))).comp τ = σ := by
  let J : Ideal B := I.map (algebraMap R B)
  have hJ : J ≤ Ideal.jacobson ⊥ :=
    Ideal.map_le_jacobson_bot_of_isIntegral (HenselianRing.jac (R := R) (I := I))
  obtain ⟨e, he, hσe, hintegral, hscalar⟩ :=
    exists_integral_factor_of_integral_henselian_base I σ
  let K : Ideal D := Ideal.span {1 - e}
  let F := D ⧸ K
  let q : D →ₐ[B] F := Ideal.Quotient.mkₐ B K
  let : Algebra.Etale B F := quotient_one_sub_of_isIdempotentElem e he
  let : Algebra.IsIntegral B F := hintegral
  let : Module.Finite B F := Algebra.IsIntegral.finite
  have hker : K ≤ RingHom.ker σ.toRingHom := by
    apply Ideal.span_le.mpr
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    change σ (1 - e) = 0
    rw [map_sub, map_one, hσe, sub_self]
  let σF : F →ₐ[B] B ⧸ J := Ideal.Quotient.liftₐ K σ (fun d hd ↦ hker hd)
  have hbij : Function.Bijective (algebraMap B F) :=
    Algebra.FiniteEtale.bijective_algebraMap_of_quotientSection J hJ σF hscalar
  let E : B ≃ₐ[B] F := AlgEquiv.ofBijective (Algebra.ofId B F) hbij
  refine ⟨E.symm.toAlgHom.comp q, ?_⟩
  apply AlgHom.ext
  intro d
  change Ideal.Quotient.mk J (E.symm (q d)) = σ d
  have h := σF.commutes (E.symm (q d))
  have hE : algebraMap B F (E.symm (q d)) = q d := E.apply_symm_apply (q d)
  rw [hE] at h
  exact h.symm

end Etale
end Algebra
