/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenFactor.Core

/-!
# A uniquely chosen finite etale factor in a separate universe

The strict-Henselian chosen-factor argument does not depend on the base and
factor carriers living in the same universe.  This file records the
universe-polymorphic form needed when the factor is a localization of an
integral closure in a generic tensor component.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Polynomial

universe uR uS

/-- A finite etale local algebra over a Henselian local ring with separably
closed residue field is the base, with independent carrier universes. -/
theorem
    algebraMap_bijective_of_henselian_of_isSepClosed_residue_of_finiteEtale_local_universe
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [IsLocalRing S]
    [Module.Finite R S] [FaithfulSMul R S] [Algebra.Etale R S]
    [IsSepClosed (IsLocalRing.ResidueField R)] :
    Function.Bijective (algebraMap R S) := by
  obtain ⟨β, hβ⟩ := IsLocalRing.exists_adjoin_eq_top (R := R) (S := S)
  let f : R[X] := minpoly R β
  have hfMonic : f.Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral β)
  obtain ⟨a₀, ha₀⟩ :=
    IsSepClosed.algebraMap_surjective
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
      (IsLocalRing.residue S β)
  have hfRootResidue : aeval a₀ f = 0 := by
    apply (algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)).injective
    rw [map_zero,
      Polynomial.map_aeval_eq_aeval_map
        (R := R) (S := IsLocalRing.ResidueField R)
        (T := IsLocalRing.ResidueField R)
        (U := IsLocalRing.ResidueField S)
        (φ := IsLocalRing.residue R)
        (ψ := algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S)) rfl f a₀,
      ha₀]
    rw [show f.map (IsLocalRing.residue R) =
        minpoly (IsLocalRing.ResidueField R)
          (IsLocalRing.residue S β) by
      simpa [f] using
        IsLocalRing.minpoly_map_residue (R := R) (S := S) hβ]
    exact minpoly.aeval _ _
  have hfDerivativeResidue : aeval a₀ f.derivative ≠ 0 := by
    intro hzero
    have hmap := congrArg
      (algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S)) hzero
    rw [map_zero,
      Polynomial.map_aeval_eq_aeval_map
        (R := R) (S := IsLocalRing.ResidueField R)
        (T := IsLocalRing.ResidueField R)
        (U := IsLocalRing.ResidueField S)
        (φ := IsLocalRing.residue R)
        (ψ := algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S)) rfl f.derivative a₀,
      ha₀] at hmap
    have hDerivativeMap :
        f.derivative.map (IsLocalRing.residue R) =
          (minpoly (IsLocalRing.ResidueField R)
            (IsLocalRing.residue S β)).derivative := by
      have hm :
          f.map (IsLocalRing.residue R) =
            minpoly (IsLocalRing.ResidueField R)
              (IsLocalRing.residue S β) := by
        simpa [f] using
          IsLocalRing.minpoly_map_residue (R := R) (S := S) hβ
      simpa [Polynomial.derivative_map] using
        congrArg Polynomial.derivative hm
    rw [hDerivativeMap] at hmap
    exact
      (Algebra.IsSeparable.isSeparable
        (IsLocalRing.ResidueField R)
        (IsLocalRing.residue S β)).aeval_derivative_ne_zero
          (minpoly.aeval _ _) hmap
  have hHensel := ((HenselianLocalRing.TFAE R).out 1 2).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨a, haRoot, haResidue⟩ :=
    hHensel f hfMonic a₀ hfRootResidue hfDerivativeResidue
  have hresidue :
      IsLocalRing.residue S (algebraMap R S a) =
        IsLocalRing.residue S β := by
    rw [← IsLocalRing.ResidueField.algebraMap_residue, haResidue, ha₀]
  have hnotUnit : ¬ IsUnit (β - algebraMap R S a) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp [hresidue]
  have hβImage : β = algebraMap R S a := by
    let g : S[X] := f.map (algebraMap R S)
    apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
      (f := g) (a := β) (b := algebraMap R S a)
    · simpa [g, f, aeval_def] using minpoly.aeval R β
    · simpa [g, eval_map] using congrArg (algebraMap R S) haRoot
    · exact hnotUnit
    · simpa [g, Polynomial.derivative_map, aeval_def] using
        IsLocalRing.isUnit_aeval_derivative_minpoly_of_adjoin_eq_top
          (R := R) (S := S) hβ
  have htopEqBot : (⊤ : Subalgebra R S) = ⊥ := by
    rw [← hβ]
    apply le_antisymm
    · apply Algebra.adjoin_le
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      rw [hβImage]
      exact Subalgebra.algebraMap_mem ⊥ a
    · exact bot_le
  exact ⟨FaithfulSMul.algebraMap_injective R S,
    Algebra.surjective_algebraMap_iff.mpr htopEqBot⟩

/-- A finite etale algebra with a unique prime over the closed point of a
strictly Henselian local ring is the base, with independent carrier
universes. -/
theorem
    algebraMap_bijective_of_unique_prime_over_maximal_of_strictHenselian_universe
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Module.Finite R S] [Algebra.Etale R S]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal R)]
    (hunique : ∀ Q : Ideal S, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q = q) :
    Function.Bijective (algebraMap R S) := by
  have hqMaximal : q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (algebraMap R S) (fun x ↦ Algebra.IsIntegral.isIntegral x) q <| by
        rw [← Ideal.under_def,
          ← q.over_def (IsLocalRing.maximalIdeal R)]
        exact IsLocalRing.maximalIdeal.isMaximal R
  let : IsLocalRing S :=
    IsLocalRing.of_unique_max_ideal ⟨q, hqMaximal, by
      intro Q hQMaximal
      let : Q.IsPrime := hQMaximal.isPrime
      have hQUnderMaximal : (Q.under R).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R S)
          (fun x ↦ Algebra.IsIntegral.isIntegral x) Q
      have hQOver : Q.LiesOver (IsLocalRing.maximalIdeal R) :=
        { over := (IsLocalRing.eq_maximalIdeal hQUnderMaximal).symm }
      exact hunique Q inferInstance hQOver⟩
  have hqEq : q = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal hqMaximal
  have hcomap :
      (IsLocalRing.maximalIdeal S).comap (algebraMap R S) =
        IsLocalRing.maximalIdeal R := by
    rw [← hqEq]
    change q.under R = IsLocalRing.maximalIdeal R
    exact (q.over_def (IsLocalRing.maximalIdeal R)).symm
  let : IsLocalHom (algebraMap R S) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 5 1).mp hcomap
  let : Module.FaithfullyFlat R S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact
    algebraMap_bijective_of_henselian_of_isSepClosed_residue_of_finiteEtale_local_universe
      (R := R) (S := S)

/-- The explicit strict-Henselian chosen-factor equivalence with independent
base and factor universes. -/
noncomputable def strictHenselianChosenFactorAlgEquiv_universe
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Module.Finite R S] [Algebra.Etale R S]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal R)]
    (hunique : ∀ Q : Ideal S, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q = q) :
    R ≃ₐ[R] S :=
  AlgEquiv.ofBijective (Algebra.ofId R S)
    (algebraMap_bijective_of_unique_prime_over_maximal_of_strictHenselian_universe
      q hunique)

end EtaleFundamentalGroups

end
