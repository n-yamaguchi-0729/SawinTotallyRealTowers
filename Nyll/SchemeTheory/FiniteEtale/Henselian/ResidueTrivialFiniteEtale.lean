/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.Etale

/-!
# Residue-trivial finite etale local algebras over a Henselian base

A finite etale local algebra over a Henselian local ring is the base ring
as soon as its residue-field map is bijective.  This is the pointed form of
the usual strict-Henselian splitting argument: instead of assuming that the
base residue field is separably closed, we use the actual residue-field
isomorphism of the selected factor.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Polynomial

universe u

/-- A residue-trivial finite etale local algebra over a Henselian local ring
is trivial.

`FaithfulSMul R S` is only the injectivity input.  Surjectivity is obtained
by lifting the residue of a monogenic generator with Hensel's lemma and then
using uniqueness of a simple root in the local target. -/
theorem algebraMap_bijective_of_henselian_of_residueFieldMap_bijective_of_finiteEtale_local
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [HenselianLocalRing R] [IsLocalRing S]
    [Module.Finite R S] [FaithfulSMul R S] [Algebra.Etale R S]
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R S))) :
    Function.Bijective (algebraMap R S) := by
  have hres' : Function.Bijective
      (algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S)) := by
    have hmap :
        IsLocalRing.ResidueField.map (algebraMap R S) =
          algebraMap (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField S) := by
      apply RingHom.ext
      intro x
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
      rfl
    simpa only [hmap] using hres
  obtain ⟨β, hβ⟩ := IsLocalRing.exists_adjoin_eq_top (R := R) (S := S)
  let f : R[X] := minpoly R β
  have hf_monic : f.Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral β)
  obtain ⟨a₀, ha₀⟩ :=
    hres'.2 (IsLocalRing.residue S β)
  have hf_root_residue : aeval a₀ f = 0 := by
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
        minpoly (IsLocalRing.ResidueField R) (IsLocalRing.residue S β) by
      simpa [f] using
        IsLocalRing.minpoly_map_residue (R := R) (S := S) hβ]
    exact minpoly.aeval _ _
  have hf_derivative_residue : aeval a₀ f.derivative ≠ 0 := by
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
    have hderivative_map :
        f.derivative.map (IsLocalRing.residue R) =
          (minpoly (IsLocalRing.ResidueField R)
            (IsLocalRing.residue S β)).derivative := by
      have hm :
          f.map (IsLocalRing.residue R) =
            minpoly (IsLocalRing.ResidueField R)
              (IsLocalRing.residue S β) := by
        simpa [f] using
          IsLocalRing.minpoly_map_residue (R := R) (S := S) hβ
      simpa [derivative_map] using congrArg Polynomial.derivative hm
    rw [hderivative_map] at hmap
    exact
      (Algebra.IsSeparable.isSeparable
        (IsLocalRing.ResidueField R)
        (IsLocalRing.residue S β)).aeval_derivative_ne_zero
          (minpoly.aeval _ _) hmap
  have h_hensel := ((HenselianLocalRing.TFAE R).out 1 2).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨a, ha_root, ha_residue⟩ :=
    h_hensel f hf_monic a₀ hf_root_residue hf_derivative_residue
  have hresidue :
      IsLocalRing.residue S (algebraMap R S a) =
        IsLocalRing.residue S β := by
    rw [← IsLocalRing.ResidueField.algebraMap_residue, ha_residue, ha₀]
  have hnot_unit : ¬ IsUnit (β - algebraMap R S a) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp [hresidue]
  have hβ_image : β = algebraMap R S a := by
    let g : S[X] := f.map (algebraMap R S)
    apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
      (f := g) (a := β) (b := algebraMap R S a)
    · simpa [g, f, aeval_def] using minpoly.aeval R β
    · simpa [g, eval_map] using congrArg (algebraMap R S) ha_root
    · exact hnot_unit
    · simpa [g, derivative_map, aeval_def] using
        IsLocalRing.isUnit_aeval_derivative_minpoly_of_adjoin_eq_top
          (R := R) (S := S) hβ
  have htop_eq_bot : (⊤ : Subalgebra R S) = ⊥ := by
    rw [← hβ]
    apply le_antisymm
    · apply Algebra.adjoin_le
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      rw [hβ_image]
      exact Subalgebra.algebraMap_mem ⊥ a
    · exact bot_le
  exact ⟨FaithfulSMul.algebraMap_injective R S,
    Algebra.surjective_algebraMap_iff.mpr htop_eq_bot⟩

/-- The explicit base-algebra equivalence associated to the preceding
pointed splitting theorem. -/
noncomputable def henselianResidueTrivialFiniteEtaleAlgEquiv
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [HenselianLocalRing R] [IsLocalRing S]
    [Module.Finite R S] [FaithfulSMul R S] [Algebra.Etale R S]
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R S))) :
    R ≃ₐ[R] S :=
  AlgEquiv.ofBijective (Algebra.ofId R S)
    (algebraMap_bijective_of_henselian_of_residueFieldMap_bijective_of_finiteEtale_local
      hres)

end EtaleFundamentalGroups

end
