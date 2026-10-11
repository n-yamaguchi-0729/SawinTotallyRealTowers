/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Locality after base change of an integral local extension

If an integral map of local rings induces a purely inseparable residue field
extension, its tensor product with any local algebra is local. The proof
constructs the map to the tensor product of the two residue fields. Every
maximal quotient factors through that map, and purely inseparability gives
uniqueness of the resulting prime of the residue tensor product.

This is the local tensor product step of Stacks Project, Tag 092Y, used in
the forward implication of Tag 06DM. It neither assumes nor encodes the
irreducibility of a strict henselization.
-/

noncomputable section

open scoped TensorProduct
open IsLocalRing

namespace SchemeTheory

universe u v w

private theorem isLocalHom_of_ker_eq_maximalIdeal
    {A K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    (f : A →+* K) (hf : RingHom.ker f = maximalIdeal A) : IsLocalHom f := by
  constructor
  intro a ha
  by_contra hunit
  have hz : f a = 0 := RingHom.mem_ker.mp (hf.symm ▸ hunit)
  exact (isUnit_iff_ne_zero.mp ha) hz

/-- An integral local extension with purely inseparable residue field remains
local after tensoring with a local algebra over the original local ring. -/
theorem isLocalRing_tensorProduct_of_integral_of_purelyInseparable_residue
    (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [CommRing T] [IsLocalRing T]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.IsIntegral R S]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    [IsPurelyInseparable (ResidueField R) (ResidueField S)] :
    IsLocalRing (T ⊗[R] S) := by
  let B := T ⊗[R] S
  let C := ResidueField T ⊗[ResidueField R] ResidueField S
  let α : B →+* C := Algebra.TensorProduct.mapRingHom
    (residue R) (residue T) (residue S)
    (by
      apply RingHom.ext
      intro r
      exact (ResidueField.algebraMap_residue (R := R) (S := T) r).symm)
    (by
      apply RingHom.ext
      intro r
      exact (ResidueField.algebraMap_residue (R := R) (S := S) r).symm)
  have : Nontrivial C :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      (ResidueField R) (ResidueField T) (ResidueField S)
      (algebraMap (ResidueField R) (ResidueField T)).injective
      (algebraMap (ResidueField R) (ResidueField S)).injective
  have : Nontrivial B := α.domain_nontrivial
  have hfactor : ∀ (M : Ideal B), M.IsMaximal →
      ∃ β : C →+* B ⧸ M, β.comp α = Ideal.Quotient.mk M := by
    intro M hM
    have : M.IsMaximal := hM
    let L := B ⧸ M
    let : Field L := Ideal.Quotient.field M
    let q : B →+* L := Ideal.Quotient.mk M
    let fT : T →+* L := q.comp Algebra.TensorProduct.includeLeftRingHom
    let fS : S →+* L := q.comp Algebra.TensorProduct.includeRight.toRingHom
    let fR : R →+* L := fT.comp (algebraMap R T)
    have hbase : fS.comp (algebraMap R S) = fR := by
      change q.comp (Algebra.TensorProduct.includeRight.toRingHom.comp
        (algebraMap R S)) =
        q.comp (Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap R T))
      rw [Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]
    have hkerT : RingHom.ker fT = maximalIdeal T := by
      rw [← RingHom.comap_ker, Ideal.mk_ker]
      exact eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := T) (S := B) M)
    have : IsLocalHom fT := isLocalHom_of_ker_eq_maximalIdeal fT hkerT
    have : IsLocalHom fR := inferInstance
    have hkerR : RingHom.ker fR = maximalIdeal R := by
      rw [← RingHom.comap_ker, hkerT]
      exact maximalIdeal_comap (algebraMap R T)
    have hkerS : RingHom.ker fS = maximalIdeal S := by
      have hunder : (RingHom.ker fS).under R = maximalIdeal R := by
        rw [Ideal.under, RingHom.comap_ker, hbase]
        exact hkerR
      have : (RingHom.ker fS).IsPrime := RingHom.ker_isPrime fS
      apply eq_maximalIdeal
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R)
      rw [hunder]
      infer_instance
    have : IsLocalHom fS := isLocalHom_of_ker_eq_maximalIdeal fS hkerS
    let rbar : ResidueField R →+* L := ResidueField.lift fR
    let tbar : ResidueField T →+* L := ResidueField.lift fT
    let sbar : ResidueField S →+* L := ResidueField.lift fS
    have hTbar : tbar.comp (algebraMap (ResidueField R) (ResidueField T)) =
        (algebraMap L L).comp rbar := by
      apply RingHom.ext
      intro z
      obtain ⟨r, rfl⟩ := residue_surjective z
      rw [RingHom.comp_apply, ResidueField.algebraMap_residue,
        RingHom.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
      exact (ResidueField.lift_residue_apply fT (algebraMap R T r)).trans
        (ResidueField.lift_residue_apply fR r).symm
    have hSbar : sbar.comp (algebraMap (ResidueField R) (ResidueField S)) =
        (algebraMap L L).comp rbar := by
      apply RingHom.ext
      intro z
      obtain ⟨r, rfl⟩ := residue_surjective z
      rw [RingHom.comp_apply, ResidueField.algebraMap_residue,
        RingHom.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
      exact (ResidueField.lift_residue_apply fS (algebraMap R S r)).trans
        ((RingHom.congr_fun hbase r).trans
          (ResidueField.lift_residue_apply fR r).symm)
    let β : C →+* L := (Algebra.TensorProduct.lid L L).toRingHom.comp
      (Algebra.TensorProduct.mapRingHom rbar tbar sbar hTbar hSbar)
    refine ⟨β, ?_⟩
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t s =>
      change (Algebra.TensorProduct.lid L L)
        (Algebra.TensorProduct.mapRingHom rbar tbar sbar hTbar hSbar
          (Algebra.TensorProduct.mapRingHom (residue R) (residue T) (residue S)
            _ _ (t ⊗ₜ[R] s))) = q (t ⊗ₜ[R] s)
      rw [Algebra.TensorProduct.mapRingHom_tmul,
        Algebra.TensorProduct.mapRingHom_tmul, Algebra.TensorProduct.lid_tmul,
        smul_eq_mul]
      change fT t * fS s = q (t ⊗ₜ[R] s)
      change q (t ⊗ₜ[R] (1 : S)) * q ((1 : T) ⊗ₜ[R] s) = q (t ⊗ₜ[R] s)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy =>
      exact (map_add (β.comp α) x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add q x y).symm)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (α := B)
  refine IsLocalRing.of_unique_max_ideal ⟨M, hM, ?_⟩
  intro N hN
  have : M.IsMaximal := hM
  have : N.IsMaximal := hN
  let : Field (B ⧸ M) := Ideal.Quotient.field M
  let : Field (B ⧸ N) := Ideal.Quotient.field N
  obtain ⟨βM, hβM⟩ := hfactor M hM
  obtain ⟨βN, hβN⟩ := hfactor N hN
  let pM : PrimeSpectrum C := ⟨RingHom.ker βM, RingHom.ker_isPrime βM⟩
  let pN : PrimeSpectrum C := ⟨RingHom.ker βN, RingHom.ker_isPrime βN⟩
  have hprimes : pN = pM :=
    (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable
      (ResidueField R) (ResidueField S) (ResidueField T)).injective
        (Subsingleton.elim _ _)
  have hk : RingHom.ker βN = RingHom.ker βM := congrArg PrimeSpectrum.asIdeal hprimes
  have hcomap := congrArg (fun I : Ideal C => I.comap α) hk
  rw [RingHom.comap_ker, RingHom.comap_ker, hβN, hβM,
    Ideal.mk_ker, Ideal.mk_ker] at hcomap
  exact hcomap

end SchemeTheory
