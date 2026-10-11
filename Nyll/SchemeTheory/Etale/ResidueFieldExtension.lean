/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.Tower

/-!
# Realizing separable residue-field extensions in étale neighborhoods

A common denominator rescales a primitive element so that its minimal
polynomial lifts to a monic polynomial over the original ring. Inverting its
derivative gives a standard étale algebra. The kernel of evaluation at the
primitive element defines the required prime, and its residue field maps
isomorphically to the prescribed extension.
-/

@[expose] public section

open Polynomial
open scoped nonZeroDivisors

universe u v

namespace Algebra.Etale

private theorem exists_monic_primitive_residue_polynomial
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] :
    ∃ β : L, Algebra.adjoin p.ResidueField {β} = ⊤ ∧
      ∃ f : R[X], f.Monic ∧
        f.map (algebraMap R p.ResidueField) = minpoly p.ResidueField β := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element p.ResidueField L
  have hαint : IsIntegral p.ResidueField α := Algebra.IsIntegral.isIntegral α
  let m : (R ⧸ p)⁰ := IsLocalization.commonDenom (R ⧸ p)⁰
    (minpoly p.ResidueField α).support (minpoly p.ResidueField α).coeff
  let c : p.ResidueField := algebraMap (R ⧸ p) p.ResidueField m
  have hc : c ≠ 0 := (IsLocalization.map_units p.ResidueField m).ne_zero
  let β : L := c • α
  have hβ : IntermediateField.adjoin p.ResidueField {β} = ⊤ := by
    have hβeq : β = α * algebraMap p.ResidueField L c := by
      change c • α = α * algebraMap p.ResidueField L c
      rw [Algebra.smul_def, mul_comm]
    rw [hβeq, IntermediateField.adjoin_simple_mul_algebraMap α c hc]
    exact hα
  have hmin : minpoly p.ResidueField β = (minpoly p.ResidueField α).scaleRoots c :=
    IsIntegrallyClosed.minpoly_smul hc hαint
  have hlifts : (minpoly p.ResidueField α).scaleRoots c ∈
      Polynomial.lifts (algebraMap (R ⧸ p) p.ResidueField) := by
    apply IsLocalization.scaleRoots_commonDenom_mem_lifts (R ⧸ p)⁰
    rw [(minpoly.monic hαint).leadingCoeff]
    exact one_mem _
  obtain ⟨f₀, hf₀, _, hf₀monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts
    ((Polynomial.monic_scaleRoots_iff c).mpr (minpoly.monic hαint))
  obtain ⟨f, hf, _, hfmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective f₀) hf₀monic
  refine ⟨β, IntermediateField.adjoin_eq_top_iff.mp hβ, f, hfmonic, ?_⟩
  calc
    f.map (algebraMap R p.ResidueField) =
        (f.map (Ideal.Quotient.mk p)).map (algebraMap (R ⧸ p) p.ResidueField) := by
      rw [Polynomial.map_map, ← Ideal.Quotient.algebraMap_eq p,
        ← IsScalarTower.algebraMap_eq R (R ⧸ p) p.ResidueField]
    _ = (minpoly p.ResidueField α).scaleRoots c := by rw [hf, hf₀]
    _ = minpoly p.ResidueField β := hmin.symm

/-- Every finite separable extension of a residue field is the residue field
of a point in an actual étale neighborhood. The displayed equality makes the
isomorphism compatible with the canonical map from the original residue field. -/
@[stacks 00UD]
theorem exists_residueField_extension
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (q : Ideal R') (_ : q.IsPrime) (_ : q.LiesOver p),
      ∃ e : q.ResidueField ≃+* L,
        e.toRingHom.comp (Ideal.ResidueField.map p q (algebraMap R R') (q.over_def p)) =
          algebraMap p.ResidueField L := by
  obtain ⟨β, hβ, f, hfmonic, hf⟩ := exists_monic_primitive_residue_polynomial p L
  let : Algebra R L :=
    ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField)).toAlgebra
  let : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let P : StandardEtalePair R := {
    f := f
    monic_f := hfmonic
    g := f.derivative
    cond := ⟨1, 0, 1, by rw [mul_one, mul_zero, add_zero, pow_one]⟩
  }
  have hP : P.HasMap β := by
    constructor
    · change aeval β f = 0
      rw [← aeval_map_algebraMap p.ResidueField β f, hf]
      exact minpoly.aeval p.ResidueField β
    · change IsUnit (aeval β f.derivative)
      rw [← aeval_map_algebraMap p.ResidueField β f.derivative, ← derivative_map, hf]
      exact isUnit_iff_ne_zero.mpr
        ((Algebra.IsSeparable.isSeparable p.ResidueField β).aeval_derivative_ne_zero
          (minpoly.aeval p.ResidueField β))
  let φ : P.Ring →ₐ[R] L := P.lift β hP
  let q : Ideal P.Ring := RingHom.ker φ.toRingHom
  let : q.IsPrime := RingHom.ker_isPrime _
  have hker : RingHom.ker (algebraMap R L) = p := by
    rw [IsScalarTower.algebraMap_eq R p.ResidueField L,
      RingHom.ker_comp_of_injective _ (RingHom.injective _),
      Ideal.ker_algebraMap_residueField]
  let : q.LiesOver p := ⟨by
    change p = (RingHom.ker φ.toRingHom).comap (algebraMap R P.Ring)
    rw [RingHom.comap_ker, AlgHom.toRingHom_eq_coe,
      φ.comp_algebraMap, hker]
  ⟩
  have hunit : q.primeCompl ≤ (IsUnit.submonoid L).comap φ.toRingHom := by
    intro x hx
    change IsUnit (φ x)
    apply isUnit_iff_ne_zero.mpr
    exact hx
  let ψ : q.ResidueField →+* L := Ideal.ResidueField.lift q φ.toRingHom le_rfl hunit
  let ι : p.ResidueField →+* q.ResidueField :=
    Ideal.ResidueField.map p q (algebraMap R P.Ring) (q.over_def p)
  have hψι : ψ.comp ι = algebraMap p.ResidueField L := by
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro r
    simpa only [RingHom.comp_apply, ψ, ι, Ideal.ResidueField.map_algebraMap,
      Ideal.ResidueField.lift_algebraMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      IsScalarTower.algebraMap_apply R p.ResidueField L] using φ.commutes r
  let : Algebra p.ResidueField q.ResidueField := ι.toAlgebra
  let ψₐ : q.ResidueField →ₐ[p.ResidueField] L := {
    __ := ψ
    commutes' x := RingHom.congr_fun hψι x
  }
  have hβrange : β ∈ ψₐ.range := by
    refine ⟨algebraMap P.Ring q.ResidueField P.X, ?_⟩
    change ψ (algebraMap P.Ring q.ResidueField P.X) = β
    rw [Ideal.ResidueField.lift_algebraMap]
    exact P.lift_X β hP
  have hsurj : Function.Surjective ψₐ := by
    apply (AlgHom.range_eq_top ψₐ).mp
    apply top_unique
    rw [← hβ]
    exact Algebra.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hβrange)
  let e : q.ResidueField ≃+* L := RingEquiv.ofBijective ψ ⟨ψ.injective, hsurj⟩
  exact ⟨P.Ring, inferInstance, inferInstance, inferInstance,
    q, inferInstance, inferInstance, e, hψι⟩

end Algebra.Etale
