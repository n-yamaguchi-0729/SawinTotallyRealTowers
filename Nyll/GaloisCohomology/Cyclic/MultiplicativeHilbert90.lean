/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Multiplicative Hilbert 90 in arbitrary universes

The cyclic norm-one condition defines an actual multiplicative cocycle by the
existing right-regular cyclic primitive. Noether's Hilbert 90 then supplies a
field-unit coboundary. For a subgroup of field automorphisms, passing to its
fixed field gives the same conclusion; an injective automorphism homomorphism
therefore suffices and need not be onto the full automorphism group.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace CyclicCohomology

open ProfiniteCohomology.Herbrand

/-- A norm-one element is the value at the generator of an actual cyclic cocycle. -/
theorem exists_mulCocycle_of_tateNorm_eq_one
    {G A : Type*} [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]
    (σ : G) (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) (a : A)
    (ha : tateNorm G A a = 1) :
    ∃ f : G → A, groupCohomology.IsMulCocycle₁ f ∧ f σ = a := by
  let f : G → A := fun g => g • a
  have hf : f ∈ rightRegularFunctionNormKernelSubgroup (G := G) (B := A) :=
    (rightRegularFunction_mem_normKernelSubgroup_iff (G := G) (B := A) f).mpr ha
  obtain ⟨b, hb⟩ := (rightRegularFunction_mem_augmentationSubgroup_iff
    (G := G) (B := A) σ f).mp
      (rightRegularFunction_normKernel_le_augmentationSubgroup
        (G := G) (B := A) σ hσ hf)
  let p : G → A := fun g => b g / b 1
  have hp1 : p 1 = 1 := div_self' (b 1)
  have hpstep (g : G) : p (g * σ) = (g • a) * p g := by
    have hbg : b (g * σ) = (g • a) * b g := eq_mul_of_mul_inv_eq (hb g)
    simp only [p, hbg, div_eq_mul_inv, mul_assoc]
  have hpow (n : ℕ) (g : G) : p (g * σ ^ n) = g • p (σ ^ n) * p g := by
    induction n with
    | zero => simp only [pow_zero, mul_one, hp1, smul_one, one_mul]
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, hpstep, ih, hpstep, smul_mul', ← mul_smul]
      ac_rfl
  refine ⟨p, ?_, ?_⟩
  · intro g h
    rw [rightRegularCyclicIndex_spec σ hσ h]
    exact hpow _ g
  · simpa only [one_mul, one_smul, hp1, mul_one] using hpstep 1

/-- Cyclic Hilbert 90 for field units with a Tate norm-one hypothesis, in arbitrary universes. -/
theorem exists_unit_coboundary_of_tateNorm_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : Lˣ) (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1) :
    ∃ y : Lˣ, (σ • y) / y = x := by
  obtain ⟨f, hf, hfx⟩ := exists_mulCocycle_of_tateNorm_eq_one σ hσ x hx
  obtain ⟨y, hy⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  exact ⟨y, (hy σ).trans hfx⟩

/-- Cyclic Hilbert 90 for the actual field norm, without restricting the field universes. -/
theorem exists_unit_coboundary_of_norm_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : Lˣ) (hx : Algebra.norm K (x : L) = 1) :
    ∃ y : Lˣ, (σ • y) / y = x := by
  apply exists_unit_coboundary_of_tateNorm_eq_one σ hσ x
  apply Units.ext
  change ((∏ τ : L ≃ₐ[K] L, τ • x : Lˣ) : L) = 1
  rw [Units.coe_prod]
  change (∏ τ : L ≃ₐ[K] L, τ (x : L)) = 1
  rw [← Algebra.norm_eq_prod_automorphisms, hx, map_one]

end CyclicCohomology

namespace groupCohomology

/-- Noether Hilbert 90 for any subgroup of the automorphisms of a finite field extension. -/
theorem exists_unit_coboundary_of_subgroup_cocycle
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (H : Subgroup (L ≃ₐ[K] L)) (f : H → Lˣ)
    (hf : ∀ g h : H, f (g * h) = (g : L ≃ₐ[K] L) • f h * f g) :
    ∃ y : Lˣ, ∀ g : H, ((g : L ≃ₐ[K] L) • y) / y = f g := by
  let e : H ≃* (L ≃ₐ[IntermediateField.fixedField H] L) :=
    IntermediateField.subgroupEquivAlgEquiv H
  have he (g : H) (x : Lˣ) : e g • x = (g : L ≃ₐ[K] L) • x := rfl
  have hes (g : L ≃ₐ[IntermediateField.fixedField H] L) (x : Lˣ) :
      (e.symm g : L ≃ₐ[K] L) • x = g • x := by
    rw [← he, e.apply_symm_apply]
  have hf' : IsMulCocycle₁ (fun g : L ≃ₐ[IntermediateField.fixedField H] L =>
      f (e.symm g)) := by
    intro g h
    change f (e.symm (g * h)) = g • f (e.symm h) * f (e.symm g)
    rw [map_mul, hf, hes]
  obtain ⟨y, hy⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
    (fun g : L ≃ₐ[IntermediateField.fixedField H] L => f (e.symm g)) hf'
  refine ⟨y, ?_⟩
  intro g
  simpa only [he, e.symm_apply_apply] using hy (e g)

/-- A faithful completed field action has Hilbert 90 without a surjectivity hypothesis
on its map to the full automorphism group. -/
theorem exists_unit_coboundary_of_injective_algAutHom
    {G K L : Type*} [Group G] [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (ρ : G →* (L ≃ₐ[K] L)) (hρ : Function.Injective ρ)
    (f : G → Lˣ) (hf : ∀ g h : G, f (g * h) = ρ g • f h * f g) :
    ∃ y : Lˣ, ∀ g : G, (ρ g • y) / y = f g := by
  let e : G ≃* ρ.range := MonoidHom.ofInjective hρ
  have he (g : G) : (e g : L ≃ₐ[K] L) = ρ g := rfl
  have hes (g : ρ.range) : ρ (e.symm g) = (g : L ≃ₐ[K] L) := by
    rw [← he, e.apply_symm_apply]
  have hf' (g h : ρ.range) :
      f (e.symm (g * h)) = (g : L ≃ₐ[K] L) • f (e.symm h) * f (e.symm g) := by
    rw [map_mul, hf, hes]
  obtain ⟨y, hy⟩ := exists_unit_coboundary_of_subgroup_cocycle
    ρ.range (fun g => f (e.symm g)) hf'
  refine ⟨y, ?_⟩
  intro g
  simpa only [he, e.symm_apply_apply] using hy (e g)

end groupCohomology
