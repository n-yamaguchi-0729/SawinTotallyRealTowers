/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.StrictHenselianFiniteDomainPoint
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Lifting a specified geometric closed point to a finite domain

The prescribed local map to an algebraically closed field induces the scalar
map on the base residue field. The finite residue extension embeds over that
scalar map into the same field. Composing with the residue map constructs a
local point over the prescribed one. Strict Henselianity then makes every
automorphism of the finite algebra fix this constructed point.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- A specified geometric closed point of a strictly Henselian local ring
lifts to a finite domain algebra over the same algebraically closed field,
and every algebra automorphism fixes the resulting point. -/
theorem exists_local_hom_finiteDomain_fixed_of_strictHenselian
    (R : Type u) (B : Type v) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (ψ : R →+* Ω) [IsLocalHom ψ] :
    ∃ φ : B →+* Ω, IsLocalHom φ ∧ φ.comp (algebraMap R B) = ψ ∧
      ∀ σ : B ≃ₐ[R] B, φ.comp σ.toRingEquiv.toRingHom = φ := by
  let : IsLocalRing B := isLocalRing_of_finite_domain_henselian R B
  have hcontract : (IsLocalRing.maximalIdeal B).under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R)
        (IsLocalRing.maximalIdeal B))
  let : IsLocalHom (algebraMap R B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R B)).out 1 5).mpr hcontract
  let k := IsLocalRing.ResidueField R
  let l := IsLocalRing.ResidueField B
  let : Algebra k Ω := (IsLocalRing.ResidueField.lift ψ).toAlgebra
  let e : l →ₐ[k] Ω := IsAlgClosed.lift (R := k) (S := l) (M := Ω)
  let φ : B →+* Ω := e.toRingHom.comp (IsLocalRing.residue B)
  let : IsLocalHom φ := inferInstance
  refine ⟨φ, inferInstance, ?_, fun σ =>
    strictHenselian_finiteDomain_aut_fixes_closedPoint R B φ σ⟩
  ext r
  change e (IsLocalRing.residue B (algebraMap R B r)) = ψ r
  rw [← IsLocalRing.ResidueField.algebraMap_residue (R := R) (S := B), e.commutes]
  exact IsLocalRing.ResidueField.lift_residue_apply ψ r

end SchemeTheory
