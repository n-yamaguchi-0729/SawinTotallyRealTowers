/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.PrimePairHartogs
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Hartogs extension for a regular pair

Two regular parameters suffice to extend sections across their common zero
locus. The parameters need not be prime, and the ring need not be a domain.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors Pointwise

namespace AlgebraicGeometry

universe u

private theorem pow_dvd_of_regular_pair
    {R : Type u} [CommRing R] {x y : R}
    (hx : IsSMulRegular R x) (hy : IsSMulRegular (QuotSMulTop x R) y)
    (n m : ℕ) {a : R} (h : x ^ n ∣ y ^ m * a) : x ^ n ∣ a := by
  induction n generalizing a with
  | zero => simpa only [pow_zero] using one_dvd a
  | succ n ih =>
    obtain ⟨b, hb⟩ := h
    have hzero : y ^ m • (Submodule.Quotient.mk a : QuotSMulTop x R) = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      change y ^ m * a ∈ x • (⊤ : Submodule R R)
      rw [hb, pow_succ', mul_assoc]
      exact Submodule.smul_mem_pointwise_smul _ x ⊤ Submodule.mem_top
    have ha : a ∈ x • (⊤ : Submodule R R) := by
      have ha0 := (hy.pow m).right_eq_zero_of_smul hzero
      rwa [Submodule.Quotient.mk_eq_zero] at ha0
    obtain ⟨c, -, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists a x ⊤).mp ha
    have hc' : a = x * c := hc.symm
    have hcancel : y ^ m * c = x ^ n * b := by
      apply hx
      change x * (y ^ m * c) = x * (x ^ n * b)
      calc
        x * (y ^ m * c) = y ^ m * a := by rw [hc']; ring
        _ = x * (x ^ n * b) := by rw [hb, pow_succ', mul_assoc]
    obtain ⟨d, hd⟩ := ih (a := c) ⟨b, hcancel⟩
    refine ⟨d, ?_⟩
    rw [hc', hd, pow_succ', mul_assoc]

/-- Sections extend uniquely across the common zero locus of a regular
pair. Regularity of both parameters is enough; neither primality nor a
domain hypothesis is needed. -/
theorem restrict_bijective_of_regular_pair
    (X : Scheme.{u}) [IsAffine X]
    (x y : Γ(X, ⊤))
    (hx : IsSMulRegular Γ(X, ⊤) x) (hy : IsSMulRegular Γ(X, ⊤) y)
    (hxy : IsSMulRegular (QuotSMulTop x Γ(X, ⊤)) y)
    (U : X.Opens) (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (hxU : X.basicOpen x ≤ U) (hyU : X.basicOpen y ≤ U) :
    Function.Bijective
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  let res : Γ(X, ⊤) ⟶ Γ(X, U) := X.presheaf.map (homOfLE le_top).op
  have hx0 : x ∈ nonZeroDivisors Γ(X, ⊤) :=
    mem_nonZeroDivisors_iff_left.mpr fun a ha => hx.right_eq_zero_of_smul ha
  have hy0 : y ∈ nonZeroDivisors Γ(X, ⊤) :=
    mem_nonZeroDivisors_iff_left.mpr fun a ha => hy.right_eq_zero_of_smul ha
  have hinj : Function.Injective res := by
    intro a b hab
    apply IsLocalization.injective Γ(X, X.basicOpen x) (Submonoid.powers_le.mpr hx0)
    have h := congrArg (X.presheaf.map (homOfLE hxU).op) hab
    have hcomp : res ≫ X.presheaf.map (homOfLE hxU).op =
        X.presheaf.map (homOfLE (show X.basicOpen x ≤ ⊤ from le_top)).op := by
      dsimp only [res]
      rw [← Functor.map_comp]
      congr 1
    change (X.presheaf.map (homOfLE le_top).op) a =
      (X.presheaf.map (homOfLE le_top).op) b
    simpa only [← CommRingCat.comp_apply, hcomp] using h
  refine ⟨hinj, ?_⟩
  intro s
  obtain ⟨a, n, ha⟩ :=
    exists_restrict_eq_pow_mul_of_basicOpen_le X U hU hU' x hx0 hxU s
  obtain ⟨b, m, hb⟩ :=
    exists_restrict_eq_pow_mul_of_basicOpen_le X U hU hU' y hy0 hyU s
  change res a = res x ^ n * s at ha
  change res b = res y ^ m * s at hb
  have hcross : y ^ m * a = x ^ n * b := by
    apply hinj
    rw [map_mul, map_pow, map_mul, map_pow, ha, hb]
    ring
  obtain ⟨c, hc⟩ := pow_dvd_of_regular_pair hx hxy n m ⟨b, hcross⟩
  refine ⟨c, ?_⟩
  have hxres : IsSMulRegular Γ(X, U) (res x) :=
    isSMulRegular_restrict_of_affine X U x hx0
  apply hxres.pow n
  change res x ^ n * res c = res x ^ n * s
  rw [← map_pow, ← map_mul, ← hc]
  simpa only [map_pow] using ha

end AlgebraicGeometry
