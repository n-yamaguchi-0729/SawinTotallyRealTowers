/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Integral elements in a smooth generic fibre

Let `R` be a normal domain with fraction field `K`, and let `S / R` be
smooth.  Every element of `S ⊗[R] K` which is integral over `S` already
comes from `S`.

This is the elementwise form of smooth base change for integral closure.  It
is useful for finite-etale generic fibres: primitive idempotents and elements
supported on a selected field component are integral, hence descend to the
original finite-etale algebra.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uR uS uK

private theorem tensorProduct_integralClosure_eq_tmul_one
    {R : Type uR} {S : Type uS} {K : Type uK}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (z : S ⊗[R] integralClosure R K) :
    ∃ s : S, z = s ⊗ₜ[R] (1 : integralClosure R K) := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro s x
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral x.2
    have hx : x = algebraMap R (integralClosure R K) r := by
      apply Subtype.ext
      exact hr.symm
    refine ⟨r • s, ?_⟩
    rw [hx]
    rw [show algebraMap R (integralClosure R K) r =
      r • (1 : integralClosure R K) by simp [Algebra.smul_def]]
    exact TensorProduct.tmul_smul
      (R := R) (R' := R) (M := S) (N := integralClosure R K)
      r s (1 : integralClosure R K)
  · rintro x y ⟨sx, hsx⟩ ⟨sy, hsy⟩
    refine ⟨sx + sy, ?_⟩
    rw [hsx, hsy]
    exact (TensorProduct.add_tmul sx sy (1 : integralClosure R K)).symm

/-- If `S / R` is smooth and `R` is normal, every `S`-integral element of
the generic fibre `S ⊗[R] K` is the image of an element of `S`.

The preimage is produced by the smooth integral-closure comparison; no
normality or component hypothesis on `S` is assumed. -/
theorem exists_eq_includeLeft_of_isIntegral_genericFiber_of_smooth
    {R : Type uR} {S : Type uS} {K : Type uK}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (x : S ⊗[R] K) (hx : IsIntegral S x) :
    ∃ s : S,
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] K) s = x := by
  let hCompare :=
    TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := R) (S := S) (B := K)
  obtain ⟨z, hz⟩ := hCompare.2 ⟨x, hx⟩
  obtain ⟨s, rfl⟩ :=
    tensorProduct_integralClosure_eq_tmul_one
      (R := R) (S := S) (K := K) z
  refine ⟨s, ?_⟩
  exact congrArg Subtype.val hz

end EtaleFundamentalGroups

end
