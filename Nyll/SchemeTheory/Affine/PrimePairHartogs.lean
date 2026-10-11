/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.RegularSection
import Nyll.SchemeTheory.RingTheory.Descent.PrimeAwayTensorDetection
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Hartogs extension after flat base change

A section on a quasi-compact, quasi-separated open containing a principal
open has a global numerator after multiplication by a power of its regular
defining section. Two prime parameters then give a global section uniquely.
-/


noncomputable section

open CategoryTheory TopologicalSpace
open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry

universe u v

/-- Clearing the denominator on a principal open gives an equality on the
larger open, because the defining global section acts injectively there. -/
theorem exists_restrict_eq_pow_mul_of_basicOpen_le
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (r : Γ(X, ⊤)) (hr : r ∈ nonZeroDivisors Γ(X, ⊤))
    (hRU : X.basicOpen r ≤ U) (s : Γ(X, U)) :
    ∃ (a : Γ(X, ⊤)) (n : ℕ),
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a =
        (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) ^ n * s := by
  let f : Γ(X, ⊤) ⟶ Γ(X, U) := X.presheaf.map (homOfLE le_top).op
  let rU : Γ(X, U) := f r
  let D := X.basicOpen rU
  let j : Γ(X, U) ⟶ Γ(X, D) :=
    X.presheaf.map (homOfLE (X.basicOpen_le rU)).op
  let k : Γ(X, ⊤) ⟶ Γ(X, D) := X.presheaf.map (homOfLE le_top).op
  have hD : D = X.basicOpen r := by
    exact (X.basicOpen_res r (homOfLE (show U ≤ ⊤ from le_top)).op).trans
      (inf_eq_right.mpr hRU)
  let : Algebra Γ(X, ⊤) Γ(X, D) := k.hom.toAlgebra
  let : IsLocalization.Away r Γ(X, D) :=
    (isAffineOpen_top X).isLocalization_of_eq_basicOpen r (homOfLE le_top) hD
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj r (j s)
  have hcomp : f ≫ j = k := by
    dsimp only [f, j, k]
    rw [← Functor.map_comp]
    rfl
  have hcomp_apply (a : Γ(X, ⊤)) : j (f a) = k a :=
    congrArg (fun t : Γ(X, ⊤) ⟶ Γ(X, D) => t a) hcomp
  refine ⟨a, n, ?_⟩
  apply restrict_basicOpen_injective_of_affine X U hU hU' r hr
  change j (f a) = j (rU ^ n * s)
  rw [map_mul, map_pow, hcomp_apply, show j rU = k r from hcomp_apply r]
  exact ha.symm.trans (mul_comm _ _)

/-- Flat base change preserves Hartogs extension across the complement of
two prime parameters. No normality of the affine scheme is needed. -/
theorem restrict_bijective_of_primePair
    {R : Type v} [CommRing R] [IsDomain R]
    (X : Scheme.{u}) [IsAffine X]
    [Algebra R Γ(X, ⊤)] [Module.Flat R Γ(X, ⊤)]
    {x y : R} (hx : Prime x) (hy : y ≠ 0) (hxy : ¬x ∣ y)
    (U : X.Opens) (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (hxU : X.basicOpen (algebraMap R Γ(X, ⊤) x) ≤ U)
    (hyU : X.basicOpen (algebraMap R Γ(X, ⊤) y) ≤ U) :
    Function.Bijective (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  let res : Γ(X, ⊤) →+* Γ(X, U) :=
    (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  let : Algebra R Γ(X, U) := (res.comp (algebraMap R Γ(X, ⊤))).toAlgebra
  let f : Γ(X, ⊤) →ₐ[R] Γ(X, U) := { res with commutes' := fun _ => rfl }
  have hregular {r : R} (hr : r ≠ 0) :
      algebraMap R Γ(X, ⊤) r ∈ nonZeroDivisors Γ(X, ⊤) := by
    refine mem_nonZeroDivisors_iff_left.mpr fun s hs => ?_
    apply (IsSMulRegular.of_ne_zero hr : IsSMulRegular Γ(X, ⊤) r).right_eq_zero_of_smul
    simpa only [Algebra.smul_def] using hs
  have hxf : IsSMulRegular Γ(X, U) x := by
    have h := isSMulRegular_restrict_of_affine X U
      (algebraMap R Γ(X, ⊤) x) (hregular hx.ne_zero)
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro s hs
    exact h.right_eq_zero_of_smul hs
  have hfi : Function.Injective f := by
    intro a b hab
    apply IsLocalization.injective Γ(X, X.basicOpen (algebraMap R Γ(X, ⊤) x))
      (Submonoid.powers_le.mpr (hregular hx.ne_zero))
    have h := congrArg (X.presheaf.map (homOfLE hxU).op) hab
    change (X.presheaf.map (homOfLE hxU).op) (res a) =
      (X.presheaf.map (homOfLE hxU).op) (res b) at h
    have hcomp : X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
        X.presheaf.map (homOfLE hxU).op =
        X.presheaf.map (homOfLE (show X.basicOpen (algebraMap R Γ(X, ⊤) x) ≤ ⊤
          from le_top)).op := by
      rw [← Functor.map_comp]
      congr 1
    change (X.presheaf.map (homOfLE le_top).op) a =
      (X.presheaf.map (homOfLE le_top).op) b
    simpa only [res, ← CommRingCat.comp_apply, hcomp] using h
  have hpow {r : R} (hr : r ≠ 0)
      (hrU : X.basicOpen (algebraMap R Γ(X, ⊤) r) ≤ U) :
      ∀ s : Γ(X, U), ∃ (a : Γ(X, ⊤)) (n : ℕ), f a = r ^ n • s := by
    intro s
    obtain ⟨a, n, ha⟩ := exists_restrict_eq_pow_mul_of_basicOpen_le X U hU hU'
      (algebraMap R Γ(X, ⊤) r) (hregular hr) hrU s
    refine ⟨a, n, ?_⟩
    change res a = (res (algebraMap R Γ(X, ⊤) r)) ^ n * s at ha
    change res a = algebraMap R Γ(X, U) (r ^ n) * s
    rw [map_pow]
    exact ha
  let F := FractionRing R
  let Ax := Localization.subalgebra.ofField F (Submonoid.powers x)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero))
  let Ay := Localization.subalgebra.ofField F (Submonoid.powers y)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hy))
  have hfx : Function.Bijective (f.toLinearMap.rTensor Ax) := by
    let : Module.Flat R Ax := IsLocalization.flat Ax (Submonoid.powers x)
    exact ⟨Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hfi,
      SchemeTheory.rTensor_surjective_of_pow_smul_mem_range Ax x f.toLinearMap
        (hpow hx.ne_zero hxU)⟩
  have hfy : Function.Bijective (f.toLinearMap.rTensor Ay) := by
    let : Module.Flat R Ay := IsLocalization.flat Ay (Submonoid.powers y)
    exact ⟨Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hfi,
      SchemeTheory.rTensor_surjective_of_pow_smul_mem_range Ay y f.toLinearMap
        (hpow hy hyU)⟩
  exact SchemeTheory.linearMap_bijective_of_tensor_primeAwayPair F hx hy hxy hxf
    f.toLinearMap hfx hfy

end AlgebraicGeometry
