/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular pairs on a finite normalization via the trace dual

This file develops the trace-dual argument which avoids factoriality and
normality assumptions on the base.  For a finite separable extension `L / K`
and the finite normalization `B` of a Noetherian domain `A`, the trace dual
of `B` is a nonzero finite `B`-module.  Its double trace dual is `B`, by the
determinant trick and integral closedness of `B` inside `L`.  A regular pair
on `A` can then test membership in that double trace dual.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped Pointwise

open Module
open nonZeroDivisors
open RingTheory.Sequence

universe u v w

section TraceDualFinite

variable {A : Type u} {K : Type v} {L : Type w}
variable [CommRing A] [hA_domain : IsDomain A] [hA_noetherian : IsNoetherianRing A]
variable [hK_field : Field K] [hAK : Algebra A K] [hfrac : IsFractionRing A K]
variable [Field L] [Algebra A L] [hKL : Algebra K L] [hAKL : IsScalarTower A K L]
variable [hfiniteDimensional : FiniteDimensional K L]
variable [hseparable : Algebra.IsSeparable K L]
variable [hBfinite : Module.Finite A (integralClosure A L)]

local notation "B" => integralClosure A L

/-- The trace dual of a finite normalization is finite over the normalization.

The key point is that the trace pairing embeds it into the `A`-dual of `B`.
That dual is finite because `A` is Noetherian, and restriction of scalars then
gives finite generation over `B`. -/
private theorem traceDual_one_finite :
    Module.Finite B (Submodule.traceDual A K (1 : Submodule B L)) := by
  let J : Submodule B L := 1
  let I : Submodule B L := Submodule.traceDual A K J
  let f : B →ₗ[A] L := (IsScalarTower.toAlgHom A B L).toLinearMap
  let fJ : B →ₗ[A] J.restrictScalars A :=
    f.codRestrict (J.restrictScalars A) fun b ↦ by
      rw [Submodule.restrictScalars_mem, Submodule.mem_one]
      exact ⟨b, rfl⟩
  have hfJ : Function.Surjective fJ := by
    rintro ⟨z, hz⟩
    rw [Submodule.restrictScalars_mem, Submodule.mem_one] at hz
    obtain ⟨b, hb⟩ := hz
    exact ⟨b, Subtype.ext hb⟩
  let : Module.Finite A (J.restrictScalars A) :=
    Module.Finite.of_surjective fJ hfJ
  let : IsLocalizedModule A⁰ f :=
    (isLocalizedModule_iff_isLocalization
      (S := A⁰) (R := A) (A := B) (Aₛ := L)).mpr
        (IsIntegralClosure.isLocalization A K L B)
  have hspanLocalized :
      Submodule.span K (f '' (Set.univ : Set B)) = ⊤ :=
    span_eq_top_of_isLocalizedModule K A⁰ f (by simp)
  have hspan :
      Submodule.span K ((J.restrictScalars A : Submodule A L) : Set L) = ⊤ := by
    change Submodule.span K ((J : Submodule B L) : Set L) = ⊤
    change Submodule.span K (((1 : Submodule B L) : Set L)) = ⊤
    rw [Submodule.one_eq_range, LinearMap.coe_range]
    change Submodule.span K (Set.range fun b : B ↦ algebraMap B L b) = ⊤
    rw [Set.image_univ] at hspanLocalized
    change Submodule.span K (Set.range fun b : B ↦ algebraMap B L b) = ⊤ at hspanLocalized
    exact hspanLocalized
  let D : Submodule A L :=
    (Algebra.traceForm K L).dualSubmodule (J.restrictScalars A)
  have hDfinite : Module.Finite A D := by
    let : IsNoetherian A (Module.Dual A (J.restrictScalars A)) :=
      isNoetherian_linearMap A A (J.restrictScalars A)
    exact Module.Finite.of_injective
      ((Algebra.traceForm K L).dualSubmoduleToDual (J.restrictScalars A))
      ((Algebra.traceForm K L).dualSubmoduleToDual_injective
        (traceForm_nondegenerate K L) (J.restrictScalars A) hspan)
  let : Module.Finite A D := hDfinite
  have hID : I.restrictScalars A = D := rfl
  let : Module.Finite A (I.restrictScalars A) :=
    Module.Finite.equiv (LinearEquiv.ofEq D (I.restrictScalars A) hID.symm)
  let : Module.Finite A I :=
    Module.Finite.equiv
      ((Submodule.restrictScalarsEquiv A B L I).restrictScalars A)
  exact Module.Finite.of_restrictScalars_finite A B I

omit [IsNoetherianRing A] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The trace dual of a finite normalization is nonzero.

Choose finitely many `A`-module generators of `B` and clear the denominators
of their traces simultaneously.  The resulting nonzero element of `A` lies
in the trace dual by linearity. -/
private theorem traceDual_one_ne_bot :
    Submodule.traceDual A K (1 : Submodule B L) ≠ ⊥ := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := B)
  let t : Fin n → K := fun i ↦ Algebra.trace K L (algebraMap B L (g i))
  obtain ⟨s, hs⟩ :=
    IsLocalization.exist_integer_multiples A⁰ Finset.univ t
  let d : L := algebraMap A L (s : A)
  let ℓ : B →ₗ[A] K :=
    ((Algebra.traceForm K L d).restrictScalars A).comp
      (IsScalarTower.toAlgHom A B L).toLinearMap
  let P : Submodule A B := (1 : Submodule A K).comap ℓ
  have hgP : Set.range g ⊆ P := by
    rintro _ ⟨i, rfl⟩
    change ℓ (g i) ∈ (1 : Submodule A K)
    rw [Submodule.mem_one]
    have hi := hs i (Finset.mem_univ i)
    change ∃ a : A, algebraMap A K a = (s : A) • t i at hi
    obtain ⟨a, ha⟩ := hi
    refine ⟨a, ha.trans ?_⟩
    simp only [ℓ, t, d, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      Algebra.traceForm_apply]
    rw [Algebra.smul_def]
    calc
      algebraMap A K (s : A) * Algebra.trace K L (algebraMap B L (g i)) =
          Algebra.trace K L
            (algebraMap A K (s : A) • algebraMap B L (g i)) := by
              simpa only [Algebra.smul_def, Algebra.algebraMap_self_apply] using
                ((Algebra.trace K L).map_smul
                  (algebraMap A K (s : A)) (algebraMap B L (g i))).symm
      _ = Algebra.trace K L
          (algebraMap A L (s : A) *
            (IsScalarTower.toAlgHom A B L).toLinearMap (g i)) := by
              congr 1
              rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A K L]
              rfl
  have hP : P = ⊤ := by
    apply top_unique
    rw [← hg]
    exact Submodule.span_le.mpr hgP
  have hdmem : d ∈ Submodule.traceDual A K (1 : Submodule B L) := by
    rw [Submodule.mem_traceDual]
    intro z hz
    rw [Submodule.mem_one] at hz
    obtain ⟨b, rfl⟩ := hz
    have hbP : b ∈ P := by rw [hP]; exact Submodule.mem_top
    change ℓ b ∈ (1 : Submodule A K) at hbP
    change Algebra.traceForm K L d
      ((IsScalarTower.toAlgHom A B L).toLinearMap b) ∈ (1 : Submodule A K) at hbP
    have htrace :
        Algebra.traceForm K L d (algebraMap B L b) ∈ (1 : Submodule A K) := by
      simpa only [AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply] using hbP
    exact Submodule.mem_one.mp htrace
  have hsne : (s : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.property
  have hdne : d ≠ 0 := by
    intro hd
    apply hsne
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa only [map_zero, d, IsScalarTower.algebraMap_apply A K L] using hd
  intro hbot
  rw [hbot] at hdmem
  rw [Submodule.mem_bot] at hdmem
  exact hdne hdmem

/-- The double trace dual of a finite normalization is the normalization.

For `I = Bᵛ`, an element of `Iᵛ` stabilizes `I`: this follows by moving
the extra factor across the commutative trace pairing.  Since `I` is nonzero
and finite, the determinant trick makes that element integral over `B`; the
integral closedness of `B` inside `L` then puts it back in `B`. -/
theorem traceDual_traceDual_one_eq_one_of_finite :
    Submodule.traceDual A K
      (Submodule.traceDual A K (1 : Submodule B L)) = 1 := by
  let I : Submodule B L := Submodule.traceDual A K (1 : Submodule B L)
  let : Module.Finite B I := traceDual_one_finite (A := A) (K := K) (L := L)
  have hIne : I ≠ ⊥ := traceDual_one_ne_bot (A := A) (K := K) (L := L)
  apply le_antisymm
  · intro z hz
    have hstable : ∀ i ∈ I, z • i ∈ I := by
      intro i hi
      rw [Submodule.mem_traceDual]
      intro a ha
      rw [Submodule.mem_one] at ha
      obtain ⟨r, rfl⟩ := ha
      rw [Submodule.mem_traceDual] at hz
      have hri : r • (i : L) ∈ I := I.smul_mem r hi
      have htrace := hz (r • (i : L)) hri
      simpa only [Algebra.traceForm_apply, Algebra.smul_def,
        Algebra.algebraMap_self_apply, mul_assoc, mul_left_comm, mul_comm] using htrace
    have hzIntegral : IsIntegral B z :=
      isIntegral_of_smul_mem_submodule I hIne
        (Module.Finite.iff_fg.mp inferInstance) z hstable
    rw [Submodule.mem_one]
    exact IsIntegrallyClosedIn.isIntegral_iff.mp hzIntegral
  · exact Submodule.le_traceDual_traceDual

include K hA_domain hA_noetherian hK_field hAK hfrac hKL hAKL
  hfiniteDimensional hseparable hBfinite in
/-- A regular pair on a Noetherian domain remains a divisibility test on its
finite normalization in a finite separable field extension.

Concretely, if `y * b = x * c` in the normalization and `[x, y]` is regular
on `A`, then `x` divides `b` in the normalization.  This proof uses neither a
UFD instance, integral closedness of `A`, nor primality of `x`. -/
theorem exists_integralClosure_factor_of_mul_eq_mul_of_isRegular
    {x y : A} (hregular : IsRegular A [x, y])
    {b c : B}
    (hbc : algebraMap A B y * b = algebraMap A B x * c) :
    ∃ d : B, b = algebraMap A B x * d := by
  have hpair := (isRegular_cons_iff A x [y]).mp hregular
  have hx : x ≠ 0 := by
    intro hxzero
    exact one_ne_zero (hpair.1.right_eq_zero_of_smul (by simp [hxzero]))
  have hxK : algebraMap A K x ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne hx
  have hxL : algebraMap A L x ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K L]
    simpa only [map_zero] using (algebraMap K L).injective.ne hxK
  have hyRegular : IsSMulRegular (QuotSMulTop x A) y :=
    ((isRegular_cons_iff (QuotSMulTop x A) y []).mp hpair.2).1
  have hbcL : algebraMap A L y * (b : L) = algebraMap A L x * (c : L) :=
    congrArg Subtype.val hbc
  let z : L := (b : L) / algebraMap A L x
  have hxz : algebraMap A L x * z = (b : L) := by
    dsimp [z]
    rw [div_eq_mul_inv]
    calc
      algebraMap A L x * ((b : L) * (algebraMap A L x)⁻¹) =
          (b : L) * (algebraMap A L x * (algebraMap A L x)⁻¹) := by
            ac_rfl
      _ = (b : L) := by rw [mul_inv_cancel₀ hxL, mul_one]
  have hyz : algebraMap A L y * z = (c : L) := by
    apply mul_left_cancel₀ hxL
    calc
      algebraMap A L x * (algebraMap A L y * z) =
          algebraMap A L y * (algebraMap A L x * z) := by ac_rfl
      _ = algebraMap A L y * (b : L) := by rw [hxz]
      _ = algebraMap A L x * (c : L) := hbcL
  let I : Submodule B L := Submodule.traceDual A K (1 : Submodule B L)
  have hzDual : z ∈ Submodule.traceDual A K I := by
    rw [Submodule.mem_traceDual]
    intro i hi
    let q : K := Algebra.traceForm K L z i
    have hbi : Algebra.traceForm K L i (b : L) ∈ (algebraMap A K).range := by
      rw [Submodule.mem_traceDual] at hi
      exact hi (b : L) (Submodule.mem_one.mpr ⟨b, rfl⟩)
    have hci : Algebra.traceForm K L i (c : L) ∈ (algebraMap A K).range := by
      rw [Submodule.mem_traceDual] at hi
      exact hi (c : L) (Submodule.mem_one.mpr ⟨c, rfl⟩)
    obtain ⟨u, hu⟩ := hbi
    obtain ⟨v, hv⟩ := hci
    have hbx : (b : L) = algebraMap A K x • z := by
      rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply A K L]
      exact hxz.symm
    have hcy : (c : L) = algebraMap A K y • z := by
      rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply A K L]
      exact hyz.symm
    have huq : algebraMap A K u = algebraMap A K x * q := by
      calc
        algebraMap A K u = Algebra.traceForm K L i (b : L) := hu
        _ = Algebra.traceForm K L i (algebraMap A K x • z) := by rw [← hbx]
        _ = algebraMap A K x • Algebra.traceForm K L i z := by rw [map_smul]
        _ = algebraMap A K x * q := by
          simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, q,
            Algebra.traceForm_apply, mul_comm]
    have hvq : algebraMap A K v = algebraMap A K y * q := by
      calc
        algebraMap A K v = Algebra.traceForm K L i (c : L) := hv
        _ = Algebra.traceForm K L i (algebraMap A K y • z) := by rw [← hcy]
        _ = algebraMap A K y • Algebra.traceForm K L i z := by rw [map_smul]
        _ = algebraMap A K y * q := by
          simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, q,
            Algebra.traceForm_apply, mul_comm]
    have hyuxv : y * u = x * v := by
      apply IsFractionRing.injective A K
      rw [map_mul, map_mul, huq, hvq]
      simp only [mul_left_comm]
    have hyuMem : y • u ∈ x • (⊤ : Submodule A A) := by
      rw [Submodule.mem_smul_pointwise_iff_exists]
      refine ⟨v, Submodule.mem_top, ?_⟩
      simpa only [smul_eq_mul] using hyuxv.symm
    have huMem : u ∈ x • (⊤ : Submodule A A) :=
      (isSMulRegular_quotient_iff_mem_of_smul_mem
        (x • (⊤ : Submodule A A)) y).mp hyRegular u hyuMem
    obtain ⟨w, -, hwu⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp huMem
    simp only [smul_eq_mul] at hwu
    refine ⟨w, ?_⟩
    apply mul_left_cancel₀ hxK
    calc
      algebraMap A K x * algebraMap A K w = algebraMap A K (x * w) := by rw [map_mul]
      _ = algebraMap A K u := by rw [hwu]
      _ = algebraMap A K x * q := huq
  have hzOne : z ∈ (1 : Submodule B L) := by
    rw [← traceDual_traceDual_one_eq_one_of_finite (A := A) (K := K) (L := L)]
    exact hzDual
  rw [Submodule.mem_one] at hzOne
  obtain ⟨d, hd⟩ := hzOne
  refine ⟨d, Subtype.ext ?_⟩
  change (b : L) = algebraMap A L x * algebraMap B L d
  rw [hd]
  exact hxz.symm

end TraceDualFinite

end EtaleFundamentalGroups
