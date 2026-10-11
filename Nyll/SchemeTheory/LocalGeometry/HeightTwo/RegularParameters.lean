/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# A prescribed first parameter in dimension two

In a two-dimensional regular local ring, an element whose cotangent class is
nonzero can be completed to a minimal pair of generators of the maximal
ideal.  If the prescribed element is prime, the resulting pair is a regular
sequence.

The localization theorem at the end obtains the cotangent dimension directly
from regularity and the height of the source prime.  The only extra datum it
needs is the geometric transversality statement that the prescribed local
equation does not lie in the square of the localized maximal ideal.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open RingTheory.Sequence

universe u

/-- In cotangent dimension two, a prime element with nonzero cotangent class
can be completed to a regular pair generating the maximal ideal. -/
theorem exists_regular_pair_of_finrank_cotangentSpace_eq_two
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hfin : Module.finrank (ResidueField R) (CotangentSpace R) = 2)
    {x : R} (hxPrime : Prime x) (hxMem : x ∈ maximalIdeal R)
    (hxSq : x ∉ maximalIdeal R ^ 2) :
    ∃ y : R, IsRegular R [x, y] ∧
      Ideal.ofList [x, y] = maximalIdeal R := by
  classical
  let m : Ideal R := maximalIdeal R
  let x' : m := ⟨x, hxMem⟩
  have hxCot : m.toCotangent x' ≠ 0 := by
    intro hx
    exact hxSq ((m.toCotangent_eq_zero x').mp hx)
  have hdim : 1 < Module.finrank (ResidueField R) (CotangentSpace R) := by
    omega
  obtain ⟨yCot, hxyCot⟩ :=
    exists_linearIndependent_pair_of_one_lt_finrank hdim hxCot
  obtain ⟨y', hyCot⟩ := m.toCotangent_surjective yCot
  let y : R := y'
  let v : Fin 2 → CotangentSpace R :=
    ![m.toCotangent x', m.toCotangent y']
  have hv : LinearIndependent (ResidueField R) v := by
    simpa only [v, Matrix.cons_val_zero, Matrix.cons_val_one, hyCot] using hxyCot
  have hvSpan : Submodule.span (ResidueField R) (Set.range v) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank' (by simp [hfin])
  have himage :
      m.toCotangent '' ({x', y'} : Set m) = Set.range v := by
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_range, v]
    constructor
    · rintro ⟨w, rfl | rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨x', Or.inl rfl, rfl⟩
      · exact ⟨y', Or.inr rfl, rfl⟩
  have hsubtypeSpan : Submodule.span R ({x', y'} : Set m) = ⊤ := by
    apply (CotangentSpace.span_image_eq_top_iff (R := R)).mp
    rw [himage]
    exact hvSpan
  have hmapSpan :
      (Submodule.span R ({x', y'} : Set m)).map m.subtype = m := by
    rw [hsubtypeSpan, Submodule.map_top, Submodule.range_subtype]
  have hspanSet : Ideal.span ({x, y} : Set R) = maximalIdeal R := by
    change Ideal.span ({x, y} : Set R) = m
    rw [← hmapSpan, Submodule.map_span]
    congr 1
    ext z
    simp [x', y, eq_comm]
  have hspan : Ideal.ofList [x, y] = maximalIdeal R := by
    change Ideal.span {r | r ∈ [x, y]} = maximalIdeal R
    rw [show {r | r ∈ [x, y]} = ({x, y} : Set R) by ext; simp]
    exact hspanSet
  have hyNotMem : y ∉ Ideal.span ({x} : Set R) := by
    intro hy
    have hle : Ideal.span ({x, y} : Set R) ≤ Ideal.span ({x} : Set R) := by
      apply Ideal.span_le.mpr
      intro z hz
      rcases hz with hzx | hzy
      · subst z
        exact Ideal.mem_span_singleton_self x
      · subst z
        exact hy
    have hmaxPrincipal : (maximalIdeal R).IsPrincipal := by
      refine ⟨x, le_antisymm ?_ ?_⟩
      · rw [← hspanSet]
        exact hle
      · exact Ideal.span_le.mpr (by simpa using hxMem)
    have hleOne :
        Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 :=
      IsLocalRing.finrank_cotangentSpace_le_one_iff.mpr hmaxPrincipal
    omega
  have hxRegular : IsSMulRegular R x := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro a ha
    have hxa : x * a = 0 := by
      simpa only [smul_eq_mul] using ha
    exact (mul_eq_zero.mp hxa).resolve_left hxPrime.ne_zero
  have hyRegular : IsSMulRegular (QuotSMulTop x R) y := by
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro a ha
    rw [Submodule.mem_smul_pointwise_iff_exists] at ha ⊢
    obtain ⟨c, -, hc⟩ := ha
    have hprod : y * a ∈ Ideal.span ({x} : Set R) := by
      rw [show y * a = x * c by simpa only [smul_eq_mul] using hc.symm]
      exact (Ideal.span ({x} : Set R)).mul_mem_right c
        (Ideal.mem_span_singleton_self x)
    have hspanPrime : (Ideal.span ({x} : Set R)).IsPrime :=
      Ideal.isPrime_span_singleton_of_prime hxPrime
    have haMem : a ∈ Ideal.span ({x} : Set R) :=
      (hspanPrime.mem_or_mem hprod).resolve_left hyNotMem
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp haMem
    refine ⟨d, Submodule.mem_top, ?_⟩
    simpa only [smul_eq_mul] using hd.symm
  have hweak : IsWeaklyRegular R [x, y] := by
    apply (isWeaklyRegular_cons_iff R x [y]).mpr
    refine ⟨hxRegular, ?_⟩
    exact (isWeaklyRegular_singleton_iff (QuotSMulTop x R) y).mpr hyRegular
  have hmem : ∀ r ∈ [x, y], r ∈ maximalIdeal R := by
    intro r hr
    rw [← hspan]
    exact Ideal.subset_span (by simpa using hr)
  exact ⟨y,
    IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal (L := R) hmem hweak,
    hspan⟩

/-- At a height-two prime of a regular domain, a transverse prime equation
extends to a regular pair of parameters in the local ring. -/
theorem exists_regular_pair_localizationAtPrime_of_height_eq_two
    {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    {t : A} (htPrime : Prime t) (htMem : t ∈ P)
    (htSq : algebraMap A (Localization.AtPrime P) t ∉
      maximalIdeal (Localization.AtPrime P) ^ 2) :
    ∃ y : Localization.AtPrime P,
      IsRegular (Localization.AtPrime P)
        [algebraMap A (Localization.AtPrime P) t, y] ∧
      Ideal.ofList [algebraMap A (Localization.AtPrime P) t, y] =
        maximalIdeal (Localization.AtPrime P) := by
  let R := Localization.AtPrime P
  have hdim :
      Module.finrank (ResidueField R) (CotangentSpace R) = 2 := by
    have hdim' :
        ((Module.finrank (ResidueField R) (CotangentSpace R) : ℕ∞) :
            WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by
      calc
        ((Module.finrank (ResidueField R) (CotangentSpace R) : ℕ∞) :
            WithBot ℕ∞) = ringKrullDim R :=
          (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
        _ = (P.height : WithBot ℕ∞) :=
          IsLocalization.AtPrime.ringKrullDim_eq_height P R
        _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
          congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hP
    exact ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp hdim')
  have htLocalMem : algebraMap A R t ∈ maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R P t).mpr htMem
  have htLocalNe : algebraMap A R t ≠ 0 := by
    intro htZero
    exact htPrime.ne_zero
      ((IsLocalization.injective R P.primeCompl_le_nonZeroDivisors)
        (by simpa only [map_zero] using htZero))
  have htSpanPrime :
      (Ideal.span ({t} : Set A)).map (algebraMap A R) |>.IsPrime := by
    let : (Ideal.span ({t} : Set A)).IsPrime :=
      Ideal.isPrime_span_singleton_of_prime htPrime
    exact Ideal.isPrime_map_of_isLocalizationAtPrime P
      (P.span_singleton_le_iff_mem.mpr htMem)
  have htLocalPrime : Prime (algebraMap A R t) := by
    apply (Ideal.span_singleton_prime htLocalNe).mp
    simpa only [Ideal.map_span, Set.image_singleton] using htSpanPrime
  exact exists_regular_pair_of_finrank_cotangentSpace_eq_two
    hdim htLocalPrime htLocalMem htSq

end EtaleFundamentalGroups

end
