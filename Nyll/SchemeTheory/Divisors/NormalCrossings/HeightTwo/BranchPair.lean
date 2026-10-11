/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Regular.Flat
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Nyll.SchemeTheory.Divisors.NormalCrossings.Basic

/-!
# Two strict-normal-crossings branches at a height-two point

If a height-two prime contains two distinct labelled branches of a split
strict-normal-crossings chart, those two branch equations form a regular
system of parameters after localization at that prime.

The proof first moves the two indexed occurrences to the front of the given
regular system.  Their two-term prefix remains weakly regular after
localization.  For generation, the ideal spanned by the two equations is
prime: after quotienting by the first equation, the second is again a member
of a regular system and hence is prime.  Its height is at least two, so its
inclusion in the given height-two prime is an equality.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open RingTheory.Sequence

universe u

/-- At a height-two point containing two distinct parameters of a split strict
normal crossings chart, the two localized parameters are a regular pair and
generate the localized maximal ideal.  In particular this applies to any two
distinct labelled branches through the point. -/
theorem regular_pair_localizationAtPrime_of_two_splitStrictNormalCrossingsParameters
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A] {d r : ℕ} {f : A} {t : Fin d → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i j : Fin d) (hij : i ≠ j)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P) (htjP : t j ∈ P) :
    IsRegular (Localization.AtPrime P)
        [algebraMap A (Localization.AtPrime P) (t i),
          algebraMap A (Localization.AtPrime P) (t j)] ∧
      Ideal.ofList
          [algebraMap A (Localization.AtPrime P) (t i),
            algebraMap A (Localization.AtPrime P) (t j)] =
        maximalIdeal (Localization.AtPrime P) := by
  classical
  let ps : List A := List.ofFn t
  let psAfterI : List A := ps.eraseIdx i.1
  let qs : List A := psAfterI.erase (t j)
  have hiIndex : i.1 < ps.length := by simp [ps]
  have hjIndex : j.1 < ps.length := by simp [ps]
  have hgetI : ps[i.1] = t i := by simp [ps]
  have hgetJ : ps[j.1] = t j := by simp [ps]
  have hjAfterI : t j ∈ psAfterI := by
    change t j ∈ ps.eraseIdx i.1
    rw [List.mem_eraseIdx_iff_getElem]
    exact ⟨j.1, hjIndex, fun h ↦ hij (Fin.ext h.symm), hgetJ⟩
  have hperm : List.Perm (t i :: t j :: qs) ps := by
    have hfirst : List.Perm (ps[i.1] :: psAfterI) ps := by
      simpa only [psAfterI] using List.getElem_cons_eraseIdx_perm hiIndex
    have hsecond : List.Perm (t i :: t j :: qs) (t i :: psAfterI) :=
      List.Perm.cons (t i) (List.perm_cons_erase hjAfterI).symm
    rw [hgetI] at hfirst
    exact hsecond.trans hfirst
  have hregPerm : IsRegular A (t i :: t j :: qs) :=
    IsLocalRing.isRegular_of_perm hNC.2.2.1.1 (by
      simpa only [ps] using hperm.symm)
  have hgenPerm : Ideal.ofList (t i :: t j :: qs) = maximalIdeal A := by
    rw [← hNC.2.2.1.2]
    apply congrArg Ideal.span
    ext x
    exact hperm.mem_iff
  have hweakPair : IsWeaklyRegular A [t i, t j] := by
    apply ((isWeaklyRegular_append_iff A [t i, t j] qs).mp ?_).1
    simpa only [List.cons_append, List.nil_append] using
      hregPerm.toIsWeaklyRegular
  have hregularLocalized :
      IsRegular (Localization.AtPrime P)
        [algebraMap A (Localization.AtPrime P) (t i),
          algebraMap A (Localization.AtPrime P) (t j)] := by
    simpa using hweakPair.isRegular_of_isLocalization_of_mem
      (Localization.AtPrime P) P (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact htiP
        · exact htjP)
  let I : Ideal A := Ideal.span {t i}
  let Q : Ideal A := Ideal.ofList [t i, t j]
  have htiPrime : Prime (t i) :=
    Kummer.prime_of_mem_regularSystem hNC.2.2.1.1 hNC.2.2.1.2
      (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hIprime : I.IsPrime := by
    apply (Ideal.span_singleton_prime htiPrime.ne_zero).mpr
    exact htiPrime
  let : I.IsPrime := hIprime
  let S := A ⧸ I
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIprime.ne_top
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective A S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hquot := Kummer.regularSystem_quotientHead hregPerm hgenPerm
  have hregS :
      IsRegular S ((t j :: qs).map (Ideal.Quotient.mk I)) := by
    simpa only [I, S] using hquot.1
  have hgenS :
      Ideal.ofList ((t j :: qs).map (Ideal.Quotient.mk I)) =
        maximalIdeal S := by
    calc
      Ideal.ofList ((t j :: qs).map (Ideal.Quotient.mk I)) =
          (maximalIdeal A).map (Ideal.Quotient.mk I) := by
        simpa only [I, S] using hquot.2
      _ = maximalIdeal S :=
        IsLocalRing.map_maximalIdeal_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have htjBarPrime : Prime (Ideal.Quotient.mk I (t j)) :=
    Kummer.prime_of_mem_regularSystem hregS hgenS (by simp)
  let J : Ideal S := Ideal.span {Ideal.Quotient.mk I (t j)}
  have hJprime : J.IsPrime := by
    apply (Ideal.span_singleton_prime htjBarPrime.ne_zero).mpr
    exact htjBarPrime
  let : J.IsPrime := hJprime
  have hmapQ : Q.map (Ideal.Quotient.mk I) = J := by
    dsimp only [Q, J, I]
    rw [Ideal.ofList_cons, Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq]
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span]
    simp
    rfl
  have hIQ : I ≤ Q := by
    change Ideal.span {t i} ≤ Ideal.ofList [t i, t j]
    rw [Ideal.ofList_cons, Ideal.ofList_cons, Ideal.ofList_nil,
      sup_bot_eq]
    exact le_sup_left
  have hcomapJ : J.comap (Ideal.Quotient.mk I) = Q := by
    rw [← hmapQ, Ideal.comap_map_of_surjective _
      Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left]
    exact hIQ
  have hQprime : Q.IsPrime := by
    rw [← hcomapJ]
    exact Ideal.comap_isPrime (Ideal.Quotient.mk I) J
  let : Q.IsPrime := hQprime
  have htjNotI : t j ∉ I := by
    intro htjI
    exact htjBarPrime.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr htjI)
  have hIQlt : I < Q := by
    refine lt_of_le_of_ne hIQ ?_
    intro hIQeq
    apply htjNotI
    rw [hIQeq]
    exact Ideal.subset_span (by simp)
  have hIheight : I.height = 1 := by
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr htiPrime.ne_zero)
      htiPrime.not_isUnit
  have htwo_le_Q : (2 : ℕ∞) ≤ Q.height := by
    have hheight := Ideal.height_add_one_le_of_lt_of_isPrime hIQlt
    rw [hIheight] at hheight
    simpa only [one_add_one_eq_two] using hheight
  have hQleP : Q ≤ P := by
    change Ideal.ofList [t i, t j] ≤ P
    rw [Ideal.ofList_cons, Ideal.ofList_cons, Ideal.ofList_nil,
      sup_bot_eq]
    exact sup_le
      (P.span_singleton_le_iff_mem.mpr htiP)
      (P.span_singleton_le_iff_mem.mpr htjP)
  have hPheight_le_Q : P.height ≤ Q.height := by
    rw [hP]
    exact htwo_le_Q
  have hQP : Q = P :=
    Ideal.eq_of_le_of_height_le (I := Q) (J := P) hQleP hPheight_le_Q
  refine ⟨hregularLocalized, ?_⟩
  calc
    Ideal.ofList
        [algebraMap A (Localization.AtPrime P) (t i),
          algebraMap A (Localization.AtPrime P) (t j)] =
        Q.map (algebraMap A (Localization.AtPrime P)) := by
      rw [Ideal.map_ofList]
      rfl
    _ = P.map (algebraMap A (Localization.AtPrime P)) := congrArg _ hQP
    _ = maximalIdeal (Localization.AtPrime P) :=
      Localization.AtPrime.map_eq_maximalIdeal

end EtaleFundamentalGroups

end
