/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Nyll.SchemeTheory.LocalGeometry.HeightTwo.RegularParameters
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Nyll.SchemeTheory.Divisors.NormalCrossings.Basic

/-!
# Strict-normal-crossings parameters at height two

A branch of a strict normal crossings divisor stays a regular parameter after
localization at every height-two point on that branch.  The key input is the
scheme-level regularity of the branch quotient.  Quotienting after localizing
is identified with localizing the branch quotient; hence the former is a
one-dimensional regular local ring.  If the branch equation lay in the square
of the localized maximal ideal, Nakayama would make that maximal ideal
principal, contradicting its two-dimensional cotangent space.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open RingTheory.Sequence

universe u

private def quotientPrimeOfLe
    {R : Type u} [CommRing R] {I P : Ideal R} [P.IsPrime] (hIP : I ≤ P) :
    PrimeSpectrum (R ⧸ I) :=
  ⟨P.map (Ideal.Quotient.mk I),
    Ideal.isPrime_map_quotientMk_of_isPrime hIP⟩

private theorem primeCompl_map_quotient_eq
    {R : Type u} [CommRing R] {I P : Ideal R} [P.IsPrime] (hIP : I ≤ P) :
    P.primeCompl.map (Ideal.Quotient.mk I) =
      (quotientPrimeOfLe hIP).asIdeal.primeCompl := by
  apply Submonoid.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩ hy
    rcases (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective).mp hy with ⟨z, hzP, hzx⟩
    have hxz : x - z ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      rw [map_sub, hzx, sub_self]
    exact hx (by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        P.add_mem (hIP hxz) hzP)
  · intro hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hxP : x ∉ P := by
      intro hx
      exact hy (Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hx)
    exact ⟨x, hxP, rfl⟩

private noncomputable def quotientLocalizationEquiv
    {R : Type u} [CommRing R] {I P : Ideal R} [P.IsPrime] (hIP : I ≤ P) :
    let Q := quotientPrimeOfLe hIP
    let Rₚ := Localization.AtPrime P
    let J := I.map (algebraMap R Rₚ)
    letI : Algebra (R ⧸ I) (Rₚ ⧸ J) :=
      Ideal.Quotient.algebraQuotientOfLEComap (R := R) (A := Rₚ)
        (p := I) (P := J)
        (by
          intro x hx
          exact Ideal.mem_comap.mpr
            (Ideal.mem_map_of_mem (algebraMap R Rₚ) hx))
    Localization.AtPrime Q.asIdeal ≃ₐ[R ⧸ I] (Rₚ ⧸ J) := by
  dsimp only
  let Q := quotientPrimeOfLe hIP
  let Rₚ := Localization.AtPrime P
  let J := I.map (algebraMap R Rₚ)
  letI : Algebra (R ⧸ I) (Rₚ ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap (R := R) (A := Rₚ)
      (p := I) (P := J)
      (by
        intro x hx
        exact Ideal.mem_comap.mpr
          (Ideal.mem_map_of_mem (algebraMap R Rₚ) hx))
  have hloc :
      IsLocalization (P.primeCompl.map (Ideal.Quotient.mk I)) (Rₚ ⧸ J) := by
    refine IsLocalization.of_surjective
      (M := P.primeCompl) (S := Rₚ)
      (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (g := Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective ?_ ?_
    · ext x
      rfl
    · simp [J, Ideal.mk_ker]
  haveI : IsLocalization Q.asIdeal.primeCompl (Rₚ ⧸ J) := by
    simpa [Q, primeCompl_map_quotient_eq hIP] using hloc
  exact IsLocalization.algEquiv Q.asIdeal.primeCompl
    (Localization.AtPrime Q.asIdeal) (Rₚ ⧸ J)

/-- A member of a regular system whose quotient is regular on the spectrum
has nonzero cotangent class at every height-two prime containing it. -/
theorem regularParameter_not_mem_localized_maximalIdeal_sq
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A] {d : ℕ} (t : Fin d → A)
    (hreg : IsRegular A (List.ofFn t))
    (hgen : Ideal.ofList (List.ofFn t) = maximalIdeal A)
    (i : Fin d) (hBranch : IsRegularRing (A ⧸ Ideal.span {t i}))
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2) (htiP : t i ∈ P) :
    algebraMap A (Localization.AtPrime P) (t i) ∉
      maximalIdeal (Localization.AtPrime P) ^ 2 := by
  let R := Localization.AtPrime P
  let x : R := algebraMap A R (t i)
  let I : Ideal R := Ideal.span {x}
  let B := A ⧸ Ideal.span {t i}
  let Q := quotientPrimeOfLe (P.span_singleton_le_iff_mem.mpr htiP)
  let S := R ⧸ I
  let : IsRegularRing B := hBranch
  have hxPrime : Prime (t i) :=
    Kummer.prime_of_mem_regularSystem hreg hgen
      (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hxMem : x ∈ maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R P (t i)).mpr htiP
  have hxNe : x ≠ 0 := by
    intro hx
    exact hxPrime.ne_zero
      ((IsLocalization.injective R P.primeCompl_le_nonZeroDivisors)
        (by simpa only [map_zero] using hx))
  have hI : (Ideal.span {t i}).map (algebraMap A R) = I := by
    simp [I, x, Ideal.map_span]
  let e₀ := quotientLocalizationEquiv
    (R := A) (I := Ideal.span {t i}) (P := P)
    (P.span_singleton_le_iff_mem.mpr htiP)
  let e : Localization.AtPrime Q.asIdeal ≃+* S :=
    e₀.toRingEquiv.trans
      (Ideal.quotientEquivAlgOfEq R hI).toRingEquiv
  have hregularS : IsRegularLocalRing S :=
    IsRegularLocalRing.of_ringEquiv e
  let : IsRegularLocalRing S := hregularS
  have hdimR : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim R = (P.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height P R
      _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hP
  have hxRegular : IsSMulRegular R x := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro a ha
    have hxa : x * a = 0 := by
      simpa only [smul_eq_mul] using ha
    exact (mul_eq_zero.mp hxa).resolve_left hxNe
  have hdimSsucc : ringKrullDim S + 1 = ringKrullDim R := by
    simpa only [S, I] using
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hxRegular hxMem
  have hdimS : ringKrullDim S = ((1 : ℕ∞) : WithBot ℕ∞) := by
    rw [hdimR] at hdimSsucc
    have htwo : ((2 : ℕ∞) : WithBot ℕ∞) =
        ((1 : ℕ∞) : WithBot ℕ∞) + 1 := by norm_num
    exact ENat.WithBot.add_one_cancel.mp (hdimSsucc.trans htwo)
  have hspanRankS : (maximalIdeal S).spanFinrank = 1 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)
    rw [hdimS] at h
    exact ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp h)
  have hprincipalS : (maximalIdeal S).IsPrincipal :=
    (Submodule.spanFinrank_eq_one_iff (maximalIdeal S)).mp hspanRankS |>.1
  obtain ⟨z, hz⟩ := hprincipalS
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective z
  have hz' : maximalIdeal S = Ideal.span {Ideal.Quotient.mk I y} := by
    simpa only [hy] using hz
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hspanR : Ideal.span {x, y} = maximalIdeal R := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha | ha
      · rw [ha]
        change x ∈ maximalIdeal R
        exact hxMem
      · have hyS : Ideal.Quotient.mk I y ∈ maximalIdeal S := by
          rw [hz']
          exact Ideal.mem_span_singleton_self _
        have hyR : y ∈ maximalIdeal R := by
          rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk I)]
          exact hyS
        rw [ha]
        change y ∈ maximalIdeal R
        exact hyR
    · intro a ha
      have haS : Ideal.Quotient.mk I a ∈ maximalIdeal S := by
        exact (IsLocalRing.map_maximalIdeal_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective) ▸
            Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha
      rw [hz', Ideal.mem_span_singleton] at haS
      obtain ⟨cS, hcS⟩ := haS
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective cS
      have hac : a - c * y ∈ I := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simp only [map_sub, map_mul, hc, mul_comm, hcS, sub_self]
      have hIle : I ≤ Ideal.span {x, y} := by
        change Ideal.span {x} ≤ Ideal.span {x, y}
        exact Ideal.span_mono (by simp)
      have hcy : c * y ∈ Ideal.span {x, y} :=
        (Ideal.span {x, y}).mul_mem_left c
          (Ideal.subset_span (by simp))
      have := (Ideal.span {x, y}).add_mem (hIle hac) hcy
      simpa only [sub_add_cancel] using this
  intro hxSq
  let m : Ideal R := maximalIdeal R
  have hyMem : y ∈ m := by
    change y ∈ maximalIdeal R
    rw [← hspanR]
    exact Ideal.subset_span (by simp)
  let x' : m := ⟨x, by simpa only [m] using hxMem⟩
  let y' : m := ⟨y, hyMem⟩
  have hxCot : m.toCotangent x' = 0 := by
    apply (m.toCotangent_eq_zero x').mpr
    simpa only [m, x'] using hxSq
  have hmapSpan :
      (Submodule.span R ({x', y'} : Set m)).map m.subtype = m := by
    rw [Submodule.map_span]
    change Ideal.span (m.subtype '' ({x', y'} : Set m)) = m
    rw [show m.subtype '' ({x', y'} : Set m) = ({x, y} : Set R) by
      ext z
      simp [x', y', eq_comm]]
    simpa only [m] using hspanR
  have hsubtypeSpan : Submodule.span R ({x', y'} : Set m) = ⊤ := by
    apply (Submodule.map_injective_of_injective m.subtype_injective)
    rw [hmapSpan, Submodule.map_top, Submodule.range_subtype]
  have hspanCot :
      Submodule.span (ResidueField R)
          (m.toCotangent '' ({x', y'} : Set m)) = ⊤ :=
    (CotangentSpace.span_image_eq_top_iff (R := R)).mpr hsubtypeSpan
  have hspanCot' :
      Submodule.span (ResidueField R)
          ({m.toCotangent y'} : Set (CotangentSpace R)) = ⊤ := by
    simpa only [Set.image_pair, hxCot,
      Submodule.span_insert_zero] using hspanCot
  have hfinle : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
    rw [← finrank_top (ResidueField R) (CotangentSpace R), ← hspanCot']
    simpa using (finrank_span_le_card
      (R := ResidueField R)
      ({m.toCotangent y'} : Set (CotangentSpace R)))
  have hfinR : Module.finrank (ResidueField R) (CotangentSpace R) = 2 := by
    have hregR :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    rw [hdimR] at hregR
    exact ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp hregR)
  omega

/-- At a height-two point of a strict normal crossings chart, a selected
branch equation extends to a regular pair generating the localized maximal
ideal. -/
theorem exists_regular_pair_localizationAtPrime_of_splitStrictNormalCrossings
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A] {d r : ℕ} {f : A} {t : Fin d → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin d) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2) (htiP : t i ∈ P) :
    ∃ y : Localization.AtPrime P,
      IsRegular (Localization.AtPrime P)
        [algebraMap A (Localization.AtPrime P) (t i), y] ∧
      Ideal.ofList [algebraMap A (Localization.AtPrime P) (t i), y] =
        maximalIdeal (Localization.AtPrime P) := by
  have htSq := regularParameter_not_mem_localized_maximalIdeal_sq
    t hNC.2.2.1.1 hNC.2.2.1.2 i (hNC.2.2.2.2.2 i hi) P hP htiP
  exact exists_regular_pair_localizationAtPrime_of_height_eq_two
    P hP (hNC.2.2.2.1 i hi) htiP htSq

end EtaleFundamentalGroups

end
