/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Domains and prime parameters from a regular system

This file supplies the algebraic fact needed by finite local root covers:
a Noetherian local ring admitting a regular sequence which generates its
maximal ideal is a domain, and every member of that regular system is prime.
No domain or primality conclusion is assumed.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped Pointwise
open IsLocalRing
open RingTheory.Sequence

universe u

/-- In a Noetherian local ring, one prime regular element forces the zero
ideal to be prime.  Krull intersection rules out infinite divisibility by the
chosen element. -/
theorem isDomain_of_prime_isSMulRegular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {p : R} (hp : Prime p) (hpreg : IsSMulRegular R p) : IsDomain R := by
  have hbot : (⊥ : Ideal R).IsPrime := by
    rw [Ideal.isPrime_iff]
    refine ⟨bot_ne_top, ?_⟩
    intro a b hab
    simp only [Ideal.mem_bot] at hab ⊢
    by_contra hzero
    push Not at hzero
    obtain ⟨k, hak⟩ : ∃ k : ℕ, a ∉ maximalIdeal R ^ k := by
      by_contra hall
      push Not at hall
      have haInf : a ∈ ⨅ k : ℕ, maximalIdeal R ^ k := Ideal.mem_iInf.mpr hall
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing
        (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top] at haInf
      exact hzero.1 (Ideal.mem_bot.mp haInf)
    obtain ⟨l, hbl⟩ : ∃ l : ℕ, b ∉ maximalIdeal R ^ l := by
      by_contra hall
      push Not at hall
      have hbInf : b ∈ ⨅ l : ℕ, maximalIdeal R ^ l := Ideal.mem_iInf.mpr hall
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing
        (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top] at hbInf
      exact hzero.2 (Ideal.mem_bot.mp hbInf)
    have hpMem : p ∈ maximalIdeal R := by
      rw [mem_maximalIdeal]
      exact hp.not_isUnit
    have hpow : ∀ k l : ℕ, ∀ a b : R, a * b = 0 →
        p ^ k ∣ a ∨ p ^ l ∣ b := by
      intro k
      induction k with
      | zero =>
          intro l a b hab
          exact Or.inl (by simp)
      | succ k ihK =>
          intro l
          induction l with
          | zero =>
              intro a b hab
              exact Or.inr (by simp)
          | succ l ihL =>
              intro a b hab
              have hpProd : p ∣ a * b := by rw [hab]; exact dvd_zero p
              rcases hp.dvd_mul.mp hpProd with hpa | hpb
              · obtain ⟨a', rfl⟩ := hpa
                have hab' : a' * b = 0 := by
                  apply hpreg.right_eq_zero_of_smul
                  simpa only [smul_eq_mul, mul_assoc] using hab
                rcases ihK (l + 1) a' b hab' with ha' | hb'
                · left
                  obtain ⟨c, hc⟩ := ha'
                  refine ⟨c, ?_⟩
                  rw [hc, pow_succ]
                  ac_rfl
                · exact Or.inr hb'
              · obtain ⟨b', rfl⟩ := hpb
                have hab' : a * b' = 0 := by
                  apply hpreg.right_eq_zero_of_smul
                  simpa only [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hab
                rcases ihL a b' hab' with ha' | hb'
                · exact Or.inl ha'
                · right
                  obtain ⟨c, hc⟩ := hb'
                  refine ⟨c, ?_⟩
                  rw [hc, pow_succ]
                  ac_rfl
    rcases hpow k l a b hab with ha | hb
    · apply hak
      obtain ⟨c, rfl⟩ := ha
      exact (maximalIdeal R ^ k).mul_mem_right c
        (Ideal.pow_mem_pow hpMem k)
    · apply hbl
      obtain ⟨c, rfl⟩ := hb
      exact (maximalIdeal R ^ l).mul_mem_right c
        (Ideal.pow_mem_pow hpMem l)
  let : (⊥ : Ideal R).IsPrime := hbot
  exact IsDomain.of_bot_isPrime R

/-- Removing the first member of a regular system leaves a regular system in
the quotient, still generating its maximal ideal. -/
theorem regularSystem_quotientHead
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {p : R} {ps : List R}
    (hreg : IsRegular R (p :: ps))
    (hgen : Ideal.ofList (p :: ps) = maximalIdeal R) :
    let I : Ideal R := Ideal.span {p}
    let S := R ⧸ I
    IsRegular S (ps.map (Ideal.Quotient.mk I)) ∧
      Ideal.ofList (ps.map (Ideal.Quotient.mk I)) =
        (maximalIdeal R).map (Ideal.Quotient.mk I) := by
  dsimp only
  let I : Ideal R := Ideal.span {p}
  let S := R ⧸ I
  have hpMem : p ∈ maximalIdeal R := by
    rw [← hgen]
    exact Ideal.subset_span (by simp)
  have hIle : I ≤ maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    change p ∈ maximalIdeal R
    exact hpMem
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hregQ : IsRegular (QuotSMulTop p R)
      (ps.map (Ideal.Quotient.mk I)) :=
    ((isRegular_cons_iff' R p ps).mp hreg).2
  let e : QuotSMulTop p R ≃ₗ[S] S :=
    ((QuotSMulTop.equivQuotTensor p R).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective).trans
        ((TensorProduct.rid R S).extendScalarsOfSurjective
          Ideal.Quotient.mk_surjective)
  have hregS : IsRegular S (ps.map (Ideal.Quotient.mk I)) :=
    (e.isRegular_congr _).mp hregQ
  have hgenS : Ideal.ofList (ps.map (Ideal.Quotient.mk I)) =
      (maximalIdeal R).map (Ideal.Quotient.mk I) := by
    rw [← hgen, Ideal.map_ofList]
    simp [I]
  exact ⟨hregS, hgenS⟩

/-- Quotienting by an initial segment of a regular system leaves the mapped
tail as a regular system generating the quotient maximal ideal.

Unlike iterating `regularSystem_quotientHead`, this theorem presents the
result directly over the single quotient by `Ideal.ofList xs`. -/
theorem regularSystem_quotientPrefix
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (xs ys : List R)
    (hreg : IsRegular R (xs ++ ys))
    (hgen : Ideal.ofList (xs ++ ys) = maximalIdeal R) :
    let I : Ideal R := Ideal.ofList xs
    let hI : I ≤ maximalIdeal R := by
      calc
        I ≤ Ideal.ofList (xs ++ ys) := by
          rw [Ideal.ofList_append]
          exact le_sup_left
        _ = maximalIdeal R := hgen
    let S := R ⧸ I
    letI : Nontrivial S :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
    letI : IsLocalRing S :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    IsRegular S (ys.map (Ideal.Quotient.mk I)) ∧
      Ideal.ofList (ys.map (Ideal.Quotient.mk I)) = maximalIdeal S := by
  dsimp only
  let I : Ideal R := Ideal.ofList xs
  have hI : I ≤ maximalIdeal R := by
    calc
      I ≤ Ideal.ofList (xs ++ ys) := by
        rw [Ideal.ofList_append]
        exact le_sup_left
      _ = maximalIdeal R := hgen
  let S := R ⧸ I
  let q : R →+* S := Ideal.Quotient.mk I
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S q Ideal.Quotient.mk_surjective
  have hweakQuotient :=
    ((isWeaklyRegular_append_iff' R xs ys).mp
      hreg.toIsWeaklyRegular).2
  have hsmulTop :
      Ideal.ofList xs • (⊤ : Ideal R) = I := by
    simp [I]
  let eAdd :
      (R ⧸ (Ideal.ofList xs • (⊤ : Ideal R))) ≃+ S :=
    (Submodule.quotEquivOfEq
      (Ideal.ofList xs • (⊤ : Ideal R)) I hsmulTop).toAddEquiv
  let e :
      (R ⧸ (Ideal.ofList xs • (⊤ : Ideal R))) ≃ₗ[S] S :=
    AddEquiv.toLinearEquiv (R := S) eAdd (by
      intro s z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
      obtain ⟨a, rfl⟩ :=
        Submodule.mkQ_surjective
          (Ideal.ofList xs • (⊤ : Ideal R)) z
      rfl)
  have hweakS : IsWeaklyRegular S (ys.map q) := by
    exact (e.isWeaklyRegular_congr _).mp hweakQuotient
  have hgenMap :
      Ideal.ofList ((xs ++ ys).map q) =
        (maximalIdeal R).map q := by
    rw [← Ideal.map_ofList, hgen]
  have hmapXs : Ideal.ofList (xs.map q) = ⊥ := by
    rw [← Ideal.map_ofList]
    exact Ideal.map_quotient_self I
  have hgenS : Ideal.ofList (ys.map q) = maximalIdeal S := by
    calc
      Ideal.ofList (ys.map q) =
          Ideal.ofList (xs.map q) ⊔ Ideal.ofList (ys.map q) := by
        rw [hmapXs, bot_sup_eq]
      _ = Ideal.ofList ((xs ++ ys).map q) := by
        rw [List.map_append, Ideal.ofList_append]
      _ = (maximalIdeal R).map q := hgenMap
      _ = maximalIdeal S :=
        IsLocalRing.map_maximalIdeal_of_surjective
          q Ideal.Quotient.mk_surjective
  have hmem : ∀ r ∈ ys.map q, r ∈ maximalIdeal S := by
    intro r hr
    rw [← hgenS]
    exact Ideal.subset_span hr
  exact ⟨IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
      (L := S) hmem hweakS, hgenS⟩

/-- A regular system generating the maximal ideal makes a Noetherian local
ring a domain. -/
theorem isDomain_of_regularSystem
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ps : List R) (hreg : IsRegular R ps)
    (hgen : Ideal.ofList ps = maximalIdeal R) : IsDomain R := by
  match ps with
  | [] =>
      have hmax : maximalIdeal R = ⊥ := by simpa using hgen.symm
      exact (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax).isDomain
  | p :: ps =>
      let I : Ideal R := Ideal.span {p}
      let S := R ⧸ I
      have hpMem : p ∈ maximalIdeal R := by
        rw [← hgen]
        exact Ideal.subset_span (by simp)
      have hIle : I ≤ maximalIdeal R := by
        apply Ideal.span_le.mpr
        intro z hz
        simp only [Set.mem_singleton_iff] at hz
        subst z
        change p ∈ maximalIdeal R
        exact hpMem
      have hIne : I ≠ ⊤ :=
        ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle
      let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
      let : IsLocalRing S :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
          Ideal.Quotient.mk_surjective
      let : IsNoetherianRing S :=
        isNoetherianRing_of_surjective R S (Ideal.Quotient.mk I)
          Ideal.Quotient.mk_surjective
      have hquot := regularSystem_quotientHead hreg hgen
      have hregS : IsRegular S (ps.map (Ideal.Quotient.mk I)) := by
        simpa [I, S] using hquot.1
      have hgenS : Ideal.ofList (ps.map (Ideal.Quotient.mk I)) =
          maximalIdeal S := by
        calc
          Ideal.ofList (ps.map (Ideal.Quotient.mk I)) =
              (maximalIdeal R).map (Ideal.Quotient.mk I) := by
            simpa [I, S] using hquot.2
          _ = maximalIdeal S :=
            IsLocalRing.map_maximalIdeal_of_surjective
              (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      have hdomainS : IsDomain S :=
        isDomain_of_regularSystem (R := S)
          (ps.map (Ideal.Quotient.mk I)) hregS hgenS
      let : IsDomain S := hdomainS
      have hIprime : I.IsPrime :=
        (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
      have hpreg : IsSMulRegular R p :=
        ((isRegular_cons_iff R p ps).mp hreg).1
      have hpNe : p ≠ 0 := by
        intro hpzero
        have hone : (1 : R) = 0 := by
          apply hpreg.right_eq_zero_of_smul
          simp only [hpzero, zero_smul]
        exact one_ne_zero hone
      have hpPrime : Prime p := by
        apply (Ideal.span_singleton_prime hpNe).mp
        simpa [I] using hIprime
      exact isDomain_of_prime_isSMulRegular hpPrime hpreg
termination_by ps.length

/-- A regular system which generates the maximal ideal makes its Noetherian
local ring regular local. -/
theorem isRegularLocalRing_of_regularSystem
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ps : List R) (hreg : IsRegular R ps)
    (hgen : Ideal.ofList ps = maximalIdeal R) : IsRegularLocalRing R := by
  classical
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hspan : (Ideal.ofList ps).spanFinrank ≤ ps.length := by
    refine (Submodule.spanFinrank_span_le_ncard_of_finite ps.finite_toSet).trans ?_
    rw [show {x : R | x ∈ ps} = (ps.toFinset : Set R) by ext; simp,
      Set.ncard_coe_finset]
    exact List.toFinset_card_le ps
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ps hreg
  rw [hgen] at hdim
  let : Field (R ⧸ maximalIdeal R) :=
    Ideal.Quotient.field (maximalIdeal R)
  have hfieldDim : ringKrullDim (R ⧸ maximalIdeal R) = 0 :=
    ringKrullDim_eq_zero_of_field _
  rw [hfieldDim, zero_add] at hdim
  rw [← hgen]
  change ((Ideal.ofList ps).spanFinrank : WithBot ℕ∞) ≤ ringKrullDim R
  calc
    ((Ideal.ofList ps).spanFinrank : WithBot ℕ∞) ≤
        (ps.length : WithBot ℕ∞) := by exact_mod_cast hspan
    _ = ringKrullDim R := by simpa using hdim

/-- The length of a regular system generating the maximal ideal is the
Krull dimension of the local ring. -/
theorem regularSystem_length_eq_ringKrullDim
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ps : List R) (hreg : IsRegular R ps)
    (hgen : Ideal.ofList ps = maximalIdeal R) :
    ((ps.length : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := by
  have hdim :=
    ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ps hreg
  rw [hgen] at hdim
  let : Field (R ⧸ maximalIdeal R) :=
    Ideal.Quotient.field (maximalIdeal R)
  have hfieldDim : ringKrullDim (R ⧸ maximalIdeal R) = 0 :=
    ringKrullDim_eq_zero_of_field _
  rw [hfieldDim, zero_add] at hdim
  simpa using hdim

/-- A single quotient by an initial segment of a regular system is again a
regular local domain.  No normality of any intermediate quotient is used. -/
theorem quotientPrefix_geometry_of_regularSystem
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (xs ys : List R)
    (hreg : IsRegular R (xs ++ ys))
    (hgen : Ideal.ofList (xs ++ ys) = maximalIdeal R) :
    IsDomain (R ⧸ Ideal.ofList xs) ∧
      IsRegularLocalRing (R ⧸ Ideal.ofList xs) := by
  let I : Ideal R := Ideal.ofList xs
  let S := R ⧸ I
  have hI : I ≤ maximalIdeal R := by
    calc
      I ≤ Ideal.ofList (xs ++ ys) := by
        rw [Ideal.ofList_append]
        exact le_sup_left
      _ = maximalIdeal R := hgen
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hquot := regularSystem_quotientPrefix xs ys hreg hgen
  have hregS : IsRegular S (ys.map (Ideal.Quotient.mk I)) := by
    simpa only [I, S] using hquot.1
  have hgenS : Ideal.ofList (ys.map (Ideal.Quotient.mk I)) =
      maximalIdeal S := by
    simpa only [I, S] using hquot.2
  exact ⟨isDomain_of_regularSystem _ hregS hgenS,
    isRegularLocalRing_of_regularSystem _ hregS hgenS⟩

/-- The Krull dimension of the direct prefix quotient is the length of the
remaining regular system. -/
theorem quotientPrefix_ringKrullDim_eq_length_of_regularSystem
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (xs ys : List R)
    (hreg : IsRegular R (xs ++ ys))
    (hgen : Ideal.ofList (xs ++ ys) = maximalIdeal R) :
    ringKrullDim (R ⧸ Ideal.ofList xs) =
      ((ys.length : ℕ∞) : WithBot ℕ∞) := by
  let I : Ideal R := Ideal.ofList xs
  let S := R ⧸ I
  have hI : I ≤ maximalIdeal R := by
    calc
      I ≤ Ideal.ofList (xs ++ ys) := by
        rw [Ideal.ofList_append]
        exact le_sup_left
      _ = maximalIdeal R := hgen
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hquot := regularSystem_quotientPrefix xs ys hreg hgen
  have hdim := regularSystem_length_eq_ringKrullDim
    (R := S) (ys.map (Ideal.Quotient.mk I))
      (by simpa only [I, S] using hquot.1)
      (by simpa only [I, S] using hquot.2)
  simpa only [I, S, List.length_map] using hdim.symm

/-- If precisely two parameters remain, the direct prefix quotient supplies
the regular local domain of dimension two needed by punctured purity. -/
theorem quotientPrefix_geometry_dimension_two_of_regularSystem
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (xs : List R) (y z : R)
    (hreg : IsRegular R (xs ++ [y, z]))
    (hgen : Ideal.ofList (xs ++ [y, z]) = maximalIdeal R) :
    IsDomain (R ⧸ Ideal.ofList xs) ∧
      IsRegularLocalRing (R ⧸ Ideal.ofList xs) ∧
      ringKrullDim (R ⧸ Ideal.ofList xs) =
        ((2 : ℕ∞) : WithBot ℕ∞) := by
  refine ⟨(quotientPrefix_geometry_of_regularSystem
    xs [y, z] hreg hgen).1, ?_⟩
  refine ⟨(quotientPrefix_geometry_of_regularSystem
    xs [y, z] hreg hgen).2, ?_⟩
  simpa using
    (quotientPrefix_ringKrullDim_eq_length_of_regularSystem
      xs [y, z] hreg hgen)

/-- Every member of a regular system generating the maximal ideal is prime. -/
theorem prime_of_mem_regularSystem
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {ps : List R} (hreg : IsRegular R ps)
    (hgen : Ideal.ofList ps = maximalIdeal R)
    {p : R} (hp : p ∈ ps) : Prime p := by
  classical
  let qs := ps.erase p
  have hperm : ps.Perm (p :: qs) := List.perm_cons_erase hp
  have hreg' : IsRegular R (p :: qs) :=
    IsLocalRing.isRegular_of_perm hreg hperm
  have hgen' : Ideal.ofList (p :: qs) = maximalIdeal R := by
    rw [← hgen]
    apply congrArg Ideal.span
    ext z
    exact hperm.mem_iff.symm
  let I : Ideal R := Ideal.span {p}
  let S := R ⧸ I
  have hpMem : p ∈ maximalIdeal R := by
    rw [← hgen']
    exact Ideal.subset_span (by simp)
  have hIle : I ≤ maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    change p ∈ maximalIdeal R
    exact hpMem
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hquot := regularSystem_quotientHead hreg' hgen'
  have hdomainS : IsDomain S :=
    isDomain_of_regularSystem (qs.map (Ideal.Quotient.mk I))
      (by simpa [I, S] using hquot.1)
      (by
        calc
          Ideal.ofList (qs.map (Ideal.Quotient.mk I)) =
              (maximalIdeal R).map (Ideal.Quotient.mk I) := by
            simpa [I, S] using hquot.2
          _ = maximalIdeal S :=
            IsLocalRing.map_maximalIdeal_of_surjective
              (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)
  let : IsDomain S := hdomainS
  have hIprime : I.IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  have hpreg : IsSMulRegular R p :=
    ((isRegular_cons_iff R p qs).mp hreg').1
  have hpNe : p ≠ 0 := by
    intro hpzero
    have hone : (1 : R) = 0 := by
      apply hpreg.right_eq_zero_of_smul
      simp only [hpzero, zero_smul]
    exact one_ne_zero hone
  apply (Ideal.span_singleton_prime hpNe).mp
  simpa [I] using hIprime

/-- Quotienting by any member of a regular system again gives a regular local
domain.  This packages the divisor geometry needed after a root construction. -/
theorem quotient_geometry_of_mem_regularSystem
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {ps : List R} (hreg : IsRegular R ps)
    (hgen : Ideal.ofList ps = maximalIdeal R)
    {p : R} (hp : p ∈ ps) :
    IsDomain (R ⧸ Ideal.span {p}) ∧
      IsRegularLocalRing (R ⧸ Ideal.span {p}) := by
  classical
  let qs := ps.erase p
  have hperm : ps.Perm (p :: qs) := List.perm_cons_erase hp
  have hreg' : IsRegular R (p :: qs) :=
    IsLocalRing.isRegular_of_perm hreg hperm
  have hgen' : Ideal.ofList (p :: qs) = maximalIdeal R := by
    rw [← hgen]
    apply congrArg Ideal.span
    ext z
    exact hperm.mem_iff.symm
  let I : Ideal R := Ideal.span {p}
  let S := R ⧸ I
  have hpMem : p ∈ maximalIdeal R := by
    rw [← hgen']
    exact Ideal.subset_span (by simp)
  have hIle : I ≤ maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact hpMem
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hquot := regularSystem_quotientHead hreg' hgen'
  have hregS : IsRegular S (qs.map (Ideal.Quotient.mk I)) := by
    simpa [I, S] using hquot.1
  have hgenS : Ideal.ofList (qs.map (Ideal.Quotient.mk I)) =
      maximalIdeal S := by
    calc
      Ideal.ofList (qs.map (Ideal.Quotient.mk I)) =
          (maximalIdeal R).map (Ideal.Quotient.mk I) := by
        simpa [I, S] using hquot.2
      _ = maximalIdeal S :=
        IsLocalRing.map_maximalIdeal_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact ⟨isDomain_of_regularSystem _ hregS hgenS,
    isRegularLocalRing_of_regularSystem _ hregS hgenS⟩

end EtaleFundamentalGroups.Kummer

end
