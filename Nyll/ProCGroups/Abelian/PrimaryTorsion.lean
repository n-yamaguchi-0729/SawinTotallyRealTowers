/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.PrimaryDetection

/-! # Prime torsion is detected by the corresponding primary quotient -/

namespace ProCGroups.ProC

universe u

/-- Elements killed by a prime inject into the maximal pro-prime quotient. -/
theorem eq_one_of_prime_torsion_of_primaryQuotient_eq_one
    {p : ℕ} [Fact p.Prime]
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    (a : A) (ha : a ^ p = 1)
    (hπ : QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p) A) a = 1) :
    a = 1 := by
  have hroots (s : ℕ) : ∃ b : A, b ^ (p ^ s) = a := by
    let P : Subgroup A := (powMonoidHom (α := A) (p ^ s)).range
    let powerMap : A →ₜ* A := ⟨powMonoidHom (p ^ s), continuous_id.pow _⟩
    have hP : IsClosed (P : Set A) := ContinuousMonoidHom.isClosed_range powerMap
    have : IsClosed (P : Set A) := hP
    have : TotallyDisconnectedSpace (A ⧸ P) :=
      ProCGroups.totallyDisconnectedSpace_quotient_closedNormal P hP
    have hQ : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) (A ⧸ P) := by
      apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
      intro U
      refine ⟨inferInstance, ?_⟩
      apply isPGroup_iff_pow_pow_eq_one.mpr
      intro q
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup (A ⧸ P)) q
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective P b
      refine ⟨s, ?_⟩
      rw [← map_pow, ← map_pow]
      have hb : QuotientGroup.mk' P (b ^ (p ^ s)) = 1 :=
        (QuotientGroup.eq_one_iff (N := P) _).mpr ⟨b, rfl⟩
      rw [hb, map_one]
    have hle : proCResidualCore (FiniteGroupClass.pGroup p) A ≤ P :=
      proCResidualCore_le_of_proCQuotient P hP hQ
    exact hle ((QuotientGroup.eq_one_iff (N :=
      proCResidualCore (FiniteGroupClass.pGroup p) A) a).mp hπ)
  apply ProCGroups.ProfiniteGrp.eq_one_of_mem_all_openNormalSubgroups
  intro U
  apply (QuotientGroup.eq_one_iff (N := (U : Subgroup A)) a).mp
  let Q := A ⧸ (U : Subgroup A)
  let x : Q := QuotientGroup.mk' (U : Subgroup A) a
  have hcard : Nat.card Q ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨b, hb⟩ := hroots ((Nat.card Q).factorization p)
  have hpow : x ^ (Nat.card Q / p ^ (Nat.card Q).factorization p) = 1 := by
    change (QuotientGroup.mk' (U : Subgroup A) a) ^ _ = 1
    rw [← hb, map_pow, ← pow_mul, Nat.ordProj_mul_ordCompl_eq_self]
    exact pow_card_eq_one'
  have hp : x ^ p = 1 := by
    change (QuotientGroup.mk' (U : Subgroup A) a) ^ p = 1
    rw [← map_pow, ha, map_one]
  have hcop : p.Coprime (Nat.card Q / p ^ (Nat.card Q).factorization p) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (Nat.not_dvd_ordCompl (Fact.out : p.Prime) hcard)
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  rw [← hcop.gcd_eq_one]
  exact Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hp)
    (orderOf_dvd_iff_pow_eq_one.mpr hpow)

end ProCGroups.ProC
