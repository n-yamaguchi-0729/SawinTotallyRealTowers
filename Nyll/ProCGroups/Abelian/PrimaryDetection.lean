/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Nyll.ProCGroups.FiniteGroups.SigmaPowerDetection
import Nyll.ProCGroups.Profinite.Basic
import Nyll.ProCGroups.Topologies.ContinuousMonoidHom

/-!
# Primary quotients separate profinite abelian groups
-/

namespace ProCGroups.ProC
universe u

theorem eq_one_of_forall_primaryQuotient
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    (a : A)
    (ha : ∀ (p : ℕ) [Fact p.Prime],
      QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p) A) a = 1) :
    a = 1 := by
  have hroots (p : ℕ) (hp : p.Prime) (s : ℕ) : ∃ b : A, b ^ (p ^ s) = a := by
    have : Fact p.Prime := ⟨hp⟩
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
      proCResidualCore (FiniteGroupClass.pGroup p) A) a).mp (ha p))
  apply ProCGroups.ProfiniteGrp.eq_one_of_mem_all_openNormalSubgroups
  intro U
  apply (QuotientGroup.eq_one_iff (N := (U : Subgroup A)) a).mp
  apply FiniteGroupClass.eq_one_of_primePower_roots (sigma := Set.univ)
    ⟨inferInstance, fun p _ hp => False.elim (hp (Set.mem_univ p))⟩
  intro p _ hp s _
  obtain ⟨b, hb⟩ := hroots p hp s
  exact ⟨QuotientGroup.mk' (U : Subgroup A) b, by rw [← map_pow, hb]; rfl⟩

end ProCGroups.ProC
