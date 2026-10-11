/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteGroups.SigmaPowerDetection
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality

/-!
# Detecting residual abelianization by prime powers

The abelianized maximal pro-Sigma quotient identifies two classes exactly
when they agree modulo every allowed prime power. The proof constructs the
factorizations through the actual power quotients and uses finite quotient
separation. It applies in particular to the conjugation action.
-/

namespace ProCGroups.ProC

universe u

/-- An element admitting all allowed prime-power roots is trivial in a Hausdorff pro-Sigma group. -/
theorem HasOpenNormalBasisInClass.eq_one_of_primePower_roots
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [T2Space G]
    (hG : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) G)
    (x : G)
    (hx : ∀ ℓ : ℕ, ℓ ∈ sigma → ℓ.Prime →
      ∀ s : ℕ, 0 < s → ∃ y : G, y ^ (ℓ ^ s) = x) : x = 1 := by
  apply hG.eq_of_forall_openNormalSubgroupInClass_quotient_eq
  intro U
  rw [map_one]
  have : Finite (G ⧸ (U.1 : Subgroup G)) := U.2.1
  apply FiniteGroupClass.eq_one_of_primePower_roots U.2
  intro ℓ hℓsigma hℓ s hs
  obtain ⟨y, hy⟩ := hx ℓ hℓsigma hℓ s hs
  exact ⟨QuotientGroup.mk' (U.1 : Subgroup G) y, by
    rw [← map_pow, hy]⟩


/-- A profinite group of prime-power exponent is pro-Sigma when the prime belongs to Sigma. -/
theorem hasOpenNormalBasisInClass_sigma_of_primePower_exponent
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓsigma : ℓ ∈ sigma) (s : ℕ)
    (hpow : ∀ x : G, x ^ (ℓ ^ s) = 1) :
    HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) G := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  have hP : IsPGroup ℓ (G ⧸ (U : Subgroup G)) := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup G) q
    exact ⟨s, by rw [← map_pow, hpow, map_one]⟩
  obtain ⟨k, hk⟩ := hP.exists_card_dvd_pow
  exact ⟨inferInstance,
    (FiniteGroupClass.IsSigmaNumber.prime_pow_of_mem hℓsigma hℓ).of_dvd hk⟩


open ProCGroups.Abelian

/-- The abelianization of a pro-Sigma group still has a pro-Sigma basis. -/
theorem residualAbelianization_hasOpenNormalBasisInClass
    {sigma : Set ℕ} (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma)
      (TopologicalAbelianization (G ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G)) := by
  let R := proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G
  have : IsClosed (R : Set G) := proCResidualCore_isClosed _ _
  have : TotallyDisconnectedSpace (G ⧸ R) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal R
      (proCResidualCore_isClosed _ _)
  have hQ : HasOpenNormalBasisInClass (FiniteGroupClass.sigmaGroup sigma) (G ⧸ R) :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass
      (FiniteGroupClass.sigmaGroup_formation sigma)
  exact quotient_closedNormalSubgroup
    (FiniteGroupClass.sigmaGroup sigma).isomClosed
    (FiniteGroupClass.sigmaGroup_quotientClosed sigma) hQ
    (Subgroup.closedCommutator (G ⧸ R)) (Subgroup.isClosed_closedCommutator _)

/-- Equality in the abelianized maximal pro-Sigma quotient is detected modulo prime powers. -/
theorem residualAbelianization_map_eq_iff_primePower
    {sigma : Set ℕ} (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (x y : TopologicalAbelianization G) :
    let π : G →ₜ* (G ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G) :=
      ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
    TopologicalAbelianization.map π x = TopologicalAbelianization.map π y ↔
      ∀ ℓ : ℕ, ℓ ∈ sigma → ℓ.Prime → ∀ s : ℕ, 0 < s →
        ∃ b : TopologicalAbelianization G, x = y * b ^ (ℓ ^ s) := by
  let R := proCResidualCore (FiniteGroupClass.sigmaGroup sigma) G
  let Q := G ⧸ R
  let π : G →ₜ* Q := ⟨QuotientGroup.mk' R, QuotientGroup.continuous_mk⟩
  let f := TopologicalAbelianization.map π
  change f x = f y ↔ _
  constructor
  · intro hxy ℓ hℓsigma hℓ s _
    let A := TopologicalAbelianization G
    let P : Subgroup A := (powMonoidHom (α := A) (ℓ ^ s)).range
    let powerMap : A →ₜ* A :=
      ⟨powMonoidHom (ℓ ^ s), continuous_id.pow _⟩
    have hPclosed : IsClosed (P : Set A) :=
      ContinuousMonoidHom.isClosed_range powerMap
    have : IsClosed (P : Set A) := hPclosed
    have : TotallyDisconnectedSpace A :=
      ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
        (Subgroup.closedCommutator G) (Subgroup.isClosed_closedCommutator G)
    have : TotallyDisconnectedSpace (A ⧸ P) :=
      ProCGroups.totallyDisconnectedSpace_quotient_closedNormal P hPclosed
    let q : A →ₜ* (A ⧸ P) :=
      ⟨QuotientGroup.mk' P, QuotientGroup.continuous_mk⟩
    have hpow (a : A ⧸ P) : a ^ (ℓ ^ s) = 1 := by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective P a
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (N := P) (a ^ (ℓ ^ s))).mpr ⟨a, rfl⟩
    have hAP := hasOpenNormalBasisInClass_sigma_of_primePower_exponent
      ℓ hℓ hℓsigma s hpow
    let ψ : Q →ₜ* (A ⧸ P) :=
      lift_proCResidualCoreQuotient
        (FiniteGroupClass.sigmaGroup_fullFormation sigma).hereditary
        (q.comp (TopologicalAbelianization.mkₜ G)) hAP
    let F := TopologicalAbelianization.lift ψ
    have hcompare (a : A) : F (f a) = q a := by
      obtain ⟨g, rfl⟩ := TopologicalAbelianization.surjective_mk G a
      change TopologicalAbelianization.lift ψ
        (TopologicalAbelianization.mk Q (QuotientGroup.mk' R g)) = _
      rw [TopologicalAbelianization.lift_apply_mk, lift_proCResidualCoreQuotient_mk]
      rfl
    have hq : q x = q y := (hcompare x).symm.trans ((congrArg F hxy).trans (hcompare y))
    have hmem : y⁻¹ * x ∈ P := QuotientGroup.eq.mp hq.symm
    obtain ⟨b, hb⟩ := hmem
    refine ⟨b, ?_⟩
    change b ^ (ℓ ^ s) = y⁻¹ * x at hb
    rw [hb, ← mul_assoc, mul_inv_cancel, one_mul]
  · intro hxy
    have hA := residualAbelianization_hasOpenNormalBasisInClass (sigma := sigma) G
    have hzero : f x * (f y)⁻¹ = 1 := by
      apply hA.eq_one_of_primePower_roots
      intro ℓ hℓsigma hℓ s hs
      obtain ⟨b, hb⟩ := hxy ℓ hℓsigma hℓ s hs
      refine ⟨f b, ?_⟩
      rw [hb, map_mul, map_pow, mul_comm (f y), mul_assoc, mul_inv_cancel, mul_one]
    exact mul_inv_eq_one.mp hzero


/-- Trivial residual conjugation is equivalent to trivial conjugation modulo all
Sigma prime powers. -/
theorem residualAbelianizationQuotientConjugation_eq_one_iff_primePower
    {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    residualAbelianizationQuotientConjugation
        (FiniteGroupClass.sigmaGroup_fullFormation sigma) N hN = 1 ↔
      ∀ g : G ⧸ N, ∀ a : TopologicalAbelianization N,
        ∀ ℓ : ℕ, ℓ ∈ sigma → ℓ.Prime → ∀ s : ℕ, 0 < s →
          ∃ b : TopologicalAbelianization N,
            quotientConjugationTopologicalAbelianizationMap N g a = a * b ^ (ℓ ^ s) := by
  have : CompactSpace N := hN.isClosedEmbedding_subtypeVal.compactSpace
  let R := proCResidualCore (FiniteGroupClass.sigmaGroup sigma) N
  let π : N →ₜ* (N ⧸ R) := ⟨QuotientGroup.mk' R, QuotientGroup.continuous_mk⟩
  let f := TopologicalAbelianization.map π
  let ρ := residualAbelianizationQuotientConjugation
    (FiniteGroupClass.sigmaGroup_fullFormation sigma) N hN
  have hcompare (g : G ⧸ N) (a : TopologicalAbelianization N) :
      f (quotientConjugationTopologicalAbelianizationMap N g a) = ρ g (f a) := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
    obtain ⟨n, rfl⟩ := TopologicalAbelianization.surjective_mk N a
    change TopologicalAbelianization.map π
        (quotientConjugationTopologicalAbelianizationMap N (QuotientGroup.mk' N g)
          (TopologicalAbelianization.mk N n)) =
      TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv
          (FiniteGroupClass.sigmaGroup_fullFormation sigma) N hN g)
        (TopologicalAbelianization.map π (TopologicalAbelianization.mk N n))
    simp only [quotientConjugationTopologicalAbelianizationMap_mk_apply_mk,
      TopologicalAbelianization.map_apply_mk]
    exact (congrArg (TopologicalAbelianization.mk (N ⧸ R))
      (residualQuotientConjugationContinuousMulEquiv_apply_mk
        (FiniteGroupClass.sigmaGroup_fullFormation sigma) N hN g n)).symm
  change ρ = 1 ↔ _
  constructor
  · intro hρ g a
    apply (residualAbelianization_map_eq_iff_primePower (sigma := sigma) N
      (quotientConjugationTopologicalAbelianizationMap N g a) a).mp
    change f (quotientConjugationTopologicalAbelianizationMap N g a) = f a
    rw [hcompare, hρ]
    rfl
  · intro hpow
    apply MonoidHom.ext
    intro g
    apply MulEquiv.ext
    intro z
    obtain ⟨a, rfl⟩ :=
      TopologicalAbelianization.surjective_map_of_surjective π (QuotientGroup.mk'_surjective R) z
    change ρ g (f a) = f a
    rw [← hcompare]
    exact (residualAbelianization_map_eq_iff_primePower (sigma := sigma) N
      (quotientConjugationTopologicalAbelianizationMap N g a) a).mpr (hpow g a)

end ProCGroups.ProC
