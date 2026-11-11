/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SawinTotallyRealTowers.RealProTwoInitialPresentation
public import Nyll.SawinTotallyRealTowers.RealProTwoDeepFrobenius
public import Nyll.SawinTotallyRealTowers.RealProPFrobenius
public import Nyll.SawinTotallyRealTowers.RealProPFrobeniusCut
public import Nyll.SawinTotallyRealTowers.FrobeniusWeightBudget
public import Nyll.SawinTotallyRealTowers.MaximalRealProPOutside
public import Nyll.SawinTotallyRealTowers.SixPrimeSupport
public import Nyll.ProCGroups.ProP.Presentation.FiniteGeneration
public import Nyll.ProCGroups.ProP.Presentation.RelatorDepth
public import Nyll.ProCGroups.GolodShafarevich.CountableRelatorTarget
public import Nyll.ProCGroups.Presentations.Profinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Finset.Range
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NormNum

/-!
# An infinite Frobenius quotient of the initial real pro-two group

Choose genuine primes and source lifts at depths n + 5 in the actual
minimal presentation from S1. The prescribed finite-prefix budget allows
all these Frobenius relations to be imposed while the quotient stays infinite.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

open ProCGroups ProCGroups.Presentations ClassFieldTower.ProP

private local instance frobeniusSequencePrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

attribute [local instance] maximalRealProPOutside_isGalois

/-- The same actual minimal presentation admits a sequence of deep source
lifts of arithmetic Frobenius at primes escaping every initial interval. -/
theorem exists_sawinDeepFrobenius_sequence :
    ∃ sourceData : FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{0, 0}
      (FiniteGroupClass.pGroup 2),
      ∃ r : ℕ, ∃ P : FiniteProPPresentation 2 5 r sourceData
        (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
          maximalRealProPOutside 2 sawinRationalPrimeSupport),
        P.IsMinimal ∧ r ≤ 6 ∧
        ∃ primes : ℕ → Nat.Primes, ∃ f : ℕ → sourceData.carrier, ∀ n : ℕ,
          n < (primes n).val ∧
          (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (primes n) ∉
            sawinRationalPrimeSupport ∧
          (primes n).val % 4 = 1 ∧
          P.quotient (f n) = maximalRealProPArithmeticFrobenius 2 sawinRationalPrimeSupport
            ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (primes n)) ∧
          ZassenhausDepthAtLeast 2 (sawinFrobeniusDepth n) (f n) := by
  classical
  obtain ⟨sourceData, r, P, hP, hr⟩ := exists_sawinInitialProTwo_minimalPresentation
  choose primes hbad hsupport hmod f hf hdepth using fun n : ℕ ↦
    exists_sawinPrime_with_deep_frobenius_lift
      P.source_topologicallyFinitelyGenerated P.quotient P.quotient_surjective
      (sawinFrobeniusDepth n) (Finset.range (n + 1))
  refine ⟨sourceData, r, P, hP, hr, primes, f, fun n ↦ ?_⟩
  refine ⟨?_, hsupport n, hmod n, hf n, hdepth n⟩
  have hnot : ¬(primes n).val < n + 1 := fun h ↦ hbad n (Finset.mem_range.mpr h)
  omega

/-- Infinitely many selected rational primes are congruent to one modulo
four and outside the six ramified primes. Killing all their actual Frobenius
elements leaves an infinite quotient of the actual initial arithmetic group. -/
theorem exists_sawinInfinite_frobenius_quotient :
    ∃ primes : ℕ → Nat.Primes,
      (∀ n : ℕ, n < (primes n).val ∧
        (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (primes n) ∉
          sawinRationalPrimeSupport ∧
        (primes n).val % 4 = 1) ∧
      (Set.range primes).Infinite ∧
      Infinite ((maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
        maximalRealProPOutside 2 sawinRationalPrimeSupport) ⧸
        closedNormalClosure (Set.range (fun n : ℕ ↦
          maximalRealProPArithmeticFrobenius 2 sawinRationalPrimeSupport
            ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (primes n))))) := by
  obtain ⟨sourceData, r, P, hP, hr, primes, f, h⟩ := exists_sawinDeepFrobenius_sequence
  have hInfinite := P.infinite_target_quotient_of_countable_relator_budget
    (fun _ ↦ 2) (P.relatorZassenhausDepthAtLeast_two hP)
    f sawinFrobeniusDepth (fun n ↦ (h n).2.2.2.2)
    (t := (5 / 12 : ℝ)) (by norm_num) (by norm_num)
    (sawinGsPolynomial_frobenius_prefix_nonpos r hr)
  have hmap : P.quotient ∘ f = fun n : ℕ ↦
      maximalRealProPArithmeticFrobenius 2 sawinRationalPrimeSupport
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (primes n)) :=
    funext (fun n ↦ (h n).2.2.2.1)
  rw [hmap] at hInfinite
  refine ⟨primes, fun n ↦ ⟨(h n).1, (h n).2.1, (h n).2.2.1⟩, ?_, hInfinite⟩
  have hvalues : (Set.range (fun n : ℕ ↦ (primes n).val)).Infinite :=
    Set.infinite_of_forall_exists_gt (fun a ↦ ⟨(primes a).val, ⟨a, rfl⟩, (h a).1⟩)
  intro hfinite
  apply hvalues
  apply (hfinite.image (fun q : Nat.Primes ↦ q.val)).subset
  rintro _ ⟨n, rfl⟩
  exact ⟨primes n, ⟨n, rfl⟩, rfl⟩

/-- S2 and S3 yield an infinite actual quotient in which the entire
decomposition group at every selected prime acts trivially. -/
theorem exists_sawinInfinite_decomposition_split_quotient :
    ∃ primes : ℕ → Nat.Primes,
      let v : ℕ → HeightOneSpectrum (𝓞 ℚ) := fun n ↦
        (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (primes n)
      (∀ n : ℕ, n < (primes n).val ∧ v n ∉ sawinRationalPrimeSupport ∧
        (primes n).val % 4 = 1) ∧
      (Set.range primes).Infinite ∧
      Infinite (RealProPFrobeniusCut 2 sawinRationalPrimeSupport v) ∧
      ∀ (n : ℕ) (σ : ClassFieldTower.Martinet.Shafarevich.finitePlaceAbsoluteDecompositionGroup
          ℚ (v n)),
        realProPFrobeniusCutProjection 2 sawinRationalPrimeSupport v
          (maximalRealProPDecompositionMap 2 sawinRationalPrimeSupport (v n) σ) = 1 := by
  obtain ⟨primes, hprimes, hrange, hInfinite⟩ := exists_sawinInfinite_frobenius_quotient
  refine ⟨primes, hprimes, hrange, hInfinite, ?_⟩
  intro n σ
  exact realProPFrobeniusCutProjection_decomposition 2 sawinRationalPrimeSupport
    (fun i ↦ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (primes i))
    n (hprimes n).2.1 σ

end ClassFieldTower.Sawin
