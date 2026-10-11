/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.GaloisCohomology.Kummer.Concrete.InvariantCompletionCharacter
import Nyll.GaloisCohomology.Kummer.Concrete.NormalRestrictionCharacterExtension
import Nyll.ValuedFieldTheory.Valuation.Completion.CyclotomicCompletion
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.ProlongationDiscrete
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicGaloisCard
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicIntermediateField

/-!
# Completion characters by cyclotomic descent

Weak approximation for cyclic characters descends from a prime
cyclotomic extension using an invariant character lift and restriction
at each completion. The resulting simultaneous approximation applies
whenever the prime modulus differs from the field characteristic.
-/

namespace KummerTheory

open ValuationTheory.DiscreteValuationField
open Field.absoluteGaloisGroup

universe u v w

/-- Weak approximation for cyclic characters descends from the prime cyclotomic extension. -/
theorem surjective_completion_characters_of_cyclotomic
    {ι : Type*} [Finite ι] {K : Type u} {E : Type w}
    [Field K] [Field E] [Algebra K E]
    (D : ι → DVF.{u, v} K)
    (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))
    (q : ℕ) [Fact q.Prime] [NeZero (q : K)]
    [IsCyclotomicExtension {q} K E] :
    Function.Surjective (fun ψ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod q) =>
      fun i => (ψ.comp (map (algebraMap K (D i).valuation.Completion)) :
        Gal(AlgebraicClosure (D i).valuation.Completion/(D i).valuation.Completion) →ₜ*
          Multiplicative (ZMod q))) := by
  classical
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {q} K E
  have : IsGalois K E := IsCyclotomicExtension.isGalois {q} K E
  have hV (i : ι) : ∃ V : DVF.{w,v} E, (D i).valuation.HasExtension V.valuation := by
    obtain ⟨v, hd, he⟩ := (D i).exists_extension_on_valueGroup (L := E)
    exact ⟨{ ValueGroup := (D i).ValueGroup, valuation := v }, he⟩
  choose V hV using hV
  have : ∀ i, (D i).valuation.HasExtension (V i).valuation := hV
  let n : ℕ+ := ⟨q, (Fact.out : q.Prime).pos⟩
  have : NeZero ((n : ℕ) : E) :=
    (show NeZero (q : E) from
      NeZero.nat_of_injective (f := algebraMap K E) (algebraMap K E).injective)
  have hcard : (Nat.card Gal(E/K)).Coprime q :=
    (prime_coprime_cyclotomicGalois_natCard K E q).symm
  have hdegree : (Module.finrank K E).Coprime q := by
    rw [← IsGalois.card_aut_eq_finrank K E]
    exact hcard
  have hmu : (primitiveRoots (n : ℕ) E).Nonempty := by
    obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K E
      (Set.mem_singleton q) (NeZero.ne q)
    exact ⟨ζ, (mem_primitiveRoots n.pos).mpr hζ⟩
  intro χ
  obtain ⟨η, hηinv, hηlocal⟩ := exists_invariant_completion_character D hD V n hcard hmu χ
  obtain ⟨ψ, hψ⟩ := exists_absoluteCharacter_extension_of_coprime_finrank q hdegree η hηinv
  refine ⟨ψ, funext fun i => ?_⟩
  let : Algebra (D i).valuation.Completion (V i).valuation.Completion :=
    DVF.completionAlgebra (D i) (V i)
  have : IsCyclotomicExtension {q} (D i).valuation.Completion (V i).valuation.Completion :=
    DVF.completion_isCyclotomicExtension (D i) (V i) q
  have : FiniteDimensional (D i).valuation.Completion (V i).valuation.Completion :=
    IsCyclotomicExtension.finiteDimensional {q} (D i).valuation.Completion
      (V i).valuation.Completion
  have : IsGalois (D i).valuation.Completion (V i).valuation.Completion :=
    IsCyclotomicExtension.isGalois {q} (D i).valuation.Completion (V i).valuation.Completion
  have hlocaldegree :
      (Module.finrank (D i).valuation.Completion (V i).valuation.Completion).Coprime q := by
    rw [← IsGalois.card_aut_eq_finrank (D i).valuation.Completion (V i).valuation.Completion]
    exact (prime_coprime_cyclotomicGalois_natCard (D i).valuation.Completion
      (V i).valuation.Completion q).symm
  apply absoluteCharacterRestriction_injective_of_coprime_finrank
    (K := (D i).valuation.Completion) (E := (V i).valuation.Completion) q hlocaldegree
  have hsquare : (DVF.completionMap (D i) (V i)).comp
      (algebraMap K (D i).valuation.Completion) =
      (algebraMap E (V i).valuation.Completion).comp (algebraMap K E) := by
    ext x
    exact DVF.completionMap_coe_base (D i) (V i) x
  exact (character_map_comp (algebraMap K (D i).valuation.Completion)
    (DVF.completionMap (D i) (V i)) ψ).symm.trans
      ((congrArg (fun f => ψ.comp (map f)) hsquare).trans
        ((character_map_comp (algebraMap K E) (algebraMap E (V i).valuation.Completion) ψ).trans
          ((congrArg (fun θ => θ.comp (map (algebraMap E (V i).valuation.Completion))) hψ).trans
            (hηlocal i))))

/-- Cyclic characters satisfy simultaneous weak approximation in characteristic
prime to their prime modulus, without a roots-of-unity hypothesis. -/
theorem surjective_completion_characters_of_ne_char
    {ι : Type*} [Finite ι] {K : Type u} [Field K]
    (D : ι → DVF.{u, v} K)
    (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))
    (q : ℕ) [Fact q.Prime] [NeZero (q : K)] :
    Function.Surjective (fun ψ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod q) =>
      fun i => (ψ.comp (map (algebraMap K (D i).valuation.Completion)) :
        Gal(AlgebraicClosure (D i).valuation.Completion/(D i).valuation.Completion) →ₜ*
          Multiplicative (ZMod q))) := by
  obtain ⟨E, hE⟩ := exists_cyclotomic_intermediateField K (AlgebraicClosure K) q
  have : IsCyclotomicExtension {q} K E := hE
  exact surjective_completion_characters_of_cyclotomic (E := E) D hD q

end KummerTheory
