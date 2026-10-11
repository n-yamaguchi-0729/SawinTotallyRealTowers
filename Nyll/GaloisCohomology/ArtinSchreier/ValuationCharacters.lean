/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ArtinSchreier.NontrivialCharacter
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ArtinSchreierNonSurjective
import Nyll.ValuedFieldTheory.Valuation.Completion.DiscreteValuedCompletion
import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology

/-! # Nontrivial prime cyclic characters from discrete valuations -/

namespace ArtinSchreierTheory
universe u v
open ValuationTheory.DiscreteValuationField
variable {K : Type u} [Field K]

/-- A discrete valuation in characteristic `p` produces a nontrivial continuous
prime cyclic character on the actual absolute Galois group. -/
theorem exists_nontrivial_absolute_character_of_DVF
    (D : DVF.{u, v} K) (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod p),
      ∃ σ : Gal(AlgebraicClosure K/K), χ σ ≠ 1 := by
  obtain ⟨χ, σ, hσ⟩ := exists_nontrivial_character_of_artinSchreier_not_surjective
    (K := K) (Ω := SeparableClosure K) p
    (D.exists_not_pow_sub p (Fact.out : p.Prime).one_lt)
  let e := ValuationTheory.Completion.separableClosureAutContinuousEquiv K
  refine ⟨χ.comp (e : Gal(AlgebraicClosure K/K) →ₜ* Gal(SeparableClosure K/K)),
    e.symm σ, ?_⟩
  change χ (e (e.symm σ)) ≠ 1
  rw [e.apply_symm_apply]
  exact hσ

/-- The valued completion of a discrete valuation in characteristic `p`
has a nontrivial continuous prime cyclic character. -/
theorem exists_nontrivial_completion_character_of_DVF
    (D : DVF.{u, v} K) (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ χ : Gal(AlgebraicClosure D.valuation.Completion/D.valuation.Completion) →ₜ*
      Multiplicative (ZMod p),
      ∃ σ : Gal(AlgebraicClosure D.valuation.Completion/D.valuation.Completion), χ σ ≠ 1 := by
  have : CharP D.valuation.Completion p :=
    (Algebra.charP_iff K D.valuation.Completion p).mp inferInstance
  have : (Valued.v : _root_.Valuation D.valuation.Completion
    D.ValueGroup).IsRankOneDiscrete := Valuation.completion_isRankOneDiscrete D.valuation
  let Dc : DVF D.valuation.Completion :=
    { ValueGroup := D.ValueGroup
      valuation := Valued.v }
  exact exists_nontrivial_absolute_character_of_DVF Dc p

end ArtinSchreierTheory
