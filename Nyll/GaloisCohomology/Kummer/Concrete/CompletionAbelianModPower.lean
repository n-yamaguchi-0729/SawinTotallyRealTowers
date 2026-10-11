/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicCompletionApproximation
import Nyll.ProCGroups.Abelian.PrimeExponentCharacters
import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Injectivity on mod-prime abelianizations of valued completions

When the prime is different from the field characteristic, extension of
completion characters separates every class in the local abelian quotient.
-/

namespace KummerTheory
open ValuationTheory.DiscreteValuationField ProCGroups.Abelian
open Field.absoluteGaloisGroup
universe u v

/-- The completion embedding induces an injection on absolute Galois
abelianizations modulo a prime different from the field characteristic. -/
theorem completion_abelianModPowerMap_injective
    {K : Type u} [Field K] (D : DVF.{u, v} K) (q : ℕ)
    [Fact q.Prime] [NeZero (q : K)] :
    Function.Injective (abelianModPowerMap q
      (map (algebraMap K D.valuation.Completion))) := by
  let family : Fin 1 → DVF.{u,v} K := fun _ => D
  have hfamily : Pairwise (fun i j => ¬ (family i).valuation.IsEquiv (family j).valuation) := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  let H : Fin 1 → Type u := fun _ =>
    Gal(AlgebraicClosure D.valuation.Completion/D.valuation.Completion)
  have (i : Fin 1) : CompactSpace (H i) :=
    (ValuationTheory.Completion.separableClosureAutContinuousEquiv
      D.valuation.Completion).symm.toHomeomorph.compactSpace
  have hchar := surjective_completion_characters_of_ne_char family hfamily q
  have hi := injective_prod_abelianModPowerMap_of_character_surjective (q := q) H
    (fun _ => map (algebraMap K D.valuation.Completion)) hchar
  intro x y hxy
  have heq : (∏ i : Fin 1, abelianModPowerMap q
      (map (algebraMap K D.valuation.Completion)) ((fun _ => x) i)) =
      ∏ i : Fin 1, abelianModPowerMap q
        (map (algebraMap K D.valuation.Completion)) ((fun _ => y) i) := by
    simpa only [Fin.prod_univ_one] using hxy
  exact congrFun (hi heq) 0
end KummerTheory
