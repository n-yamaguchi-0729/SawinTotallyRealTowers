/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicInfiniteImage
import Nyll.GaloisCohomology.ProfiniteIntegers.PadicUnitInfiniteImage
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.PrimePowerRoots
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Prime cyclic characters of mixed-characteristic discretely valued fields

Finiteness of primary roots in every finite extension forces the cyclotomic
character to have infinite image. Its image therefore has a cyclic quotient
of order equal to the residue characteristic.
-/

namespace KummerTheory
open ValuationTheory.DiscreteValuationField
variable {K : Type*} [Field K] [CharZero K]

/-- Every mixed-characteristic discretely valued field has a continuous cyclic
quotient of residue-prime order. -/
theorem exists_surjective_prime_character_of_mixedChar
    (base : DVF K) (p : ℕ) [Fact p.Prime] [CharP base.residueField p] :
    ∃ ψ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod p),
      Function.Surjective ψ := by
  have (i : ℕ) : HasEnoughRootsOfUnity (AlgebraicClosure K) (p ^ i) := by
    infer_instance
  have hRoots (E : IntermediateField K (AlgebraicClosure K))
      (hE : FiniteDimensional K E) : Finite (CommGroup.primaryComponent Eˣ p) := by
    have : Finite {ζ : E | ∃ n : ℕ, ζ ^ (p ^ n) = 1} :=
      (base.finite_primePowerRoots_of_finiteExtension (L := E) p).to_subtype
    let f : CommGroup.primaryComponent Eˣ p → {ζ : E | ∃ n : ℕ, ζ ^ (p ^ n) = 1} :=
      fun z => ⟨(z.val : E), by
        obtain ⟨n, hn⟩ := z.property
        exact ⟨n, congrArg Units.val hn⟩⟩
    apply Finite.of_injective f
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val hab
  let χ : Gal(AlgebraicClosure K/K) →ₜ* (PadicInt p)ˣ :=
    ⟨(cyclotomicCharacter (AlgebraicClosure K) p).comp
      (MulSemiringAction.toRingAut Gal(AlgebraicClosure K/K) (AlgebraicClosure K)),
      cyclotomicCharacter.continuous p K (AlgebraicClosure K)⟩
  exact PadicInt.exists_surjective_prime_character_of_infinite_unit_image χ
    (infinite_range_cyclotomicCharacter_of_finite_primary p hRoots)
end KummerTheory
