/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.CyclicExtension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Primitive eigenunits in prime-degree Galois extensions

A nonidentity automorphism of a prime-degree Galois extension has an
eigenunit with primitive eigenvalue when the base field contains the
corresponding roots of unity. The unit is produced by the cyclic Kummer
radical generator theorem.
-/

namespace KummerTheory

open IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A nonidentity automorphism of a prime-degree Galois extension admits
an eigenunit with a primitive eigenvalue, constructed from roots of unity
in the base field. -/
theorem exists_primitive_eigenunit_of_prime_degree
    [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (hμ : (primitiveRoots p K).Nonempty)
    (σ : Gal(L/K)) (hσ : σ ≠ 1) :
    ∃ α : Lˣ, ∃ ζ : Lˣ,
      IsPrimitiveRoot ζ p ∧ Units.map σ.toMonoidHom α = ζ * α := by
  have hcard : Nat.card Gal(L/K) = p :=
    (IsGalois.card_aut_eq_finrank K L).trans hdeg
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic Gal(L/K) := isCyclic_of_prime_card hcard
  have hexponent : ∀ τ : Gal(L/K), τ ^ p = 1 := by
    intro τ
    rw [← hcard]
    exact pow_card_eq_one'
  obtain ⟨a, ha, hapow, hagen⟩ :=
    exists_single_radical_generator_of_cyclic_galois_exponent
      (K := K) (L := L) ⟨p, hp.pos⟩ hμ hexponent
  obtain ⟨b, hb⟩ := hapow
  change algebraMap K L b = a ^ p at hb
  have hfixpow : σ (a ^ p) = a ^ p := by
    rw [← hb]
    exact σ.commutes b
  have hquotpow : (σ a / a) ^ p = 1 := by
    rw [div_pow, ← map_pow, hfixpow, div_self (pow_ne_zero p ha)]
  have hquotne : σ a / a ≠ 1 := by
    intro hquot
    have hfixa : σ a = a := (div_eq_one_iff_eq ha).1 hquot
    apply hσ
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ K⟮a⟯ := by
      rw [hagen]
      exact IntermediateField.mem_top
    change σ x = x
    refine IntermediateField.adjoin_induction K
      (p := fun y _hy => σ y = y) ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      have hya : y = a := Set.mem_singleton_iff.1 hy
      rw [hya]
      exact hfixa
    · intro y
      exact σ.commutes y
    · intro y z hy hz hfy hfz
      rw [map_add, hfy, hfz]
    · intro y hy hfy
      rw [map_inv₀, hfy]
    · intro y z hy hz hfy hfz
      rw [map_mul, hfy, hfz]
  have hprim : IsPrimitiveRoot (σ a / a) p :=
    isPrimitiveRoot_of_mem_nthRootsFinset hp
      ((Polynomial.mem_nthRootsFinset hp.pos (1 : L)).2 hquotpow) hquotne
  let α : Lˣ := Units.mk0 a ha
  let ζ : Lˣ := Units.map σ.toMonoidHom α / α
  refine ⟨α, ζ, ?_, ?_⟩
  · apply IsPrimitiveRoot.coe_units_iff.1
    simp only [ζ, α, Units.val_div_eq_div_val, Units.coe_map, Units.val_mk0]
    exact hprim
  · exact (div_mul_cancel (Units.map σ.toMonoidHom α) α).symm

end KummerTheory
