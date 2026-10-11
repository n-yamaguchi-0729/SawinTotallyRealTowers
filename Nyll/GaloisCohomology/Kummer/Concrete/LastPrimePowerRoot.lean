/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.PrimePowerRootObstruction
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The last prime-power root level

Finiteness of the prime-power roots gives a maximal primitive-root exponent.
At this exponent a primitive root of prime order has nonidentity power class.
-/

namespace KummerTheory

variable {K : Type*} [Field K]

/-- A finite set of prime-power roots has a last primitive-root level. The
maximality statement also bounds every other available level. -/
theorem exists_last_primePower_primitiveRoot {p : ℕ} (hp : p.Prime)
    (hfinite : Set.Finite {ζ : K | ∃ n : ℕ, ζ ^ (p ^ n) = 1}) :
    ∃ s : ℕ, (primitiveRoots (p ^ s) K).Nonempty ∧
      (∀ m : ℕ, (primitiveRoots (p ^ m) K).Nonempty → m ≤ s) ∧
      ¬ (primitiveRoots (p ^ (s + 1)) K).Nonempty := by
  classical
  let levels : Set ℕ := {m : ℕ | (primitiveRoots (p ^ m) K).Nonempty}
  have hlevels : levels.Finite := by
    apply ((hfinite.image (orderOf : K → ℕ)).preimage
      (Nat.pow_right_injective hp.two_le).injOn).subset
    intro m hm
    obtain ⟨ζ, hζ⟩ := hm
    have hprim : IsPrimitiveRoot ζ (p ^ m) := isPrimitiveRoot_of_mem_primitiveRoots hζ
    exact ⟨ζ, ⟨m, hprim.pow_eq_one⟩, hprim.eq_orderOf.symm⟩
  have hzero : 0 ∈ levels := by
    change (primitiveRoots (p ^ 0) K).Nonempty
    rw [pow_zero, IsPrimitiveRoot.primitiveRoots_one]
    exact Finset.singleton_nonempty (1 : K)
  obtain ⟨s, hs, hmax⟩ := Set.exists_max_image levels (fun m : ℕ => m)
    hlevels ⟨0, hzero⟩
  refine ⟨s, hs, hmax, ?_⟩
  intro hnext
  exact Nat.not_succ_le_self s (hmax (s + 1) hnext)

/-- If a primitive root of prime order exists, finiteness of all prime-power
roots supplies a positive last exponent and a nonidentity power class there. -/
theorem exists_last_primePowerRoot_nontrivial_class {p : ℕ} (hp : p.Prime)
    (hfinite : Set.Finite {ξ : K | ∃ n : ℕ, ξ ^ (p ^ n) = 1})
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ s : ℕ, 1 ≤ s ∧ (primitiveRoots (p ^ s) K).Nonempty ∧
      (∀ m : ℕ, (primitiveRoots (p ^ m) K).Nonempty → m ≤ s) ∧
      ¬ (primitiveRoots (p ^ (s + 1)) K).Nonempty ∧
      (ζ : Kˣ ⧸ (powMonoidHom (p ^ s) : Kˣ →* Kˣ).range) ≠ 1 := by
  obtain ⟨s, hs, hmax, hnext⟩ := exists_last_primePower_primitiveRoot hp hfinite
  have hone : (primitiveRoots (p ^ 1) K).Nonempty := by
    rw [pow_one]
    exact ⟨(ζ : K), (mem_primitiveRoots hp.pos).mpr
      (IsPrimitiveRoot.coe_units_iff.mpr hζ)⟩
  exact ⟨s, hmax 1 hone, hs, hmax, hnext,
    primitiveRoot_primePowerClass_ne_one hp s hζ hnext⟩

end KummerTheory
