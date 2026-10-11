/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaStructure
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Prime-order inertia detects residual roots

The faithful residue-unit character in characteristic zero turns a nonidentity
prime-order inertia element into an actual primitive root in the residue field.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- In residue characteristic zero, a nontrivial inertia element of prime order
forces a primitive root of that order in the actual residue field. -/
theorem exists_primitiveRoot_residue_of_inertia_prime_order
    (A : _root_.ValuationSubring L) [Finite (inertiaGroup K A)]
    [CharZero (IsLocalRing.ResidueField A)]
    {p : ℕ} (hp : p.Prime) (σ : inertiaGroup K A)
    (hσ : σ ≠ 1) (hpow : σ ^ p = 1) :
    (primitiveRoots p (IsLocalRing.ResidueField A)).Nonempty := by
  classical
  have htop := valueTrivialInertiaGroup_eq_top_of_finite K A
  let s : valueTrivialInertiaGroup K A := ⟨σ, htop.symm ▸ Subgroup.mem_top σ⟩
  have hs : valueTrivialInertiaCharacterHom K A s ≠ 1 := by
    intro h
    apply hσ
    have hmem : σ ∈ ramificationGroup K A :=
      (valueTrivialInertiaCharacterHom_mem_ker_iff K A s).mp h
    rw [ramificationGroup_eq_bot_of_residueCharZero K A] at hmem
    exact hmem
  obtain ⟨x, hx⟩ : ∃ x, valueTrivialInertiaCharacterHom K A s x ≠ 1 := by
    by_contra h
    apply hs
    apply MonoidHom.ext
    intro x
    exact Classical.not_not.mp (not_exists.mp h x)
  let ζ : IsLocalRing.ResidueField A := valueTrivialInertiaCharacterHom K A s x
  have hζpow : ζ ^ p = 1 := by
    have hsPow : s ^ p = 1 := Subtype.ext hpow
    have h := congrArg (fun f => (f x : IsLocalRing.ResidueField A))
      (congrArg (valueTrivialInertiaCharacterHom K A) hsPow)
    simpa only [map_pow, map_one, MonoidHom.pow_apply, MonoidHom.one_apply,
      Units.val_pow_eq_pow_val, Units.val_one] using h
  have hζne : ζ ≠ 1 := by
    intro h
    apply hx
    exact Units.ext h
  exact ⟨ζ, (mem_primitiveRoots hp.pos).mpr (isPrimitiveRoot_of_mem_nthRootsFinset hp
    ((Polynomial.mem_nthRootsFinset hp.pos 1).mpr hζpow) hζne)⟩

end RamificationTheory.HilbertRamification.ValuationSubring
