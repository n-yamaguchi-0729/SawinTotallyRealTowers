/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.GroupTheory.FiniteOrbitProduct
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerCharacterAction
import Nyll.GaloisCohomology.Kummer.Concrete.RootKummerInvariantCharacter
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicCompositumCommutation
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicGaloisCard
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Defs

/-!
# An invariant Kummer trace retaining a nontrivial difference

The orbit product of an eigenunit's Kummer character is invariant under
the upper cyclotomic group. The commuting automorphism changes it by the
root's Kummer character to the cyclotomic degree. Coprimality prevents this
nontrivial difference from disappearing.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory GroupTheory

-- Keep the orbit calculation in its six-structure group/topology context;
-- it needs none of the four-field algebra towers of the Kummer construction.
private theorem invariant_moved_character_of_coprime
    {G Γ A : Type*} [Group G] [Fintype G] [Monoid Γ] [TopologicalSpace Γ]
    [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    (ρ : G →* MulAut (Γ →ₜ* A)) (a : MulAut (Γ →ₜ* A)) (C D : Γ →ₜ* A)
    (hcomm : ∀ g : G, Commute a (ρ g)) (hdiff : a C / C = D)
    (hD : ∀ g : G, ρ g D = D) (hDne : D ≠ 1)
    (hcop : (Nat.card A).Coprime (Fintype.card G)) :
    ∃ T : Γ →ₜ* A, (∀ g : G, ρ g T = T) ∧ a T ≠ T := by
  let T : Γ →ₜ* A := finiteOrbitProduct ρ C
  have htrace : a T / T = D ^ Fintype.card G :=
    finiteOrbitProduct_map_div ρ a C D hcomm hdiff hD
  have hpowinj : Function.Injective (fun x : A => x ^ Fintype.card G) :=
    hcop.pow_left_bijective.injective
  refine ⟨T, finiteOrbitProduct_invariant ρ C, ?_⟩
  intro hfixed
  have hpow : D ^ Fintype.card G = 1 := by
    rw [← htrace, hfixed, div_self']
  apply hDne
  apply ContinuousMonoidHom.ext
  intro σ
  change D σ = 1
  have heval := DFunLike.congr_fun hpow σ
  simp only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.coe_one, Pi.one_apply] at heval
  exact hpowinj (heval.trans (one_pow (Fintype.card G)).symm)

variable {F K L E : Type*} [Field F] [Field K] [Field L] [Field E]
  [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
  [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K] [CharZero E]

-- Four fields, five algebras and two towers: eleven data structures.
-- The sole new local instance is the cyclotomic finite-dimensionality proposition.
/-- A root-valued eigenunit difference survives the actual cyclotomic orbit
product. The root fixing and commutation are generated from the two fields. -/
theorem exists_invariant_moved_cyclotomicKummerTrace
    (p : ℕ) [Fact p.Prime]
    [IsCyclotomicExtension {p} F L] [IsCyclotomicExtension {p} K E]
    (s : ℕ) (hmu : (primitiveRoots (p ^ (s + 1)) E).Nonempty)
    (hdown : ∀ ξ : E, ξ ^ (p ^ (s + 1)) = 1 → ξ ∈ Set.range (algebraMap L E))
    (τ : E ≃ₐ[L] E) (α ζ : Eˣ)
    (hα : Units.map τ.toRingEquiv.toMonoidHom α = ζ * α)
    (hζroot : (ζ : E) ^ p = 1)
    (hζclass : (ζ : Eˣ ⧸ (powMonoidHom (p ^ (s + 1)) : Eˣ →* Eˣ).range) ≠ 1) :
    ∃ T : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod (p ^ (s + 1))),
      (∀ δ : E ≃ₐ[K] E,
        absoluteContinuousCharacterAction (K := E)
          (A := Multiplicative (ZMod (p ^ (s + 1)))) δ.toRingEquiv T = T) ∧
      absoluteContinuousCharacterAction (K := E)
        (A := Multiplicative (ZMod (p ^ (s + 1)))) τ.toRingEquiv T ≠ T := by
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {p} K E
  let n : ℕ+ := ⟨p ^ (s + 1), pow_pos (Fact.out : p.Prime).pos (s + 1)⟩
  let A := Multiplicative (ZMod (n : ℕ))
  let κ : (Eˣ ⧸ (powMonoidHom (n : ℕ) : Eˣ →* Eˣ).range) ≃*
      (Gal(AlgebraicClosure E/E) →ₜ* A) := absoluteKummerContinuousZModCharacterEquiv E n hmu
  let C : Gal(AlgebraicClosure E/E) →ₜ* A := κ α
  let D : Gal(AlgebraicClosure E/E) →ₜ* A := κ ζ
  let act : RingAut E →* MulAut (Gal(AlgebraicClosure E/E) →ₜ* A) :=
    absoluteContinuousCharacterAction (K := E) (A := A)
  let ρ : (E ≃ₐ[K] E) →* MulAut (Gal(AlgebraicClosure E/E) →ₜ* A) :=
    act.comp (MulSemiringAction.toRingEquiv (E ≃ₐ[K] E) E)
  have hfix : ∀ ξ : E, ξ ^ (n : ℕ) = 1 → τ.toRingEquiv ξ = ξ := by
    intro ξ hξ
    obtain ⟨x, rfl⟩ := hdown ξ hξ
    exact τ.commutes x
  have hexact : act τ.toRingEquiv C / C = D ∧ D ≠ 1 :=
    absoluteKummerContinuousZModCharacterEquiv_action_div_ne_one_of_eigenunit
      E n hmu τ.toRingEquiv hfix α ζ hα hζclass
  obtain ⟨hdiff, hDne⟩ := hexact
  have hζnth : (ζ : E) ^ (n : ℕ) = 1 := by
    change (ζ : E) ^ (p ^ (s + 1)) = 1
    rw [pow_succ', pow_mul, hζroot, one_pow]
  have hD (δ : E ≃ₐ[K] E) : ρ δ D = D := by
    change act δ.toRingEquiv D = D
    exact absoluteContinuousCharacterAction_kummer_root E n hmu ζ hζnth δ.toRingEquiv
  have hcomm (δ : E ≃ₐ[K] E) : Commute (act τ.toRingEquiv) (ρ δ) := by
    change Commute (act τ.toRingEquiv) (act δ.toRingEquiv)
    exact (ValuationTheory.DiscreteValuationField.cyclotomic_compositum_aut_commute
      F K L E p τ δ).map act
  have hcardp : p.Coprime (Fintype.card (E ≃ₐ[K] E)) := by
    simpa only [Nat.card_eq_fintype_card] using
      ValuationTheory.DiscreteValuationField.prime_coprime_cyclotomicGalois_natCard K E p
  have hcop : (Fintype.card (E ≃ₐ[K] E)).Coprime (n : ℕ) :=
    hcardp.symm.pow_right (s + 1)
  have hcopA : (Nat.card A).Coprime (Fintype.card (E ≃ₐ[K] E)) := by
    simpa only [A, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      using hcop.symm
  exact invariant_moved_character_of_coprime
    ρ (act τ.toRingEquiv) C D hcomm hdiff hD hDne hcopA

end ClassFieldTower.Martinet.Shafarevich
