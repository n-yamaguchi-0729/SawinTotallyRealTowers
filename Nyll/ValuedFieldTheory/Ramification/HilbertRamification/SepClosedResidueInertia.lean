/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianResidueAction
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteOrderValuation
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteRamificationPrimary
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.CharacterMap
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Inertia over a separably closed residue field

The algebraic residue extension is purely inseparable, so its Galois action
is trivial. On each finite Galois layer the inertia character sends the
commutator to one, placing it in the actual wild ramification group.
-/

open scoped commutatorElement Topology

namespace RamificationTheory.HilbertRamification.ValuationSubring
noncomputable section
universe u v w x

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  {Γ : Type w} {Δ : Type x}
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
  (v : Valuation K Γ) (w : Valuation L Δ) [v.HasExtension w]
  [IsGalois K L]
  [HenselianRing v.valuationSubring (IsLocalRing.maximalIdeal v.valuationSubring)]
  [IsSepClosed (IsLocalRing.ResidueField v.valuationSubring)]

/-- Over a separably closed residue field every Galois automorphism is inertia. -/
def henselianGalToInertia : Gal(L/K) →* inertiaGroup K w.valuationSubring where
  toFun σ := ⟨henselianGalToDecomposition v w σ, by
    have : Algebra.IsIntegral (IsLocalRing.ResidueField v.valuationSubring)
        (IsLocalRing.ResidueField w.valuationSubring) :=
      henselianResidueExtension_isIntegral v w
    have he := Subsingleton.elim (henselianResidueAction v w σ).toAlgHom
      (AlgHom.id (IsLocalRing.ResidueField v.valuationSubring)
        (IsLocalRing.ResidueField w.valuationSubring))
    apply RingEquiv.ext
    intro a
    exact congrArg (fun f => f a) he⟩
  map_one' := rfl
  map_mul' _ _ := rfl

include v in
/-- The commutator of finite Galois inertia lies in wild inertia. -/
theorem commutator_isPGroup_of_henselian_separablyClosedResidue
    [FiniteDimensional K L] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField w.valuationSubring) p] :
    IsPGroup p (commutator Gal(L/K)) := by
  let A := w.valuationSubring
  let ι := henselianGalToInertia v w
  have htop := valueTrivialInertiaGroup_eq_top_of_finite K A
  let j : Gal(L/K) →* valueTrivialInertiaGroup K A :=
    { toFun := fun σ => ⟨ι σ, htop.symm ▸ Subgroup.mem_top (ι σ)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let χ := (valueTrivialInertiaCharacterHom K A).comp j
  have hker : commutator Gal(L/K) ≤ χ.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro a ⟨σ, τ, rfl⟩
    change χ ⁅σ, τ⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply MonoidHom.ext
    intro a
    exact mul_comm _ _
  let f : commutator Gal(L/K) →* ramificationGroup K A :=
    { toFun := fun σ => ⟨ι σ,
        (valueTrivialInertiaCharacterHom_mem_ker_iff K A (j σ)).mp (hker σ.property)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  apply (ramificationGroup_isPGroup_of_residueChar K A p).of_injective f
  intro σ τ h
  apply Subtype.ext
  exact congrArg (fun a : ramificationGroup K A =>
    inertiaGroupToAut (K := K) A (a : inertiaGroup K A)) h

end
end RamificationTheory.HilbertRamification.ValuationSubring
