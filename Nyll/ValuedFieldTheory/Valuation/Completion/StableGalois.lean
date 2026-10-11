/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Valuation.Completion.EquivariantMap
import Nyll.ValuedFieldTheory.Valuation.Completion.DVFTensorMap
import Mathlib.FieldTheory.Galois.Basic

/-!
# Completion of a finite Galois extension with invariant valuation

Every relative automorphism preserving the valuation extends to the completion.
If all automorphisms preserve the valuation class, comparison with the canonical
surjective tensor map shows that the degree is unchanged and that every
completion automorphism is obtained in this way.
-/

noncomputable section
namespace ValuationTheory.DiscreteValuationField.DVF
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (base : DVF K) (target : DVF L)
  [base.valuation.HasExtension target.valuation]
local instance stableCompletionAlgebra :
    Algebra base.valuation.Completion target.valuation.Completion :=
  completionAlgebra base target

/-- Extend a relative field automorphism preserving the valuation class. -/
def completionAlgEquiv (τ : Gal(L/K))
    (hτ : target.valuation.IsEquiv (target.valuation.comap τ.toRingEquiv.toRingHom)) :
    Gal(target.valuation.Completion/base.valuation.Completion) where
  __ := completionRingEquiv target target τ.toRingEquiv hτ
  commutes' a := DFunLike.congr_fun
    (completionRingEquiv_comp_completionMap base target target τ hτ) a

/-- The completed automorphism retains its prescribed action on the original field. -/
theorem completionAlgEquiv_algebraMap (τ : Gal(L/K))
    (hτ : target.valuation.IsEquiv (target.valuation.comap τ.toRingEquiv.toRingHom))
    (x : L) :
    completionAlgEquiv base target τ hτ (algebraMap L target.valuation.Completion x) =
      algebraMap L target.valuation.Completion (τ x) :=
  completionRingEquiv_algebraMap target target τ.toRingEquiv hτ x

/-- Distinct original automorphisms induce distinct completed automorphisms. -/
theorem completionAlgEquiv_injective
    (hstable : ∀ τ : Gal(L/K),
      target.valuation.IsEquiv (target.valuation.comap τ.toRingEquiv.toRingHom)) :
    Function.Injective (fun τ => completionAlgEquiv base target τ (hstable τ)) := by
  intro τ σ h
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L target.valuation.Completion).injective
  exact (completionAlgEquiv_algebraMap base target τ (hstable τ) x).symm.trans
    ((DFunLike.congr_fun h (algebraMap L target.valuation.Completion x)).trans
      (completionAlgEquiv_algebraMap base target σ (hstable σ) x))

/-- The degree cannot increase on completing an extension of discrete valued fields. -/
theorem finrank_completion_le [FiniteDimensional K L] :
    Module.finrank base.valuation.Completion target.valuation.Completion ≤
      Module.finrank K L := by
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (completionTensorHom base target).toLinearMap)
    (completionTensorHom_surjective base target)
  exact h.trans_eq Module.finrank_baseChange

/-- An invariant prolongation preserves the degree of a finite Galois extension. -/
theorem finrank_completion_eq_of_galois_stable [FiniteDimensional K L] [IsGalois K L]
    (hstable : ∀ τ : Gal(L/K),
      target.valuation.IsEquiv (target.valuation.comap τ.toRingEquiv.toRingHom)) :
    Module.finrank base.valuation.Completion target.valuation.Completion =
      Module.finrank K L := by
  have : FiniteDimensional base.valuation.Completion target.valuation.Completion :=
    completion_finiteDimensional base target
  apply le_antisymm (finrank_completion_le base target)
  calc
    Module.finrank K L = Nat.card Gal(L/K) := (IsGalois.card_aut_eq_finrank K L).symm
    _ ≤ Nat.card Gal(target.valuation.Completion/base.valuation.Completion) :=
      Nat.card_le_card_of_injective _ (completionAlgEquiv_injective base target hstable)
    _ ≤ Module.finrank base.valuation.Completion target.valuation.Completion := by
      rw [← Fintype.card_eq_nat_card]
      exact AlgEquiv.card_le

/-- Completing at an invariant prolongation preserves the Galois property. -/
theorem completion_isGalois_of_stable [FiniteDimensional K L] [IsGalois K L]
    (hstable : ∀ τ : Gal(L/K),
      target.valuation.IsEquiv (target.valuation.comap τ.toRingEquiv.toRingHom)) :
    IsGalois base.valuation.Completion target.valuation.Completion := by
  have : FiniteDimensional base.valuation.Completion target.valuation.Completion :=
    completion_finiteDimensional base target
  apply IsGalois.of_card_aut_eq_finrank
  apply le_antisymm
  · rw [← Fintype.card_eq_nat_card]
    exact AlgEquiv.card_le
  · rw [finrank_completion_eq_of_galois_stable base target hstable,
      ← IsGalois.card_aut_eq_finrank K L]
    exact Nat.card_le_card_of_injective _ (completionAlgEquiv_injective base target hstable)

/-- Every completed automorphism extends an original automorphism when the
prolongation is invariant under the finite Galois group. -/
theorem completionAlgEquiv_surjective [FiniteDimensional K L] [IsGalois K L]
    (hstable : ∀ τ : Gal(L/K),
      target.valuation.IsEquiv (target.valuation.comap τ.toRingEquiv.toRingHom)) :
    Function.Surjective (fun τ => completionAlgEquiv base target τ (hstable τ)) := by
  have : FiniteDimensional base.valuation.Completion target.valuation.Completion :=
    completion_finiteDimensional base target
  have : IsGalois base.valuation.Completion target.valuation.Completion :=
    completion_isGalois_of_stable base target hstable
  exact ((completionAlgEquiv_injective base target hstable).bijective_of_nat_card_le
    (by rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
      finrank_completion_eq_of_galois_stable base target hstable])).2

end ValuationTheory.DiscreteValuationField.DVF
