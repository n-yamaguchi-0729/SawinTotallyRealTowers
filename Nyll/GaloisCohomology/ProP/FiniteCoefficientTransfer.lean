/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.FiniteIndexTransfer
import Nyll.GaloisCohomology.ProP.TransferRestriction
import Mathlib.GroupTheory.OrderOfElement

/-!
# Coprime-index transfer with arbitrary finite abelian coefficients

Bézout inversion of the index power normalizes transfer. This works for every
finite abelian coefficient group, including universe-lifted coefficient groups,
and preserves continuity. No choice of cyclic coordinates is needed.
-/

noncomputable section

namespace ClassFieldTower.Cohomology

variable {G B : Type*} [Group G] [CommGroup B]

/-- Restriction is injective when the subgroup index is coprime to the
coefficient-group order. -/
theorem finiteCharacterRestriction_injective_of_coprime
    (H : Subgroup G) [H.Normal]
    (hcop : (Nat.card B).Coprime H.index) :
    Function.Injective (fun φ : G →* B => φ.comp H.subtype) := by
  intro φ ψ hres
  apply MonoidHom.ext
  intro g
  have hpow : g ^ H.index ∈ H := by
    apply (QuotientGroup.eq_one_iff (g ^ H.index)).mp
    change (QuotientGroup.mk' H) (g ^ H.index) = 1
    rw [map_pow, Subgroup.index_eq_card]
    exact pow_card_eq_one'
  apply (powCoprime hcop).injective
  have heq := DFunLike.congr_fun hres (⟨g ^ H.index, hpow⟩ : H)
  change φ (g ^ H.index) = ψ (g ^ H.index) at heq
  exact (map_pow φ g H.index).symm.trans
    (heq.trans (map_pow ψ g H.index))

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace B] [IsTopologicalGroup B] [DiscreteTopology B]

/-- Continuous transfer followed by the Bézout inverse of the index power. -/
def finiteCoefficientTransfer
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (φ : H →ₜ* B) : G →ₜ* B where
  toFun g := openSubgroupTransfer H φ g ^ (Nat.card B).gcdB H.toSubgroup.index
  map_one' := by
    rw [map_one, one_zpow]
  map_mul' g h := by
    rw [map_mul, mul_zpow]
  continuous_toFun :=
    (continuous_of_discreteTopology : Continuous
      (fun b : B => b ^ (Nat.card B).gcdB H.toSubgroup.index)).comp
        (openSubgroupTransfer H φ).continuous

/-- Normalized transfer extends an invariant character across a coprime index. -/
theorem finiteCoefficientTransfer_subtype
    (H : OpenSubgroup G) [H.toSubgroup.Normal] [H.toSubgroup.FiniteIndex]
    (hcop : (Nat.card B).Coprime H.toSubgroup.index)
    (φ : H →ₜ* B)
    (hinv : ∀ (g : G) (h : H), φ (MulAut.conjNormal g h) = φ h)
    (h : H) :
    finiteCoefficientTransfer H φ (h : G) = φ h := by
  change openSubgroupTransfer H φ (h : G) ^
    (Nat.card B).gcdB H.toSubgroup.index = φ h
  have ht : openSubgroupTransfer H φ (h : G) = φ h ^ H.toSubgroup.index :=
    transfer_subtype_eq_pow_of_conjInvariant H.toSubgroup φ.toMonoidHom hinv h
  rw [ht]
  exact (powCoprime hcop).left_inv (φ h)

end ClassFieldTower.Cohomology
