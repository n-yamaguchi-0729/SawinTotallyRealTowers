/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutEquiv
import Mathlib.Algebra.CharP.Reduced
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The Krull topology on algebraic and separable closures

Every element of the algebraic closure has an exponential-characteristic
power in the separable closure. Stabilizers of those powers form finite
intersections of open subgroups. Injectivity of Frobenius then controls the
action on a finite linear basis, proving continuity of inverse restriction.
-/

noncomputable section

namespace ValuationTheory.Completion

open scoped Topology

variable (K : Type*) [Field K]

/-- Extending automorphisms from the separable closure to the algebraic
closure is continuous in every characteristic. -/
theorem continuous_separableClosureAutEquiv_symm :
    Continuous (separableClosureAutEquiv K).symm := by
  classical
  apply continuous_of_tendsto_nhds_one (separableClosureAutEquiv K).symm
  rw [Filter.Tendsto]
  intro U hU
  obtain ⟨F, hF, hFU⟩ :=
    (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) U).mp hU
  let b : Module.Basis (Fin (Module.finrank K F)) K F := Module.finBasis K F
  let q : ℕ := ringExpChar (SeparableClosure K)
  have : ExpChar (AlgebraicClosure K) q :=
    expChar_of_injective_ringHom
      (algebraMap (SeparableClosure K) (AlgebraicClosure K)).injective q
  have hpowers : ∀ j : Fin (Module.finrank K F),
      ∃ n : ℕ, ∃ y : SeparableClosure K,
        (y : AlgebraicClosure K) = (b j : AlgebraicClosure K) ^ (q ^ n) := by
    intro j
    exact IsPurelyInseparable.pow_mem (SeparableClosure K) q
      (b j : AlgebraicClosure K)
  choose n y hy using hpowers
  have hH : (⋂ j, (MulAction.stabilizer Gal(SeparableClosure K/K) (y j) :
      Set Gal(SeparableClosure K/K))) ∈ 𝓝 1 :=
    Filter.iInter_mem.mpr fun j =>
      (stabilizer_isOpen_of_isIntegral (K := K) (y j)).mem_nhds (Subgroup.one_mem _)
  apply Filter.mem_of_superset hH
  intro τ hτ
  apply hFU
  have hfixed : ∀ j : Fin (Module.finrank K F),
      (separableClosureAutEquiv K).symm τ (b j : AlgebraicClosure K) =
        (b j : AlgebraicClosure K) := by
    intro j
    apply iterateFrobenius_inj (AlgebraicClosure K) q (n j)
    change ((separableClosureAutEquiv K).symm τ (b j : AlgebraicClosure K)) ^
      (q ^ n j) = (b j : AlgebraicClosure K) ^ (q ^ n j)
    rw [← map_pow, ← hy j, ← separableClosureAutEquiv_apply, MulEquiv.apply_symm_apply]
    exact congrArg (fun z : SeparableClosure K => (z : AlgebraicClosure K))
      (MulAction.mem_stabilizer_iff.mp (Set.mem_iInter.mp hτ j))
  have hlin : (((separableClosureAutEquiv K).symm τ).toAlgHom.comp F.val).toLinearMap =
      F.val.toLinearMap := b.ext hfixed
  apply (IntermediateField.mem_fixingSubgroup_iff F
    ((separableClosureAutEquiv K).symm τ)).mpr
  intro x hx
  exact congrArg (fun f : F →ₗ[K] AlgebraicClosure K => f ⟨x, hx⟩) hlin

/-- Restriction identifies the Krull topological groups of the algebraic
and separable closures over an arbitrary field. -/
def separableClosureAutContinuousEquiv :
    Gal(AlgebraicClosure K/K) ≃ₜ* Gal(SeparableClosure K/K) where
  toMulEquiv := separableClosureAutEquiv K
  continuous_toFun := continuous_separableClosureAutEquiv K
  continuous_invFun := continuous_separableClosureAutEquiv_symm K

/-- The topological group isomorphism retains restriction on field elements. -/
@[simp] theorem separableClosureAutContinuousEquiv_apply
    (σ : Gal(AlgebraicClosure K/K)) (s : SeparableClosure K) :
    (separableClosureAutContinuousEquiv K σ s : AlgebraicClosure K) =
      σ (s : AlgebraicClosure K) :=
  separableClosureAutEquiv_apply K σ s

/-- The algebraic-closure Galois group is compact even when the base field is
imperfect: restriction is a homeomorphism onto the separable-closure group. -/
instance algebraicClosureAut_compactSpace : CompactSpace Gal(AlgebraicClosure K/K) :=
  (separableClosureAutContinuousEquiv K).symm.toHomeomorph.compactSpace

end ValuationTheory.Completion
