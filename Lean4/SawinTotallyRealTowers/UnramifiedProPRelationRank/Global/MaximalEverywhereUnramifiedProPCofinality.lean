/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.MaximalEverywhereUnramifiedProPFiniteSupport

set_option autoImplicit false
/-!
# Cofinality of finite everywhere-unramified pro-p extensions

For odd `p`, the bundled finite extensions are directed under binary
compositum.  Compactness therefore upgrades finite support in the maximal
compositum to containment in one bundled extension.
-/

open scoped NumberField

noncomputable section

universe u

namespace ClassFieldTower.Martinet

private theorem finite_iSup_extension_le_extension
    {F : Type u} [Field F] [NumberField F]
    {p : ℕ} [Fact p.Prime]
    (hpOdd : Odd p)
    (s : Finset (FiniteEverywhereUnramifiedProPExtension F p)) :
    ∃ C : FiniteEverywhereUnramifiedProPExtension F p,
      (⨆ E ∈ s, E.field) ≤ C.field := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨FiniteEverywhereUnramifiedProPExtension.bot, by simp⟩
  | @insert E s hE ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨FiniteEverywhereUnramifiedProPExtension.sup hpOdd E C, ?_⟩
      change (⨆ K ∈ insert E s, K.field) ≤ E.field ⊔ C.field
      simpa [hE] using sup_le_sup le_rfl hC

/-- Every finite-dimensional intermediate field below the maximal compositum
is contained in one bundled finite everywhere-unramified pro-p extension. -/
theorem finiteDimensional_le_maximalEverywhereUnramifiedProP_exists_extension
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact p.Prime]
    (hpOdd : Odd p)
    (L : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F L]
    (hL : L ≤ maximalEverywhereUnramifiedProP F p) :
    ∃ C : FiniteEverywhereUnramifiedProPExtension F p, L ≤ C.field := by
  obtain ⟨s, hs⟩ :=
    finiteDimensional_le_maximalEverywhereUnramifiedProP_exists_finset
      F p L hL
  obtain ⟨C, hC⟩ := finite_iSup_extension_le_extension hpOdd s
  exact ⟨C, hs.trans hC⟩

/-- Every element of the maximal compositum lies in one bundled finite
everywhere-unramified pro-p extension. -/
theorem mem_maximalEverywhereUnramifiedProP_exists_extension
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact p.Prime]
    (hpOdd : Odd p)
    {x : AlgebraicClosure F}
    (hx : x ∈ maximalEverywhereUnramifiedProP F p) :
    ∃ C : FiniteEverywhereUnramifiedProPExtension F p, x ∈ C.field := by
  let L : IntermediateField F (AlgebraicClosure F) :=
    IntermediateField.adjoin F {x}
  let _ : FiniteDimensional F L :=
    IntermediateField.finiteDimensional_adjoin
      (fun y _ ↦ (Algebra.IsAlgebraic.isAlgebraic y).isIntegral)
  have hL : L ≤ maximalEverywhereUnramifiedProP F p := by
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
  obtain ⟨C, hC⟩ :=
    finiteDimensional_le_maximalEverywhereUnramifiedProP_exists_extension
      F p hpOdd L hL
  exact ⟨C, hC (IntermediateField.mem_adjoin_simple_self F x)⟩

/-- A finite Galois intermediate field below the maximal compositum is
everywhere unramified over the base field. -/
theorem isEverywhereUnramified_of_le_maximalEverywhereUnramifiedProP
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact p.Prime]
    (hpOdd : Odd p)
    (L : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F L] [IsGalois F L] [NumberField L]
    (hL : L ≤ maximalEverywhereUnramifiedProP F p) :
    IsEverywhereUnramified F L := by
  obtain ⟨C, hLC⟩ :=
    finiteDimensional_le_maximalEverywhereUnramifiedProP_exists_extension
      F p hpOdd L hL
  let _ : Algebra L C.field :=
    (IntermediateField.inclusion hLC).toRingHom.toAlgebra
  let _ : IsScalarTower F L C.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact IsEverywhereUnramified.bot C.everywhereUnramified

end ClassFieldTower.Martinet
