/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.InvariantKernelH1
import ProCGroups.ProP.Presentation.RelationNakayama
import ProCGroups.Cohomology.RelativeNakayama

set_option autoImplicit false
/-!
# Relation rank and invariant kernel H1

For a finite minimal pro-`p` presentation realizing the least relation count, relative Nakayama
characters separate each displayed relator from the closed normal closure of the others.  After
normalization, their invariant degree-one classes map to the coordinate basis.  Consequently,
relator evaluation is surjective and the invariant kernel `H1` dimension equals the displayed
relation count.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC ProCGroups.Presentations

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Every coordinate vector is the relator evaluation of an invariant kernel class when the
displayed relation count is minimal. -/
theorem exists_invariantKernelH1_relatorEval_eq_single_of_relationCard_minimal
    {d n : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (hG : HasFiniteMinimalPresentation p G)
    (P : FiniteProPPresentation p d (n + 1) sourceData G)
    (hP : P.IsMinimal)
    (hcard : minimalRelationRank p G hG = n + 1)
    (i : Fin (n + 1)) :
    ∃ eta : InvariantKernelH1 P,
      invariantKernelH1RelatorEval P eta = Pi.single i 1 := by
  classical
  let R : ClosedSubgroup sourceData.carrier :=
    { toSubgroup := P.quotient.toMonoidHom.ker
      isClosed' := ContinuousMonoidHom.isClosed_ker P.quotient }
  let K : ClosedSubgroup sourceData.carrier :=
    { toSubgroup := closedNormalClosure
        (Set.range (fun j : Fin n ↦ P.relator (i.succAbove j)))
      isClosed' := closedNormalClosure_isClosed _ }
  let _ : R.Normal := by
    change P.quotient.toMonoidHom.ker.Normal
    infer_instance
  let _ : K.Normal := by
    change (closedNormalClosure
      (Set.range (fun j : Fin n ↦ P.relator (i.succAbove j)))).Normal
    exact closedNormalClosure_normal _
  have hKRle : K ≤ R := by
    change closedNormalClosure
      (Set.range (fun j : Fin n ↦ P.relator (i.succAbove j))) ≤
        P.quotient.toMonoidHom.ker
    exact closedNormalClosure_le_closed_normal
      (ContinuousMonoidHom.isClosed_ker P.quotient) (by
        rintro _ ⟨j, rfl⟩
        exact P.relator_mem_kernel (i.succAbove j))
  have hKR : K < R := lt_of_le_of_ne hKRle (by
    intro hEq
    apply relator_not_mem_closedNormalClosure_others_of_relationCard_minimal
      hG P hP hcard i
    change P.relator i ∈ K
    rw [hEq]
    exact P.relator_mem_kernel i)
  have hsource : HasPGroupOpenNormalBasis p sourceData.carrier :=
    sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass
  obtain ⟨chi, hchiNe, hchiKill, hchiInv⟩ :=
    relativeNakayama_character hsource K R hKR
  let theta : InvariantKernelCharacter P := ⟨chi, hchiInv⟩
  let thetaOne : InvariantKernelCharacter P :=
    ⟨1, by intros; rfl⟩
  have hother (j : Fin (n + 1)) (hji : j ≠ i) :
      P.relator j ∈ K := by
    let k : Fin n := (finSuccAboveEquiv i).symm ⟨j, hji⟩
    have hk : i.succAbove k = j := by
      change ((finSuccAboveEquiv i) k).1 = j
      simp [k]
    change P.relator j ∈ closedNormalClosure
      (Set.range (fun k : Fin n ↦ P.relator (i.succAbove k)))
    exact subset_closedNormalClosure _ ⟨k, by simp [hk]⟩
  have hchiRelatorNe :
      chi ⟨P.relator i, P.relator_mem_kernel i⟩ ≠ 1 := by
    intro hchiI
    apply hchiNe
    have htheta : theta = thetaOne :=
      invariantKernelCharacterRelatorEval_injective P (by
        funext j
        by_cases hji : j = i
        · subst j
          exact hchiI
        · change chi ⟨P.relator j, P.relator_mem_kernel j⟩ = 1
          simpa [K, R] using hchiKill ⟨P.relator j, hother j hji⟩)
    exact congrArg Subtype.val htheta
  let eta0 : InvariantKernelH1 P :=
    (invariantKernelH1CharacterEquiv P).symm theta
  let a : ZMod p :=
    chi ⟨P.relator i, P.relator_mem_kernel i⟩ |>.toAdd
  have ha : a ≠ 0 := by
    change chi ⟨P.relator i, P.relator_mem_kernel i⟩ ≠ 1
    exact hchiRelatorNe
  refine ⟨a⁻¹ • eta0, ?_⟩
  rw [map_smul]
  funext j
  by_cases hji : j = i
  · subst j
    change a⁻¹ * a =
      (Pi.single i (1 : ZMod p) : Fin (n + 1) → ZMod p) i
    rw [Pi.single_eq_same]
    exact inv_mul_cancel₀ ha
  · change a⁻¹ *
      (chi ⟨P.relator j, P.relator_mem_kernel j⟩).toAdd =
        (Pi.single i (1 : ZMod p) : Fin (n + 1) → ZMod p) j
    have hj := hchiKill ⟨P.relator j, hother j hji⟩
    change chi ⟨P.relator j, P.relator_mem_kernel j⟩ = 1 at hj
    rw [hj]
    simp [hji]

/-- Relator evaluation is onto for a nonempty finite minimal presentation realizing the least
relation count. -/
theorem invariantKernelH1RelatorEval_surjective_of_relationCard_minimal
    {d n : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (hG : HasFiniteMinimalPresentation p G)
    (P : FiniteProPPresentation p d (n + 1) sourceData G)
    (hP : P.IsMinimal)
    (hcard : minimalRelationRank p G hG = n + 1) :
    Function.Surjective (invariantKernelH1RelatorEval P) := by
  classical
  intro y
  choose eta heta using fun i ↦
    exists_invariantKernelH1_relatorEval_eq_single_of_relationCard_minimal
      hG P hP hcard i
  refine ⟨∑ i, y i • eta i, ?_⟩
  rw [map_sum]
  simp_rw [map_smul, heta]
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Pi.single_eq_of_ne (Ne.symm hij)]
    simp
  · simp

/-- The displayed relation count is at most the dimension of invariant kernel `H1` when the
presentation realizes the least relation count. -/
theorem relationCard_le_finrank_invariantKernelH1_of_minimal
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (hG : HasFiniteMinimalPresentation p G)
    (P : FiniteProPPresentation p d r sourceData G)
    (hP : P.IsMinimal)
    (hcard : minimalRelationRank p G hG = r) :
    r ≤ Module.finrank (ZMod p) (InvariantKernelH1 P) := by
  cases r with
  | zero => exact Nat.zero_le _
  | succ n =>
      let _ : FiniteDimensional (ZMod p) (InvariantKernelH1 P) :=
        invariantKernelH1_finiteDimensional P
      have hle := (invariantKernelH1RelatorEval P).finrank_le_finrank_of_surjective
        (invariantKernelH1RelatorEval_surjective_of_relationCard_minimal
          hG P hP hcard)
      simpa only [Module.finrank_fin_fun] using hle

/-- For a finite minimal presentation realizing the least relation count, the invariant kernel
`H1` dimension is exactly the number of displayed relators. -/
theorem finrank_invariantKernelH1_eq_relationCard_of_minimal
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (hG : HasFiniteMinimalPresentation p G)
    (P : FiniteProPPresentation p d r sourceData G)
    (hP : P.IsMinimal)
    (hcard : minimalRelationRank p G hG = r) :
    Module.finrank (ZMod p) (InvariantKernelH1 P) = r :=
  le_antisymm (finrank_invariantKernelH1_le_relationCard P)
    (relationCard_le_finrank_invariantKernelH1_of_minimal hG P hP hcard)

end

end ClassFieldTower.ProP
