import GaloisCohomology.ProP.FiniteStageTransgressionKernel
import GaloisCohomology.ProP.FiniteStageTransgressionLinear
import ProCGroups.Cohomology.InvariantCharacterFiniteFamily
import GaloisCohomology.ProP.PresentationQuotientEquiv
import GaloisCohomology.ProP.RelationRankH1
import Mathlib.LinearAlgebra.Dimension.Finite

set_option autoImplicit false
/-!
# Relation rank as a lower bound for presentation target H²

For a minimal pro-`p` presentation realizing the least relation count, normalized invariant
kernel characters descend to a common finite stage.  Their inflated transgression classes are
linearly independent: a vanishing combination extends continuously to the free source, where
minimality forces its restriction to the presentation kernel to vanish.  The presentation
quotient equivalence then transports the resulting dimension bound to the target group.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC ProCGroups.Presentations
open ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

local instance lowerBoundStageTargetTopology
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    TopologicalSpace ((F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U) := ⊥

local instance lowerBoundStageTargetDiscrete
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    DiscreteTopology ((F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U) :=
  discreteTopology_bot _

/-- A nonempty relation family realizing the least relation count gives independent target H² classes. -/
theorem presentation_relationCard_succ_le_finrank_h2
    {d n : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (hG : HasFiniteMinimalPresentation p G)
    (P : FiniteProPPresentation p d (n + 1) sourceData G)
    (hP : P.IsMinimal)
    (hcard : minimalRelationRank p G hG = n + 1)
    [FiniteDimensional (ZMod p)
      (continuousCohomologyZModPLifted p G 2)] :
    n + 1 ≤ Module.finrank (ZMod p)
      (continuousCohomologyZModPLifted p G 2) := by
  classical
  choose eta heta using fun i ↦
    exists_invariantKernelH1_relatorEval_eq_single_of_relationCard_minimal
      hG P hP hcard i
  let R : ClosedSubgroup sourceData.carrier :=
    { toSubgroup := P.quotient.toMonoidHom.ker
      isClosed' := ContinuousMonoidHom.isClosed_ker P.quotient }
  let _ : R.Normal := by
    change P.quotient.toMonoidHom.ker.Normal
    infer_instance
  let chi : Fin (n + 1) → R →ₜ* Multiplicative (ZMod p) := fun i ↦
    characterOfH1 (eta i).1
  have hchiInv : ∀ (i : Fin (n + 1)) (f : sourceData.carrier) (r : R),
      chi i (MulAut.conjNormal f r) = chi i r := by
    intro i f r
    exact congrArg Multiplicative.ofAdd ((eta i).2 f r)
  have hsource : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p)
      sourceData.carrier :=
    sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass
  obtain ⟨U, chibar, hpull, hchibarInv, hcomb⟩ :=
    exists_finiteStage_invariant_character_family hsource R chi hchiInv
  let v : Fin (n + 1) →
      InvariantFiniteCharacter (p := p) (finiteStageImage R U) := fun i ↦
    ⟨Additive.ofMul (chibar i), hchibarInv i⟩
  have hv (i : Fin (n + 1)) :
      InvariantFiniteCharacter.toMonoidHom (finiteStageImage R U) (v i) =
        chibar i := rfl
  let w : Fin (n + 1) → continuousCohomologyZModPLifted p
      (sourceData.carrier ⧸ (R : Subgroup sourceData.carrier)) 2 := fun i ↦
    inflatedFiniteTransgressionLinearMap R U (v i)
  have hw : LinearIndependent (ZMod p) w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    let etaSum : InvariantKernelH1 P := ∑ i, a i • eta i
    let chiSum : R →ₜ* Multiplicative (ZMod p) :=
      characterOfH1 etaSum.1
    let vSum : InvariantFiniteCharacter (p := p) (finiteStageImage R U) :=
      ∑ i, a i • v i
    have hzero : inflatedFiniteTransgressionClass R U
        (InvariantFiniteCharacter.toMonoidHom (finiteStageImage R U) vSum)
        (InvariantFiniteCharacter.isInvariant (finiteStageImage R U) vSum) = 0 := by
      rw [← inflatedFiniteTransgressionLinearMap_apply]
      simpa only [vSum, map_sum, map_smul, w] using ha
    have hpullSum :
        (InvariantFiniteCharacter.toMonoidHom (finiteStageImage R U) vSum).comp
            (finiteStageImageMap R U) = chiSum.toMonoidHom := by
      ext r
      let evStage :
          InvariantFiniteCharacter (p := p) (finiteStageImage R U) →+ ZMod p :=
        { toFun := fun theta ↦
            (InvariantFiniteCharacter.toMonoidHom
              (finiteStageImage R U) theta (finiteStageImageMap R U r)).toAdd
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      let evKernel : InvariantKernelH1 P →+ ZMod p :=
        { toFun := fun theta ↦ theta.1 (Additive.ofMul r)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      let evStageLinear :
          InvariantFiniteCharacter (p := p) (finiteStageImage R U) →ₗ[ZMod p] ZMod p :=
        evStage.toZModLinearMap p
      let evKernelLinear : InvariantKernelH1 P →ₗ[ZMod p] ZMod p :=
        evKernel.toZModLinearMap p
      change evStageLinear vSum = evKernelLinear etaSum
      rw [show vSum = ∑ i, a i • v i by rfl,
        show etaSum = ∑ i, a i • eta i by rfl, map_sum, map_sum]
      simp_rw [map_smul]
      apply Finset.sum_congr rfl
      intro i hi
      change a i * (chibar i (finiteStageImageMap R U r)).toAdd =
        a i * (chi i r).toAdd
      have hir := DFunLike.congr_fun (hpull i) r
      change chibar i (finiteStageImageMap R U r) = chi i r at hir
      rw [hir]
    have hchiSumInv : ∀ (f : sourceData.carrier) (r : R),
        chiSum (MulAut.conjNormal f r) = chiSum r := by
      intro f r
      exact congrArg Multiplicative.ofAdd (etaSum.2 f r)
    obtain ⟨psi, hpsi⟩ :=
      exists_continuous_extension_of_inflatedFiniteTransgressionClass_eq_zero
        R U
        (InvariantFiniteCharacter.toMonoidHom (finiteStageImage R U) vSum)
        (InvariantFiniteCharacter.isInvariant (finiteStageImage R U) vSum)
        chiSum hchiSumInv hpullSum hzero
    have hetaSumZero : etaSum = 0 := by
      apply Subtype.ext
      ext r
      have hmin := P.kernel_h1_eq_zero hP (h1OfCharacter psi)
        (Additive.toMul r)
      have hres := DFunLike.congr_fun hpsi (Additive.toMul r)
      change psi ((Additive.toMul r : P.quotient.toMonoidHom.ker) :
        sourceData.carrier) = chiSum (Additive.toMul r) at hres
      change etaSum.1 r = 0
      change (psi ((Additive.toMul r : P.quotient.toMonoidHom.ker) :
        sourceData.carrier)).toAdd = 0 at hmin
      rw [hres] at hmin
      exact hmin
    have hevalSum : invariantKernelH1RelatorEval P etaSum = a := by
      dsimp only [etaSum]
      rw [map_sum]
      simp_rw [map_smul, heta]
      apply funext
      intro k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · simp
      · intro i hi hik
        rw [Pi.single_eq_of_ne (Ne.symm hik)]
        simp
      · simp
    have hevalZero := congrArg (invariantKernelH1RelatorEval P) hetaSumZero
    rw [map_zero] at hevalZero
    have haZero : a = 0 := hevalSum.symm.trans hevalZero
    exact congrFun haZero j
  clear hcomb
  let e := continuousCohomologyZModPLiftedLinearEquiv (p := p)
    (P.quotientKerContinuousMulEquiv) 2
  have hwTarget : LinearIndependent (ZMod p) (fun i ↦ e.symm (w i)) :=
    hw.map' e.symm.toLinearMap (LinearMap.ker_eq_bot.mpr e.symm.injective)
  simpa only [Fintype.card_fin] using hwTarget.fintype_card_le_finrank

/-- A finite minimal presentation realizing the least relation count supplies that many
linearly independent degree-two continuous cohomology classes. -/
theorem presentation_relationCard_le_finrank_h2
    {d r : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (hG : HasFiniteMinimalPresentation p G)
    (P : FiniteProPPresentation p d r sourceData G)
    (hP : P.IsMinimal)
    (hcard : minimalRelationRank p G hG = r)
    [FiniteDimensional (ZMod p)
      (continuousCohomologyZModPLifted p G 2)] :
    r ≤ Module.finrank (ZMod p)
      (continuousCohomologyZModPLifted p G 2) := by
  cases r with
  | zero => exact Nat.zero_le _
  | succ n =>
      exact presentation_relationCard_succ_le_finrank_h2 hG P hP hcard

end

end ClassFieldTower.ProP
