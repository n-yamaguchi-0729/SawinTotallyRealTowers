/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2CocycleExtension
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.ProfiniteIntegerFree
import ProCGroups.ProC.InverseLimits.FiniteQuotients
import ProCGroups.ProC.Subgroups.Closed

set_option autoImplicit false
/-!
# Degree-two cohomology of the profinite integers

The rank-one free-profinite property of `ZHat` splits the compact profinite central extension
attached to every continuous homogeneous two-cocycle.  The section supplies an explicit
degree-one primitive, so continuous degree-two cohomology with trivial lifted `ZMod p`
coefficients vanishes.
-/

open scoped Topology

namespace ClassFieldTower.Cohomology.ProfiniteInteger

open CategoryTheory TopRep ContRepresentation
open ProCGroups ProCGroups.ProC
open ClassFieldTower.ProP
open ClassFieldTower.ProP.FreeProPH2Cocycle

noncomputable section

variable {p : ℕ} [Fact p.Prime]

private theorem exists_continuous_section_of_surjective
    {E : Type} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
    [CompactSpace E] [T2Space E] [TotallyDisconnectedSpace E]
    (hE : HasOpenNormalBasisInClass FiniteGroupClass.allFinite E)
    (q : E →ₜ* ClassFormation.ZHatMul) (hq : Function.Surjective q) :
    ∃ s : ClassFormation.ZHatMul →ₜ* E,
      q.comp s = ContinuousMonoidHom.id ClassFormation.ZHatMul := by
  classical
  let hfree := isFreeProfinite
  let φ : PUnit → E := fun _ => Function.surjInv hq generator
  let s : ClassFormation.ZHatMul →ₜ* E :=
    hfree.liftHom hE φ continuous_const
  refine ⟨s, ?_⟩
  apply ContinuousMonoidHom.toMonoidHom_injective
  apply hfree.hom_ext hfree.hasOpenNormalBasisInClass
    (q.comp s).continuous_toFun continuous_id
  intro x
  cases x
  change q (s generator) = generator
  rw [show s generator = φ PUnit.unit by
    exact hfree.liftHom_apply hE φ continuous_const PUnit.unit]
  exact Function.surjInv_eq hq generator

private theorem normalizedCocycle_is_continuous_coboundary
    (z : trivialZModPCocyclesLifted p ClassFormation.ZHatMul 2) :
    ∃ b : C(ClassFormation.ZHatMul, A p), ∀ g h,
      b (g * h) = b g + b h + normalizedCocycle z g h := by
  let F := ClassFormation.ZHatMul
  let E := H2CocycleExtension z
  let eh : E ≃ₜ A p × F := H2CocycleExtension.toProdHomeomorph z
  let q : E →ₜ* F := H2CocycleExtension.projection z
  have hq : Function.Surjective q := H2CocycleExtension.projection_surjective z
  let K : Subgroup E := q.ker
  let _ : Finite K := by
    dsimp [K, q]
    exact H2CocycleExtension.instFiniteKernel z
  have hK : HasOpenNormalBasisInClass FiniteGroupClass.allFinite K := by
    let _ : DiscreteTopology K := by infer_instance
    exact HasOpenNormalBasisInClass.of_finite_discrete
      FiniteGroupClass.allFinite_quotientClosed (show Finite K from inferInstance)
  have hKclosed : IsClosed (K : Set E) := by
    simpa [K] using ContinuousMonoidHom.isClosed_ker q
  let _ : IsClosed (K : Set E) := hKclosed
  let _ : CompactSpace q.range := isCompact_iff_compactSpace.mp <| by
    simpa using isCompact_range q.continuous_toFun
  let er : q.range ≃ₜ* F :=
    ContinuousMulEquiv.ofBijectiveCompactToT2 (Subgroup.subtype q.range)
      continuous_subtype_val
      ⟨Subtype.coe_injective, by
        intro g
        rcases hq g with ⟨x, rfl⟩
        exact ⟨⟨q x, ⟨x, rfl⟩⟩, rfl⟩⟩
  let eqRange : (E ⧸ K) ≃ₜ* q.range := by
    simpa [K] using ContinuousMonoidHom.quotientKerContinuousMulEquivRange q
  let eqF : (E ⧸ K) ≃ₜ* F := eqRange.trans er
  have hQ : HasOpenNormalBasisInClass FiniteGroupClass.allFinite (E ⧸ K) :=
    HasOpenNormalBasisInClass.ofContinuousMulEquiv
      isFreeProfinite.hasOpenNormalBasisInClass eqF.symm
  have hE : HasOpenNormalBasisInClass FiniteGroupClass.allFinite E :=
    HasOpenNormalBasisInClass.extension
      FiniteGroupClass.allFinite_isomClosed
      FiniteGroupClass.allFinite_quotientClosed
      FiniteGroupClass.allFinite_extensionClosed K hKclosed hK hQ
  obtain ⟨s, hs⟩ := exists_continuous_section_of_surjective hE q hq
  let b : C(F, A p) :=
    { toFun := fun g => (s g).left
      continuous_toFun :=
        (continuous_fst.comp eh.continuous).comp s.continuous_toFun }
  refine ⟨b, ?_⟩
  intro g h
  have hsg : (s g).right = g := by
    have h := congrArg (fun f : F →ₜ* F => f g) hs
    exact h
  have hsh : (s h).right = h := by
    have h := congrArg (fun f : F →ₜ* F => f h) hs
    exact h
  have hmul := congrArg H2CocycleExtension.left (s.map_mul g h)
  change b (g * h) = b g + b h + normalizedCocycle z g h
  change (s (g * h)).left =
    (s g).left + (s h).left + normalizedCocycle z g h
  change (s (g * h)).left =
    (s g).left + (s h).left + normalizedCocycle z (s g).right (s h).right at hmul
  simpa [hsg, hsh] using hmul

theorem degree_two_π_apply_eq_zero
    (z : trivialZModPCocyclesLifted p ClassFormation.ZHatMul 2) :
    ContinuousCohomology.π (trivialZModPLifted p ClassFormation.ZHatMul) 2 z = 0 := by
  obtain ⟨b, hb⟩ := normalizedCocycle_is_continuous_coboundary z
  let K := trivialZModPCochainsLifted p ClassFormation.ZHatMul
  let c : K.X 1 := homogeneousPrimitive z b
  have hc : (K.d 1 2).hom c = (K.iCycles 2).hom z :=
    homogeneousPrimitive_boundary z b hb
  have hzc : (K.toCycles 1 2).hom c = z := by
    apply topModule_mono_injective_lifted (K.iCycles 2)
    calc
      (K.iCycles 2).hom ((K.toCycles 1 2).hom c) = (K.d 1 2).hom c := by
        have hcomp := ConcreteCategory.congr_hom (K.toCycles_i 1 2) c
        change (K.iCycles 2).hom ((K.toCycles 1 2).hom c) = (K.d 1 2).hom c at hcomp
        exact hcomp
      _ = (K.iCycles 2).hom z := hc
  rw [← hzc]
  have hzero := ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ 1 2) c
  exact hzero

theorem degree_two_π_eq_zero :
    ContinuousCohomology.π (trivialZModPLifted p ClassFormation.ZHatMul) 2 = 0 := by
  ext z
  exact degree_two_π_apply_eq_zero z

/-- Continuous `H²(ZHat, ZMod p)` with trivial lifted coefficients vanishes. -/
theorem degree_two_subsingleton :
    Subsingleton (continuousCohomologyZModPLifted p ClassFormation.ZHatMul 2) := by
  let H := continuousCohomologyZModPLifted p ClassFormation.ZHatMul 2
  let π := ContinuousCohomology.π
    (trivialZModPLifted p ClassFormation.ZHatMul) 2
  have hπ : π = 0 := degree_two_π_eq_zero
  have hid : 𝟙 H = 0 := by
    rw [← cancel_epi π]
    rw [hπ]
    simp
  constructor
  intro x y
  have hx : x = 0 := by
    have h := ConcreteCategory.congr_hom hid x
    simpa [H] using h
  have hy : y = 0 := by
    have h := ConcreteCategory.congr_hom hid y
    simpa [H] using h
  exact hx.trans hy.symm

end

end ClassFieldTower.Cohomology.ProfiniteInteger
