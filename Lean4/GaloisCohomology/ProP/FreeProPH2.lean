import GaloisCohomology.ProP.H2CocycleExtension
import ProCGroups.Cohomology.FreeProPProjective
import ProCGroups.ProC.InverseLimits.FiniteQuotients
import ProCGroups.ProC.Subgroups.Closed

set_option autoImplicit false
/-!
# Degree-two cohomology of a free pro-p group

This file proves that continuous degree-two cohomology with universe-lifted trivial
`ZMod p` coefficients vanishes for the finite-basis free pro-`p` source used by a
presentation.  The proof is explicit: a homogeneous cocycle defines a twisted compact
pro-`p` extension, projectivity supplies a continuous section, and the section gives a
homogeneous degree-one primitive.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CategoryTheory TopRep ContRepresentation
open ProCGroups ProCGroups.ProC
open FreeProPH2Cocycle

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

private theorem normalizedCocycle_is_continuous_coboundary
    {d : ℕ}
    (sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p))
    (hbasis : Cardinal.mk sourceData.basis = d)
    (z : Cohomology.trivialZModPCocyclesLifted p sourceData.carrier 2) :
    ∃ b : C(sourceData.carrier, A p), ∀ g h,
      b (g * h) = b g + b h + normalizedCocycle z g h := by
  let F := sourceData.carrier
  let E := H2CocycleExtension z
  let eh : E ≃ₜ A p × F := H2CocycleExtension.toProdHomeomorph z
  let q : E →ₜ* F := H2CocycleExtension.projection z
  have hq : Function.Surjective q := H2CocycleExtension.projection_surjective z
  let K : Subgroup E := q.ker
  let _ : Finite K := by
    dsimp [K, q]
    exact H2CocycleExtension.instFiniteKernel z
  have hKP : IsPGroup p K := by
    dsimp [K, q]
    exact H2CocycleExtension.kernel_isPGroup z
  let _ : DiscreteTopology K := by infer_instance
  have hK : HasPGroupOpenNormalBasis p K :=
    HasOpenNormalBasisInClass.of_finite_discrete
      (FiniteGroupClass.pGroup_formation p).quotientClosed ⟨inferInstance, hKP⟩
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
    simpa [K] using
      (ContinuousMonoidHom.quotientKerContinuousMulEquivRange q)
  let eqF : (E ⧸ K) ≃ₜ* F := eqRange.trans er
  have hQ : HasPGroupOpenNormalBasis p (E ⧸ K) :=
    HasOpenNormalBasisInClass.ofContinuousMulEquiv
      sourceData.isEpimorphicallyFree.hasOpenNormalBasisInClass eqF.symm
  have hE : HasPGroupOpenNormalBasis p E := HasOpenNormalBasisInClass.extension
    (FiniteGroupClass.pGroup_formation p).isomClosed
    (FiniteGroupClass.pGroup_formation p).quotientClosed
    (FiniteGroupClass.pGroup_extensionClosed p) K hKclosed hK hQ
  obtain ⟨s, hs⟩ :=
    freeProP_exists_continuous_section_of_surjective sourceData hbasis hE q hq
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

theorem freeProP_continuousCohomologyZModPLifted_degree_two_π_apply_eq_zero
    {d : ℕ}
    (sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p))
    (hbasis : Cardinal.mk sourceData.basis = d)
    (z : Cohomology.trivialZModPCocyclesLifted p sourceData.carrier 2) :
    ContinuousCohomology.π
        (Cohomology.trivialZModPLifted p sourceData.carrier) 2 z = 0 := by
  obtain ⟨b, hb⟩ := normalizedCocycle_is_continuous_coboundary sourceData hbasis z
  let K := Cohomology.trivialZModPCochainsLifted p sourceData.carrier
  let c : K.X 1 := homogeneousPrimitive z b
  have hc : (K.d 1 2).hom c = (K.iCycles 2).hom z :=
    homogeneousPrimitive_boundary z b hb
  have hzc : (K.toCycles 1 2).hom c = z := by
    apply Cohomology.topModule_mono_injective_lifted (K.iCycles 2)
    calc
      (K.iCycles 2).hom ((K.toCycles 1 2).hom c) = (K.d 1 2).hom c := by
        have hcomp := ConcreteCategory.congr_hom (K.toCycles_i 1 2) c
        change (K.iCycles 2).hom ((K.toCycles 1 2).hom c) = (K.d 1 2).hom c at hcomp
        exact hcomp
      _ = (K.iCycles 2).hom z := hc
  rw [← hzc]
  have hzero := ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ 1 2) c
  exact hzero

theorem freeProP_continuousCohomologyZModPLifted_degree_two_π_eq_zero
    {d : ℕ}
    (sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p))
    (hbasis : Cardinal.mk sourceData.basis = d) :
    ContinuousCohomology.π
        (Cohomology.trivialZModPLifted p sourceData.carrier) 2 = 0 := by
  ext z
  exact freeProP_continuousCohomologyZModPLifted_degree_two_π_apply_eq_zero
    sourceData hbasis z

theorem freeProP_continuousCohomologyZModPLifted_degree_two_subsingleton
    {d : ℕ}
    (sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p))
    (hbasis : Cardinal.mk sourceData.basis = d) :
    Subsingleton
      (Cohomology.continuousCohomologyZModPLifted p sourceData.carrier 2) := by
  let H := Cohomology.continuousCohomologyZModPLifted p sourceData.carrier 2
  let π := ContinuousCohomology.π
    (Cohomology.trivialZModPLifted p sourceData.carrier) 2
  have hπ : π = 0 :=
    freeProP_continuousCohomologyZModPLifted_degree_two_π_eq_zero sourceData hbasis
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

end ClassFieldTower.ProP
