import ProCGroups.ProP.Presentation.Basic

set_option autoImplicit false
/-!
# Projectivity of finite-basis free pro-p groups

A finite-basis free pro-`p` group lifts continuously through every continuous surjection from a
pro-`p` group.  The section form is the projective input for the standard proof that its
continuous degree-two cohomology vanishes.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups

noncomputable section

universe u

variable {p d : ℕ} [Fact p.Prime]
variable
  (sourceData :
    FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
      (FiniteGroupClass.pGroup p))

/-- A finite-basis free pro-`p` source lifts continuously through every continuous surjection
whose source is pro-`p`. -/
theorem freeProP_exists_continuous_lift_of_surjective
    (hbasis : Cardinal.mk sourceData.basis = d)
    {E : Type u} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
    [CompactSpace E] [T2Space E] [TotallyDisconnectedSpace E]
    (hE : ProC.HasPGroupOpenNormalBasis p E)
    {Q : Type u} [Group Q] [TopologicalSpace Q] [T2Space Q]
    (q : E →ₜ* Q) (hq : Function.Surjective q)
    (f : sourceData.carrier →ₜ* Q) :
    ∃ s : sourceData.carrier →ₜ* E,
      q.comp s = f := by
  classical
  let ι : ULift.{u} (Fin d) → sourceData.carrier :=
    CrowellExactSequence.freeProCChosenULiftFamilyOfBasisCard sourceData hbasis
  let hfree :=
    CrowellExactSequence.freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree
      sourceData hbasis
  let φ : ULift.{u} (Fin d) → E := fun i => Function.surjInv hq (f (ι i))
  have hφ : FreeProC.FamilyConvergesToOneAlongOpenSubgroups (G := E) φ :=
    FreeProC.FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain φ
  obtain ⟨s₀, hs₀, _⟩ :=
    FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet.existsUnique_lift_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
        (FiniteGroupClass.pGroup p)
        (FiniteGroupClass.pGroup_formation p).isomClosed
        (FiniteGroupClass.pGroup_subgroupClosed p)
        hfree hE φ hφ
  let s : sourceData.carrier →ₜ* E :=
    { toMonoidHom := s₀
      continuous_toFun := hs₀.1 }
  refine ⟨s, ?_⟩
  apply hfree.hom_ext
  intro i
  change q (s₀ (ι i)) = f (ι i)
  rw [hs₀.2 i]
  exact Function.surjInv_eq hq (f (ι i))

/-- A continuous pro-`p` surjection onto a finite-basis free pro-`p` group has a continuous
group section. -/
theorem freeProP_exists_continuous_section_of_surjective
    (hbasis : Cardinal.mk sourceData.basis = d)
    {E : Type u} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
    [CompactSpace E] [T2Space E] [TotallyDisconnectedSpace E]
    (hE : ProC.HasPGroupOpenNormalBasis p E)
    (q : E →ₜ* sourceData.carrier) (hq : Function.Surjective q) :
    ∃ s : sourceData.carrier →ₜ* E,
      q.comp s = ContinuousMonoidHom.id sourceData.carrier :=
  freeProP_exists_continuous_lift_of_surjective sourceData hbasis hE q hq
    (ContinuousMonoidHom.id sourceData.carrier)

end

end ClassFieldTower.ProP
