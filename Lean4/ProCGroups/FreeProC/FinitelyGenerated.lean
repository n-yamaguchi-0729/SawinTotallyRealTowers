import ProCGroups.FreeProC.Basic

set_option autoImplicit false

/-!
# Pro C Groups / Free pro-C / Finitely Generated

This module turns a finite discrete converging-set basis into the usual
free pro-C universal property.
-/

open scoped Topology

namespace ProCGroups.FreeProC

universe u v w

namespace IsEpimorphicallyFreeProCGroupOnConvergingSet

/--
A finite discrete converging-set basis gives the usual free pro-\(C\) universal property for a
concrete finite-group class.
-/
theorem isFreeProCGroup_of_finite
    (C : ProCGroups.FiniteGroupClass.{u})
    [hVar : Fact (ProCGroups.FiniteGroupClass.Variety C)]
    [hIso : Fact (ProCGroups.FiniteGroupClass.IsomClosed C)]
    {X : Type u} [TopologicalSpace X] [DiscreteTopology X] [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι) :
    IsFreeProCGroup (C := C) ι := by
  refine
    { hasOpenNormalBasisInClass := hι.hasOpenNormalBasisInClass
      continuous_ι := continuous_of_discreteTopology
      generates_range := hι.generates_range
      existsUnique_lift := ?_ }
  intro G _ _ _ _ _ _ hG φ _hφ
  rcases hι.existsUnique_liftHom_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass C
      hIso.out hVar.out.subgroupClosed hG φ
      (FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := G) φ) with
    ⟨f, hf, huniq⟩
  refine ⟨f.toMonoidHom, ⟨f.continuous, hf⟩, ?_⟩
  intro g hg
  let gc : F →ₜ* G := { toMonoidHom := g, continuous_toFun := hg.1 }
  exact congrArg ContinuousMonoidHom.toMonoidHom (huniq gc hg.2)

end IsEpimorphicallyFreeProCGroupOnConvergingSet




end ProCGroups.FreeProC
