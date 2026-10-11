/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.IsPerfect
import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Nyll.ProCGroups.FiniteGroups.Solvable
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ClosedCommutator
import Nyll.ProCGroups.ProC.Quotients.ClosedNormal

/-!
# A local-abelianization criterion for prosolvable quotients

This file proves the profinite group-theoretic criterion used in the boundary argument: a
continuous epimorphism inducing injections on the abelianizations of the preimages of all open
normal subgroups admits a unique factorization of every finite solvable quotient of the source.
It then identifies the concrete prosolvable residual quotients of source and target.
-/

open scoped ProCGroupsSolvableQuotients

namespace ProCGroups.FiniteStepSolvableQuotients

universe u

/-- The local abelianization maps over all open normal subgroups are injective.  Surjectivity of
these maps follows from surjectivity of the original homomorphism. -/
def OpenNormalAbelianizationInjective
    {G Q : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (f : G →ₜ* Q) : Prop :=
  ∀ H : OpenNormalSubgroup Q,
    Function.Injective
      (topMaxSolvQuotMap
        (ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q)) 1)

/-- On every open normal subgroup of the target, all finite discrete abelian representations of
its preimage kill the kernel of the restricted map. -/
def OpenNormalFiniteDiscreteAbelianMapsKillKernel
    {G Q : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (f : G →ₜ* Q) : Prop :=
  ∀ H : OpenNormalSubgroup Q,
    ProCGroups.ProC.FiniteDiscreteAbelianMapsKillKernel
      (ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q))

/-- A surjection whose kernel is killed by every finite discrete abelian representation induces
an injective map on topological abelianizations. -/
theorem injective_topMaxSolvQuotMap_one_of_finiteDiscreteAbelianMapsKillKernel
    {G Q : Type u}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q] [T2Space Q]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (hkill : ProCGroups.ProC.FiniteDiscreteAbelianMapsKillKernel f) :
    Function.Injective (topMaxSolvQuotMap f 1) := by
  have hkerClosed : f.ker ≤ Subgroup.closedCommutator G :=
    ProCGroups.ProC.ker_le_closedCommutator_of_finiteDiscreteAbelianMapsKillKernel f hkill
  have hkerDerived : f.ker ≤ topDerivedTop G 1 := by
    simpa [Subgroup.closedCommutator, topDerivedTop, closedDerivedSeries,
      closedCommutator, commutator] using hkerClosed
  have hmap :
      (topDerivedTop G 1).map (f : G →* Q) = topDerivedTop Q 1 :=
    topDerived_map_eq_of_surj f hf
      (fun n => closedCommutator_topDerived_map_isClosed_of_compact f n) 1
  have hcomap :
      (topDerivedTop Q 1).comap (f : G →* Q) = topDerivedTop G 1 :=
    QuotientGroup.comap_eq_of_map_eq_of_ker_le
      (f := (f : G →* Q)) (N := topDerivedTop G 1) (M := topDerivedTop Q 1)
      hmap hkerDerived
  have hkerbot : (topMaxSolvQuotMap f 1).toMonoidHom.ker = ⊥ := by
    dsimp [topMaxSolvQuotMap, MaxSolvQuot]
    exact TopologicalGroup.ker_map_eq_bot_of_comap_eq
      (f := (f : G →* Q))
      (N := topDerivedTop G 1) (M := topDerivedTop Q 1)
      (topDerivedTop_le_comap (f := f) 1) hcomap
  exact (MonoidHom.ker_eq_bot_iff (f := (topMaxSolvQuotMap f 1).toMonoidHom)).mp hkerbot

/-- Finite discrete abelian representations on all open-normal preimages supply the local
abelianization hypothesis used by the prosolvable quotient criterion. -/
theorem openNormalAbelianizationInjective_of_finiteDiscreteAbelianMapsKillKernel
    {G Q : Type u}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q] [T2Space Q]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (hkill : OpenNormalFiniteDiscreteAbelianMapsKillKernel f) :
    OpenNormalAbelianizationInjective f := by
  intro H
  have hHclosed : IsClosed ((H : Subgroup Q) : Set Q) :=
    Subgroup.isClosed_of_isOpen (H : Subgroup Q) H.isOpen'
  let : IsClosed
      ((((H : Subgroup Q).comap (f : G →* Q)) : Subgroup G) : Set G) :=
    hHclosed.preimage f.continuous_toFun
  let : CompactSpace ↥((H : Subgroup Q).comap (f : G →* Q)) :=
    (show IsClosed
      ((((H : Subgroup Q).comap (f : G →* Q)) : Subgroup G) : Set G) from
        inferInstance).isClosedEmbedding_subtypeVal.compactSpace
  let fH : ↥((H : Subgroup Q).comap (f : G →* Q)) →ₜ* ↥(H : Subgroup Q) :=
    ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q)
  have hfH : Function.Surjective fH :=
    ProCGroups.ContinuousMonoidHom.restrictPreimage_surjective
      f hf (H : Subgroup Q)
  exact injective_topMaxSolvQuotMap_one_of_finiteDiscreteAbelianMapsKillKernel
    fH hfH (hkill H)

/-- Injectivity on a preimage abelianization puts the kernel of the restricted map in the first
closed derived subgroup. -/
theorem restrictPreimage_ker_le_topDerived_one
    {G Q : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    {f : G →ₜ* Q} (hAb : OpenNormalAbelianizationInjective f)
    (H : OpenNormalSubgroup Q) :
    (ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q)).ker ≤
      topDerivedTop ↥((H : Subgroup Q).comap (f : G →* Q)) 1 := by
  intro x hx
  apply (continuousToMaxSolvQuot_eq_one_iff (G :=
    ↥((H : Subgroup Q).comap (f : G →* Q))) (m := 1) (x := x)).1
  apply hAb H
  have hx' :
      ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q) x = 1 :=
    MonoidHom.mem_ker.mp hx
  calc
    topMaxSolvQuotMap
        (ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q)) 1
        (continuousToMaxSolvQuot ↥((H : Subgroup Q).comap (f : G →* Q)) 1 x) =
      continuousToMaxSolvQuot ↥(H : Subgroup Q) 1
        (ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q) x) := by
          rfl
    _ = 1 := by rw [hx']; exact map_one _
    _ = topMaxSolvQuotMap
        (ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q)) 1 1 := by
          exact (map_one _).symm

/-- A surjection satisfying the local injectivity condition induces a
topological isomorphism on the abelianization over every open normal
subgroup. -/
noncomputable def openNormalAbelianizationContinuousMulEquiv
    {G Q : Type u}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q] [T2Space Q]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (hAb : OpenNormalAbelianizationInjective f)
    (H : OpenNormalSubgroup Q) :
    MaxSolvQuot ((H : Subgroup Q).comap (f : G →* Q)) 1 ≃ₜ*
      MaxSolvQuot (H : Subgroup Q) 1 := by
  have hHclosed : IsClosed ((H : Subgroup Q) : Set Q) :=
    Subgroup.isClosed_of_isOpen (H : Subgroup Q) H.isOpen'
  letI : IsClosed
      (((H : Subgroup Q).comap (f : G →* Q) : Subgroup G) : Set G) :=
    hHclosed.preimage f.continuous_toFun
  letI : CompactSpace
      ↥((H : Subgroup Q).comap (f : G →* Q)) :=
    (show IsClosed
      (((H : Subgroup Q).comap (f : G →* Q) : Subgroup G) : Set G) from
        inferInstance).isClosedEmbedding_subtypeVal.compactSpace
  have hrestrictClosed : IsClosedMap
      (ProCGroups.ContinuousMonoidHom.restrictPreimage
        f (H : Subgroup Q)) :=
    TopologicalGroup.restrictPreimage_isClosedMap_of_isClosedMap
      f (H : Subgroup Q) f.continuous_toFun.isClosedMap hHclosed
  let e :
      MaxSolvQuot ((H : Subgroup Q).comap (f : G →* Q)) 1 ≃*
        MaxSolvQuot (H : Subgroup Q) 1 :=
    TopologicalGroup.restrictPreimage_topMaxSolvQuot_mulEquiv
      hf hrestrictClosed
        (restrictPreimage_ker_le_topDerived_one hAb H)
  exact
    ContinuousMulEquiv.ofBijectiveCompactToT2
      (topMaxSolvQuotMap
        (ProCGroups.ContinuousMonoidHom.restrictPreimage
          f (H : Subgroup Q)) 1).toMonoidHom
      (topMaxSolvQuotMap
        (ProCGroups.ContinuousMonoidHom.restrictPreimage
          f (H : Subgroup Q)) 1).continuous_toFun
      e.bijective

private noncomputable def factorThroughOfSurjective
    {G Q A : Type u} [TopologicalSpace G] [Group G] [CompactSpace G]
    [TopologicalSpace Q] [Group Q] [T2Space Q]
    [TopologicalSpace A] [Group A]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (q : G →ₜ* A) (hker : f.ker ≤ q.ker) : Q →ₜ* A := by
  let r : Q →* A :=
    f.toMonoidHom.liftOfSurjective hf ⟨q.toMonoidHom, hker⟩
  have hcomp : r.comp f.toMonoidHom = q.toMonoidHom := by
    ext x
    exact MonoidHom.liftOfRightInverse_comp_apply
      (f := f.toMonoidHom) (f_inv := Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨q.toMonoidHom, hker⟩ x
  refine
    { toMonoidHom := r
      continuous_toFun :=
        (Topology.IsQuotientMap.of_surjective_continuous
          hf f.continuous_toFun).continuous_iff.2 ?_ }
  convert q.continuous_toFun using 1
  funext x
  exact MonoidHom.ext_iff.mp hcomp x

private theorem factorThroughOfSurjective_comp
    {G Q A : Type u} [TopologicalSpace G] [Group G] [CompactSpace G]
    [TopologicalSpace Q] [Group Q] [T2Space Q]
    [TopologicalSpace A] [Group A]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (q : G →ₜ* A) (hker : f.ker ≤ q.ker) :
    (factorThroughOfSurjective f hf q hker).comp f = q := by
  ext x
  exact MonoidHom.liftOfRightInverse_comp_apply
    (f := f.toMonoidHom) (f_inv := Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨q.toMonoidHom, hker⟩ x

/-- Under the open-normal abelianization hypothesis, the kernel of `f` is killed by every
surjective continuous finite solvable quotient of the source. -/
theorem ker_le_ker_finite_solvable_quotient
    {G Q S : Type u}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [T2Space Q]
    [TopologicalSpace S] [Group S] [DiscreteTopology S] [Group.IsSolvable S]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (hAb : OpenNormalAbelianizationInjective f)
    (q : G →ₜ* S) (hq : Function.Surjective q) :
    f.ker ≤ q.ker := by
  let K : Subgroup G := f.ker
  let N : Subgroup S := K.map q.toMonoidHom
  let : N.Normal := Subgroup.Normal.map (show K.Normal by infer_instance) q.toMonoidHom hq
  let : DiscreteTopology (S ⧸ N) :=
    QuotientGroup.discreteTopology (isOpen_discrete (N : Set S))
  let qN : G →ₜ* S ⧸ N :=
    { toMonoidHom := (QuotientGroup.mk' N).comp q.toMonoidHom
      continuous_toFun := QuotientGroup.continuous_mk.comp q.continuous_toFun }
  have hKqN : f.ker ≤ qN.ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    apply (QuotientGroup.eq_one_iff (N := N) (q x)).2
    exact ⟨x, hx, rfl⟩
  let r : Q →ₜ* S ⧸ N := factorThroughOfSurjective f hf qN hKqN
  have hrf : r.comp f = qN := factorThroughOfSurjective_comp f hf qN hKqN
  let H : OpenNormalSubgroup Q := ProCGroups.ProC.OpenNormalSubgroup.ker r
  let P : Subgroup G := (H : Subgroup Q).comap (f : G →* Q)
  have hq_mem_N : ∀ x : P, q x.1 ∈ N := by
    intro x
    have hxH : f x.1 ∈ (H : Subgroup Q) := x.2
    have hrfx : r (f x.1) = 1 := by
      exact (ProCGroups.ProC.OpenNormalSubgroup.mem_ker (f := r)).1 hxH
    have hqNx : qN x.1 = 1 := by
      rw [← hrf]
      exact hrfx
    exact (QuotientGroup.eq_one_iff (N := N) (q x.1)).1 hqNx
  let qP : P →ₜ* N :=
    { toMonoidHom := q.toMonoidHom.comp P.subtype |>.codRestrict N hq_mem_N
      continuous_toFun :=
        (q.continuous_toFun.comp continuous_subtype_val).subtype_mk hq_mem_N }
  have hNderived : topDerivedTop N 1 = ⊤ := by
    apply top_unique
    intro n _
    rcases n.2 with ⟨k, hkK, hkq⟩
    have hkP : k ∈ P := by
      change f k ∈ (H : Subgroup Q)
      have hkK' : k ∈ f.ker := by simpa [K] using hkK
      have hfk : f k = 1 := MonoidHom.mem_ker.mp hkK'
      simpa only [hfk] using (H : Subgroup Q).one_mem
    let x : P := ⟨k, hkP⟩
    have hxker :
        x ∈ (ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q)).ker := by
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      change f x.1 = 1
      have hkK' : k ∈ f.ker := by simpa [K] using hkK
      exact MonoidHom.mem_ker.mp hkK'
    have hxder : x ∈ topDerivedTop P 1 :=
      restrictPreimage_ker_le_topDerived_one hAb H hxker
    have hqPx : qP x ∈ topDerivedTop N 1 :=
      topDerived_map_le (f := qP) 1 ⟨x, hxder, rfl⟩
    have hqPx_eq : qP x = n := by
      apply Subtype.ext
      exact hkq
    exact hqPx_eq ▸ hqPx
  have hNperfect : Group.IsPerfect N := by
    rw [Group.isPerfect_def]
    change ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ = ⊤
    simpa [topDerivedTop, closedDerivedSeries, closedCommutator] using hNderived
  have hNsubsingle : Subsingleton N := by
    by_contra h
    let : Nontrivial N := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable N (by infer_instance)
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have hqxN : q x ∈ N := ⟨x, hx, rfl⟩
  exact congrArg Subtype.val (Subsingleton.elim ⟨q x, hqxN⟩ 1)

/-- Every surjective continuous finite solvable quotient of the source factors uniquely through
`f`.  This is the operational finite-quotient form of the prosolvable criterion. -/
theorem finite_solvable_quotient_existsUnique_factorization
    {G Q S : Type u}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [T2Space Q]
    [TopologicalSpace S] [Group S] [DiscreteTopology S] [Group.IsSolvable S]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (hAb : OpenNormalAbelianizationInjective f)
    (q : G →ₜ* S) (hq : Function.Surjective q) :
    ∃! r : Q →ₜ* S, r.comp f = q := by
  have hker : f.ker ≤ q.ker :=
    ker_le_ker_finite_solvable_quotient f hf hAb q hq
  let r : Q →ₜ* S := factorThroughOfSurjective f hf q hker
  have hrf : r.comp f = q := factorThroughOfSurjective_comp f hf q hker
  refine ⟨r, hrf, ?_⟩
  intro s hsf
  ext y
  rcases hf y with ⟨x, rfl⟩
  calc
    s (f x) = q x := DFunLike.congr_fun hsf x
    _ = r (f x) := (DFunLike.congr_fun hrf x).symm

/-- The kernel of `f` lies in the prosolvable residual core of the source. -/
theorem ker_le_prosolvableResidualCore
    {G Q : Type u}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q] [T2Space Q]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (hAb : OpenNormalAbelianizationInjective f) :
    f.ker ≤ ProCGroups.ProC.proCResidualCore FiniteGroupClass.solvable G := by
  intro x hx
  rw [ProCGroups.ProC.proCResidualCore, Subgroup.mem_sInf]
  rintro K ⟨N, rfl⟩
  let : IsClosed (N.toSubgroup : Set G) := N.isClosed'
  let qN : G →ₜ* G ⧸ N.toSubgroup :=
    { toMonoidHom := QuotientGroup.mk' N.toSubgroup
      continuous_toFun := continuous_quotient_mk' }
  have hqx : qN x = 1 := by
    apply N.quotient_hasOpenNormalBasisInClass.eq_one_of_mem_all_openNormalSubgroupInClass
    intro U
    let S : Type u := (G ⧸ N.toSubgroup) ⧸ (U.1 : Subgroup (G ⧸ N.toSubgroup))
    let : Finite S := U.2.1
    let : Group.IsSolvable S := U.2.2
    let : DiscreteTopology S :=
      QuotientGroup.discreteTopology
        (ProCGroups.openNormalSubgroup_isOpen (G := G ⧸ N.toSubgroup) U.1)
    let qU : G ⧸ N.toSubgroup →ₜ* S :=
      ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj U
    let q : G →ₜ* S := qU.comp qN
    have hqsurj : Function.Surjective q :=
      (ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj_surjective U).comp
        (QuotientGroup.mk'_surjective N.toSubgroup)
    have hkill : f.ker ≤ q.ker :=
      ker_le_ker_finite_solvable_quotient f hf hAb q hqsurj
    exact
      (ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj_eq_one_iff).1
        (MonoidHom.mem_ker.mp (hkill hx))
  exact (QuotientGroup.eq_one_iff (N := N.toSubgroup) x).1 hqx

/-- A local isomorphism on all open-normal abelianizations induces an equivalence on the
prosolvable residual quotients. -/
noncomputable def prosolvableResidualQuotientContinuousMulEquiv
    {G Q : Type u}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q] [T2Space Q]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (hAb : OpenNormalAbelianizationInjective f) :
    (G ⧸ ProCGroups.ProC.proCResidualCore FiniteGroupClass.solvable G) ≃ₜ*
      (Q ⧸ ProCGroups.ProC.proCResidualCore FiniteGroupClass.solvable Q) := by
  let RG : Subgroup G :=
    ProCGroups.ProC.proCResidualCore FiniteGroupClass.solvable G
  let RQ : Subgroup Q :=
    ProCGroups.ProC.proCResidualCore FiniteGroupClass.solvable Q
  have hker : f.ker ≤ RG := by
    simpa [RG] using ker_le_prosolvableResidualCore f hf hAb
  have hRGbasis : ProCGroups.ProC.HasOpenNormalBasisInClass
      FiniteGroupClass.solvable (G ⧸ RG) := by
    simpa [RG] using
      (ProCGroups.ProC.proCResidualCoreQuotient_hasOpenNormalBasisInClass
        (G := G) FiniteGroupClass.solvable_formation)
  have hmap : RG.map f.toMonoidHom = RQ := by
    simpa [RG, RQ] using
      (ProCGroups.ProC.map_proCResidualCore_eq_of_surjective
        (C := FiniteGroupClass.solvable)
        FiniteGroupClass.solvable_fullFormation f.toMonoidHom f.continuous_toFun hf hRGbasis)
  have hRQclosed : IsClosed (RQ : Set Q) := by
    simpa [RQ] using
      ProCGroups.ProC.proCResidualCore_isClosed FiniteGroupClass.solvable Q
  exact QuotientGroup.mapContinuousMulEquivOfSurjective f hf hmap hker

end ProCGroups.FiniteStepSolvableQuotients
