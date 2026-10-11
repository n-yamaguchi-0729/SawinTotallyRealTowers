/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.InverseSystems.Quotients
import Nyll.ProCGroups.InverseSystems.StagewiseIso
import Nyll.ProCGroups.ProC.Quotients.ClosedNormal

/-!
# Topological abelianization and inverse limits

This module applies topological abelianization stagewise to inverse systems and compares the
resulting limit with the abelianization of the original limit.
-/

open scoped Topology

namespace ProCGroups.Abelian

open InverseSystems.InverseSystem.CompatibleClosedNormalSubgroups

universe u v
/-- The stagewise inverse system obtained by applying topological abelianization. -/
noncomputable def abelianizationInverseSystem
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] :
    InverseSystems.InverseSystem (I := I) where
  X := fun i => TopologicalAbelianization (S.X i)
  topologicalSpace := fun i => inferInstance
  map := fun {i j} hij =>
    TopologicalAbelianization.map
      { toMonoidHom :=
          { toFun := S.map hij
            map_one' := InverseSystems.IsGroupSystem.map_one (S := S) hij
            map_mul' := InverseSystems.IsGroupSystem.map_mul (S := S) hij }
        continuous_toFun := S.continuous_map hij }
  continuous_map := by
    intro i j hij
    exact (TopologicalAbelianization.map
      { toMonoidHom :=
          { toFun := S.map hij
            map_one' := InverseSystems.IsGroupSystem.map_one (S := S) hij
            map_mul' := InverseSystems.IsGroupSystem.map_mul (S := S) hij }
        continuous_toFun := S.continuous_map hij }).continuous_toFun
  map_id := by
    intro i
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change
      QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.map (le_rfl : i ≤ i) a) =
        QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          a
    exact congrArg
      (QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (S.X i))))
      (S.map_id_apply i a)
  map_comp := by
    intro i j k hij hjk
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change
      QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.map hij (S.map hjk a)) =
        QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.map (hij.trans hjk) a)
    exact congrArg
      (QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (S.X i))))
      (S.map_comp_apply hij hjk a)

/-- Each stage of the abelianization inverse system inherits its quotient group structure. -/
instance abelianizationInverseSystem_stageGroup
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] (i : I) :
    Group ((abelianizationInverseSystem S).X i) := by
  change Group (TopologicalAbelianization (S.X i))
  infer_instance

/-- The abelianization inverse system is a group-valued inverse system. -/
instance abelianizationInverseSystem_isGroupSystem
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] :
    InverseSystems.IsGroupSystem (abelianizationInverseSystem S) where
  map_one := by
    intro i j hij
    exact (TopologicalAbelianization.map
      { toMonoidHom :=
          { toFun := S.map hij
            map_one' := InverseSystems.IsGroupSystem.map_one (S := S) hij
            map_mul' := InverseSystems.IsGroupSystem.map_mul (S := S) hij }
        continuous_toFun := S.continuous_map hij }).map_one
  map_mul := by
    intro i j hij x y
    exact (TopologicalAbelianization.map
      { toMonoidHom :=
          { toFun := S.map hij
            map_one' := InverseSystems.IsGroupSystem.map_one (S := S) hij
            map_mul' := InverseSystems.IsGroupSystem.map_mul (S := S) hij }
        continuous_toFun := S.continuous_map hij }).map_mul x y
  map_inv := by
    intro i j hij x
    exact (TopologicalAbelianization.map
      { toMonoidHom :=
          { toFun := S.map hij
            map_one' := InverseSystems.IsGroupSystem.map_one (S := S) hij
            map_mul' := InverseSystems.IsGroupSystem.map_mul (S := S) hij }
        continuous_toFun := S.continuous_map hij }).map_inv x

/--
The stagewise quotient maps assemble into a morphism from an inverse system to its stagewise
topological abelianization.
-/
def toAbelianizationInverseSystem
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] :
    S.Morphism (abelianizationInverseSystem S) where
  map := fun i => TopologicalAbelianization.mk (S.X i)
  continuous_map := fun _ => continuous_quotient_mk'
  comm := by
    intro i j hij
    funext x
    rfl

/--
The stagewise closed commutator subgroups form a compatible closed-normal family in any
group-valued inverse system of topological groups.
-/
noncomputable def closedCommutatorCompatibleClosedNormalSubgroups
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] :
    S.CompatibleClosedNormalSubgroups where
  N := fun i => Subgroup.closedCommutator (S.X i)
  normal := fun i => by infer_instance
  closed := fun i => Subgroup.isClosed_closedCommutator (S.X i)
  map_le := by
    intro i j hij x hx
    let f : S.X j →ₜ* S.X i :=
      { toMonoidHom := S.transitionHom hij
        continuous_toFun :=
          InverseSystems.InverseSystem.continuous_transitionHom (S := S) hij }
    have hxmap :
        S.transitionHom hij x ∈
          (Subgroup.closedCommutator (S.X j)).map f.toMonoidHom :=
      Subgroup.mem_map_of_mem f.toMonoidHom hx
    exact Subgroup.closedCommutator_map_le f hxmap

/--
The canonical comparison map from the abelianization of an inverse limit to the inverse limit of
the stagewise abelianizations.
-/
noncomputable def topologicalAbelianizationInverseLimitComparison
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)] :
    TopologicalAbelianization S.inverseLimit →ₜ*
      (abelianizationInverseSystem S).inverseLimit := by
  let T : InverseSystems.InverseSystem (I := I) := abelianizationInverseSystem S
  let ψ : ∀ i, TopologicalAbelianization S.inverseLimit →ₜ* T.X i := fun i =>
    TopologicalAbelianization.map
      { toMonoidHom := InverseSystems.projectionHom (S := S) i
        continuous_toFun := S.continuous_projection i }
  let ψFun : ∀ i, TopologicalAbelianization S.inverseLimit → T.X i := fun i => ψ i
  have hψ : ∀ i, Continuous (ψFun i) := by
    intro i
    exact (ψ i).continuous_toFun
  have hcompat : T.CompatibleMaps ψFun := by
    intro i j hij
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change
      QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.map hij (S.projection j a)) =
        QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.projection i a)
    exact congrArg
      (QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (S.X i))))
      (S.projection_compatible a i j hij)
  refine
    { toMonoidHom :=
        { toFun := T.inverseLimitLift ψFun hcompat
          map_one' := by
            apply T.ext
            intro i
            change ψFun i 1 = 1
            exact (ψ i).map_one
          map_mul' := by
            intro x y
            apply T.ext
            intro i
            change ψFun i (x * y) = ψFun i x * ψFun i y
            exact (ψ i).map_mul x y }
      continuous_toFun := T.continuous_inverseLimitLift ψFun hψ hcompat }

/--
The projection from the topological abelianization inverse-limit comparison to a finite stage.
-/
@[simp 900] theorem π_topologicalAbelianizationInverseLimitComparison
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    (i : I) :
    (abelianizationInverseSystem S).projection i ∘
        topologicalAbelianizationInverseLimitComparison S =
      TopologicalAbelianization.map
        { toMonoidHom :=
            { toFun := S.projection i
              map_one' := rfl
              map_mul' := by intro x y; rfl }
          continuous_toFun := S.continuous_projection i } := by
  let T : InverseSystems.InverseSystem (I := I) := abelianizationInverseSystem S
  let ψ : ∀ i, TopologicalAbelianization S.inverseLimit →ₜ* T.X i := fun i =>
    TopologicalAbelianization.map
      { toMonoidHom := InverseSystems.projectionHom (S := S) i
        continuous_toFun := S.continuous_projection i }
  let ψFun : ∀ i, TopologicalAbelianization S.inverseLimit → T.X i := fun i => ψ i
  have hcompat : T.CompatibleMaps ψFun := by
    intro i j hij
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change
      QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.map hij (S.projection j a)) =
        QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (S.X i)))
          (S.projection i a)
    exact congrArg
      (QuotientGroup.mk' (Subgroup.topologicalClosure (commutator (S.X i))))
      (S.projection_compatible a i j hij)
  funext x
  change T.projection i (T.inverseLimitLift ψFun hcompat x) = ψFun i x
  exact T.projection_inverseLimitLift_apply ψFun hcompat i x

/--
The finite-stage projection of the topological abelianization comparison has the stated value on
representatives.
-/
@[simp 900] theorem π_topologicalAbelianizationInverseLimitComparison_mk
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    (i : I) (x : S.inverseLimit) :
    (abelianizationInverseSystem S).projection i
        (topologicalAbelianizationInverseLimitComparison S
          (QuotientGroup.mk' (Subgroup.closedCommutator S.inverseLimit) x)) =
      QuotientGroup.mk' (Subgroup.closedCommutator (S.X i)) (S.projection i x) := by
  rfl

/--
The inverse-limit map induced by stagewise abelianization factors as the limit quotient map
followed by the abelianization comparison map.
-/
@[simp 900] theorem limMap_toAbelianizationInverseSystem_apply
    {I : Type u} [Preorder I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    (x : S.inverseLimit) :
    S.limMap (toAbelianizationInverseSystem S) x =
      topologicalAbelianizationInverseLimitComparison S
        (TopologicalAbelianization.mk S.inverseLimit x) := by
  change S.limMap (toAbelianizationInverseSystem S) x =
    topologicalAbelianizationInverseLimitComparison S
      (QuotientGroup.mk' (Subgroup.closedCommutator S.inverseLimit) x)
  apply (abelianizationInverseSystem S).ext
  intro i
  rw [S.π_limMap_apply (toAbelianizationInverseSystem S) i]
  exact (π_topologicalAbelianizationInverseLimitComparison_mk (S := S) i x).symm

/--
Auxiliary injectivity of the canonical comparison map used to build the continuous equivalence;
the main formulation is \(injective_topologicalAbelianizationInverseLimitComparison\).
-/
private theorem inj_topologicalAbelianizationInverseLimitComparison_of_profinite_inverse_system
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    Function.Injective (topologicalAbelianizationInverseLimitComparison S) := by
  let f : TopologicalAbelianization S.inverseLimit →ₜ*
      (abelianizationInverseSystem S).inverseLimit :=
    topologicalAbelianizationInverseLimitComparison S
  have : TotallyDisconnectedSpace (TopologicalAbelianization S.inverseLimit) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator S.inverseLimit)
      (Subgroup.isClosed_closedCommutator S.inverseLimit)
  have hkerbot : f.toMonoidHom.ker = ⊥ := by
    ext a
    constructor
    · intro ha
      by_contra hane
      rcases ProCGroups.ProC.exists_openNormalSubgroup_not_mem
          (G := TopologicalAbelianization S.inverseLimit) (x := a) hane with ⟨U, haU⟩
      let Q := TopologicalAbelianization S.inverseLimit ⧸
        (U : Subgroup (TopologicalAbelianization S.inverseLimit))
      have : Finite Q := openNormalSubgroup_finiteQuotient
        (G := TopologicalAbelianization S.inverseLimit) U
      have : DiscreteTopology Q :=
        QuotientGroup.discreteTopology
          (openNormalSubgroup_isOpen (G := TopologicalAbelianization S.inverseLimit) U)
      let qInv : S.inverseLimit →ₜ* TopologicalAbelianization S.inverseLimit :=
        { toMonoidHom := TopologicalAbelianization.mk S.inverseLimit
          continuous_toFun := continuous_quotient_mk' }
      let β : S.inverseLimit →ₜ* Q :=
        { toMonoidHom :=
            (QuotientGroup.mk' (U : Subgroup (TopologicalAbelianization S.inverseLimit))).comp
              qInv.toMonoidHom
          continuous_toFun := continuous_quotient_mk'.comp qInv.continuous_toFun
        }
      rcases InverseSystems.InverseSystem.factors_through_projection_finite_group_hom
          (S := S) hdir β.toMonoidHom β.continuous_toFun with ⟨i, βi, hβi_continuous, hβfac⟩
      let βiCont : S.X i →ₜ* Q :=
        { toMonoidHom := βi
          continuous_toFun := hβi_continuous }
      have hq : QuotientGroup.mk' (U : Subgroup (TopologicalAbelianization S.inverseLimit)) a =
          1 := by
        rcases QuotientGroup.mk'_surjective
            (Subgroup.topologicalClosure (commutator S.inverseLimit)) a with ⟨x, rfl⟩
        calc
          QuotientGroup.mk'
              (U : Subgroup (TopologicalAbelianization S.inverseLimit))
              (TopologicalAbelianization.mk S.inverseLimit x)
              = β x := rfl
          _ = βi (S.projection i x) := by
              exact congrFun hβfac x
          _ = TopologicalAbelianization.lift βiCont
                (TopologicalAbelianization.mk (S.X i) (S.projection i x)) := by
              symm
              exact TopologicalAbelianization.lift_apply_mk βiCont (S.projection i x)
            _ = TopologicalAbelianization.lift βiCont
                  ((abelianizationInverseSystem S).projection i
                    (topologicalAbelianizationInverseLimitComparison S
                      (QuotientGroup.mk'
                        (Subgroup.closedCommutator S.inverseLimit) x))) := by
                exact congrArg (TopologicalAbelianization.lift βiCont)
                  (π_topologicalAbelianizationInverseLimitComparison_mk (S := S) i x).symm
          _ = TopologicalAbelianization.lift βiCont
                ((abelianizationInverseSystem S).projection i 1) := by
              rw [show topologicalAbelianizationInverseLimitComparison S
                    (QuotientGroup.mk' (Subgroup.closedCommutator S.inverseLimit) x) = 1 by
                    simpa [MonoidHom.mem_ker, f] using ha]
          _ = TopologicalAbelianization.lift βiCont (1 : TopologicalAbelianization (S.X i)) := by
              rfl
          _ = 1 := by simp only [map_one]
      exact haU <| (QuotientGroup.eq_one_iff
        (N := (U : Subgroup (TopologicalAbelianization S.inverseLimit))) a).1 hq
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [MonoidHom.mem_ker]
      simp only [ContinuousMonoidHom.coe_toMonoidHom, hx, map_one]
  exact (MonoidHom.ker_eq_bot_iff (f := f.toMonoidHom)).mp hkerbot

/--
Membership in the inverse-limit closed commutator subgroup is equivalent to the displayed
coordinate condition.
-/
theorem mem_closedCommutator_inverseLimit_iff
      {I : Type u} [Preorder I] [Nonempty I]
      {S : InverseSystems.InverseSystem (I := I)}
      [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
      [∀ i, IsTopologicalGroup (S.X i)]
      [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
      [∀ i, TotallyDisconnectedSpace (S.X i)]
      (hdir : Directed (· ≤ ·) (id : I → I)) {x : S.inverseLimit} :
      x ∈ Subgroup.closedCommutator S.inverseLimit ↔
        ∀ i, S.projection i x ∈ Subgroup.closedCommutator (S.X i) := by
    constructor
    · intro hx i
      have hxmk :
          QuotientGroup.mk' (Subgroup.closedCommutator S.inverseLimit) x = 1 :=
        (TopologicalAbelianization.mk_eq_one_iff (G := S.inverseLimit) (x := x)).2 hx
      have hcoord :=
        π_topologicalAbelianizationInverseLimitComparison_mk (S := S) i x
      have hcoord' :
          (abelianizationInverseSystem S).projection i
              ((topologicalAbelianizationInverseLimitComparison S)
                (QuotientGroup.mk' (Subgroup.closedCommutator S.inverseLimit) x)) =
            QuotientGroup.mk' (Subgroup.closedCommutator (S.X i)) (S.projection i x) := by
        exact hcoord
      rw [hxmk] at hcoord'
      have hmk :
          QuotientGroup.mk' (Subgroup.closedCommutator (S.X i)) (S.projection i x) = 1 := by
        exact hcoord'.symm.trans
          (InverseSystems.projection_one (S := abelianizationInverseSystem S) i)
      exact (TopologicalAbelianization.mk_eq_one_iff
        (G := S.X i) (x := S.projection i x)).1 hmk
    · intro hxcoord
      let f := topologicalAbelianizationInverseLimitComparison S
      have hf :
          f (QuotientGroup.mk' (Subgroup.closedCommutator S.inverseLimit) x) = 1 := by
        apply (abelianizationInverseSystem S).ext
        intro i
        have hmk :
            QuotientGroup.mk' (Subgroup.closedCommutator (S.X i)) (S.projection i x) = 1 :=
          (TopologicalAbelianization.mk_eq_one_iff
            (G := S.X i) (x := S.projection i x)).2 (hxcoord i)
        change (abelianizationInverseSystem S).projection i
            (topologicalAbelianizationInverseLimitComparison S
              (QuotientGroup.mk' (Subgroup.closedCommutator S.inverseLimit) x)) =
          (abelianizationInverseSystem S).projection i 1
        exact (π_topologicalAbelianizationInverseLimitComparison_mk (S := S) i x).trans
          (hmk.trans
            (InverseSystems.projection_one (S := abelianizationInverseSystem S) i).symm)
      have hxmk :
          QuotientGroup.mk' (Subgroup.closedCommutator S.inverseLimit) x = 1 := by
        apply inj_topologicalAbelianizationInverseLimitComparison_of_profinite_inverse_system (S
            := S) hdir
        simpa only [f, map_one] using hf
      exact (TopologicalAbelianization.mk_eq_one_iff (G := S.inverseLimit) (x := x)).1 hxmk

/--
The closed commutator subgroup of a profinite inverse limit is the infimum of the pullbacks of
the stagewise closed commutator subgroups.
-/
theorem closedCommutator_inverseLimit_eq_iInf_comap
      {I : Type u} [Preorder I] [Nonempty I]
      (S : InverseSystems.InverseSystem (I := I))
      [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
      [∀ i, IsTopologicalGroup (S.X i)]
      [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
      [∀ i, TotallyDisconnectedSpace (S.X i)]
      (hdir : Directed (· ≤ ·) (id : I → I)) :
      Subgroup.closedCommutator S.inverseLimit =
        ⨅ i, (Subgroup.closedCommutator (S.X i)).comap
          ({ toFun := S.projection i
             map_one' := rfl
             map_mul' := by intro x y; rfl } : S.inverseLimit →* S.X i) := by
    change Subgroup.closedCommutator S.inverseLimit =
      ⨅ i, (Subgroup.closedCommutator (S.X i)).comap
        (InverseSystems.projectionHom (S := S) i)
    ext x
    simp only [Subgroup.mem_iInf, Subgroup.mem_comap, InverseSystems.projectionHom_apply]
    exact mem_closedCommutator_inverseLimit_iff (S := S) hdir (x := x)

/--
For the closed-commutator compatible family, the generic quotient-limit kernel is the closed
commutator subgroup of the inverse limit.
-/
theorem closedCommutatorCompatibleClosedNormalSubgroups_inverseLimitKernel
      {I : Type u} [Preorder I] [Nonempty I]
      (S : InverseSystems.InverseSystem (I := I))
      [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
      [∀ i, IsTopologicalGroup (S.X i)]
      [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
      [∀ i, TotallyDisconnectedSpace (S.X i)]
      (hdir : Directed (· ≤ ·) (id : I → I)) :
      (closedCommutatorCompatibleClosedNormalSubgroups S).inverseLimitKernel =
        Subgroup.closedCommutator S.inverseLimit := by
  symm
  simpa [closedCommutatorCompatibleClosedNormalSubgroups,
    InverseSystems.InverseSystem.CompatibleClosedNormalSubgroups.inverseLimitKernel,
    InverseSystems.projectionHom]
    using closedCommutator_inverseLimit_eq_iInf_comap (S := S) hdir

/-- The generic quotient inverse-limit theorem specialized to the closed commutator family. -/
noncomputable def closedCommutatorQuotientInverseLimitContinuousMulEquiv
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    TopologicalAbelianization S.inverseLimit ≃ₜ*
      (closedCommutatorCompatibleClosedNormalSubgroups S).quotientInverseSystem.inverseLimit := by
  let Q := closedCommutatorCompatibleClosedNormalSubgroups S
  have hkernel :
      (Subgroup.closedCommutator S.inverseLimit).map
          (ContinuousMulEquiv.refl S.inverseLimit).toMulEquiv.toMonoidHom =
        Q.inverseLimitKernel := by
    rw [closedCommutatorCompatibleClosedNormalSubgroups_inverseLimitKernel (S := S) hdir]
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hyx⟩
      simpa using hyx ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact (QuotientGroup.congrₜ
    (Subgroup.closedCommutator S.inverseLimit) Q.inverseLimitKernel
    (ContinuousMulEquiv.refl S.inverseLimit) hkernel).trans
      (Q.quotientInverseLimitContinuousMulEquiv hdir)

/--
The projection closed commutator quotient inverse limit continuous multiplicative equivalence mk
is compatible with the profinite topology and gives the continuous map or equivalence determined
by the finite-quotient data.
-/
@[simp 900] theorem projection_closedCommutatorQuotientInverseLimitContinuousMulEquiv_mk
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (i : I) (x : S.inverseLimit) :
    (closedCommutatorCompatibleClosedNormalSubgroups S).quotientInverseSystem.projection i
        (closedCommutatorQuotientInverseLimitContinuousMulEquiv (S := S) hdir
          (QuotientGroup.mk' (Subgroup.closedCommutator S.inverseLimit) x)) =
      QuotientGroup.mk'
        ((closedCommutatorCompatibleClosedNormalSubgroups S).N i)
        (S.projection i x) := by
  let Q := closedCommutatorCompatibleClosedNormalSubgroups S
  unfold closedCommutatorQuotientInverseLimitContinuousMulEquiv
  dsimp
  change Q.quotientInverseSystem.projection i
      (Q.quotientInverseLimitContinuousMulEquiv hdir
        (QuotientGroup.mk' Q.inverseLimitKernel x)) =
    QuotientGroup.mk' (Q.N i) (S.projection i x)
  unfold quotientInverseLimitContinuousMulEquiv
  change Q.quotientInverseSystem.projection i
      (Q.quotientInverseLimitComparison (QuotientGroup.mk' Q.inverseLimitKernel x)) =
    QuotientGroup.mk' (Q.N i) (S.projection i x)
  exact Q.projection_quotientInverseLimitComparison_mk i x

/--
Topological abelianization commutes with profinite inverse limits as a topological-group
isomorphism.
-/
noncomputable def topologicalAbelianizationInverseLimitContinuousMulEquiv
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    TopologicalAbelianization S.inverseLimit ≃ₜ*
      (abelianizationInverseSystem S).inverseLimit := by
  let Q := closedCommutatorCompatibleClosedNormalSubgroups S
  let E : InverseSystems.InverseSystem.InverseSystemIso Q.quotientInverseSystem
      (abelianizationInverseSystem S) :=
    { stageEquiv := fun _ => ContinuousMulEquiv.refl _
      comm := by intro i j hij x; rfl }
  exact (closedCommutatorQuotientInverseLimitContinuousMulEquiv (S := S) hdir).trans
    E.inverseLimitContinuousMulEquiv

/-- The inverse-limit comparison for topological abelianization evaluates coordinatewise. -/
@[simp 900] theorem topologicalAbelianizationInverseLimitContinuousMulEquiv_apply
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (x : TopologicalAbelianization S.inverseLimit) :
    topologicalAbelianizationInverseLimitContinuousMulEquiv (S := S) hdir x =
      topologicalAbelianizationInverseLimitComparison S x := by
  refine Quotient.inductionOn' x ?_
  intro g
  apply (abelianizationInverseSystem S).ext
  intro i
  let Q := closedCommutatorCompatibleClosedNormalSubgroups S
  let E : InverseSystems.InverseSystem.InverseSystemIso Q.quotientInverseSystem
      (abelianizationInverseSystem S) :=
    { stageEquiv := fun _ => ContinuousMulEquiv.refl _
      comm := by intro i j hij x; rfl }
  change (abelianizationInverseSystem S).projection i
      (E.inverseLimitContinuousMulEquiv
        ((closedCommutatorQuotientInverseLimitContinuousMulEquiv (S := S) hdir)
          (QuotientGroup.mk'
            (Subgroup.topologicalClosure (commutator S.inverseLimit)) g))) =
    (abelianizationInverseSystem S).projection i
      (topologicalAbelianizationInverseLimitComparison S
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator S.inverseLimit)) g))
  change (abelianizationInverseSystem S).projection i
      (Q.quotientInverseSystem.limMap E.toMorphism
        ((closedCommutatorQuotientInverseLimitContinuousMulEquiv (S := S) hdir)
          (QuotientGroup.mk'
            (Subgroup.topologicalClosure (commutator S.inverseLimit)) g))) =
    (abelianizationInverseSystem S).projection i
      (topologicalAbelianizationInverseLimitComparison S
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator S.inverseLimit)) g))
  rw [Q.quotientInverseSystem.π_limMap_apply E.toMorphism i]
  change Q.quotientInverseSystem.projection i
      ((closedCommutatorQuotientInverseLimitContinuousMulEquiv (S := S) hdir)
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator S.inverseLimit)) g)) =
    (abelianizationInverseSystem S).projection i
      (topologicalAbelianizationInverseLimitComparison S
        (QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator S.inverseLimit)) g))
  rw [projection_closedCommutatorQuotientInverseLimitContinuousMulEquiv_mk]
  rw [π_topologicalAbelianizationInverseLimitComparison_mk]
  rfl

/-- The inverse-limit comparison is injective, as a corollary of the continuous equivalence. -/
theorem injective_topologicalAbelianizationInverseLimitComparison
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    Function.Injective (topologicalAbelianizationInverseLimitComparison S) := by
  let e := topologicalAbelianizationInverseLimitContinuousMulEquiv (S := S) hdir
  intro x y hxy
  apply e.injective
  simpa [e] using hxy

/-- The inverse-limit comparison is surjective, as a corollary of the continuous equivalence. -/
theorem surjective_topologicalAbelianizationInverseLimitComparison
    {I : Type u} [Preorder I] [Nonempty I]
    (S : InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [InverseSystems.IsGroupSystem S]
    [∀ i, IsTopologicalGroup (S.X i)]
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    Function.Surjective (topologicalAbelianizationInverseLimitComparison S) := by
  let e := topologicalAbelianizationInverseLimitContinuousMulEquiv (S := S) hdir
  intro y
  rcases e.surjective y with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa [e] using hx

end ProCGroups.Abelian
