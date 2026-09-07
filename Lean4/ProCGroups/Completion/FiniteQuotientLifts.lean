import ProCGroups.Completion.UniversalProperty
import ProCGroups.ProC.InverseLimits.Predicates
import ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation

set_option autoImplicit false

/-!
# Pro C Groups / Completion / Finite Quotient Lifts

This module proves that unique lifting against finite discrete \(C\)-quotients,
together with density, implies the full pro-\(C\) completion universal property.
-/

open scoped Topology

namespace ProCGroups.Completion

universe u

/--
A compatible family of continuous homomorphisms to finite stages assembles to a continuous
homomorphism to the inverse limit.
-/
noncomputable def lift_to_inverseLimit_of_compatible_finite_lifts
    {I : Type u} [Preorder I]
    (S : ProCGroups.InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [ProCGroups.InverseSystems.IsGroupSystem S]
    {A : Type u} [Group A] [TopologicalSpace A]
    (φ : ∀ i, A →ₜ* S.X i)
    (hcompat : S.CompatibleMaps (fun i => φ i)) :
    A →ₜ* S.inverseLimit :=
  { toMonoidHom :=
      { toFun := S.inverseLimitLift (fun i => φ i) hcompat
        map_one' := by
          apply S.ext
          intro i
          calc
            S.projection i (S.inverseLimitLift (fun i => φ i) hcompat 1) = φ i 1 := by
              exact S.projection_inverseLimitLift_apply (fun i => φ i) hcompat i (1 : A)
            _ = 1 := by simp only [map_one]
        map_mul' := by
          intro x y
          apply S.ext
          intro i
          calc
            S.projection i (S.inverseLimitLift (fun i => φ i) hcompat (x * y)) = φ i (x * y) := by
              exact S.projection_inverseLimitLift_apply (fun i => φ i) hcompat i (x * y)
            _ = φ i x * φ i y := by simp only [map_mul]
            _ =
                S.projection i (S.inverseLimitLift (fun i => φ i) hcompat x) *
                  S.projection i (S.inverseLimitLift (fun i => φ i) hcompat y) := by
              have hx :
                  S.projection i (S.inverseLimitLift (fun i => φ i) hcompat x) = φ i x := by
                exact S.projection_inverseLimitLift_apply (fun i => φ i) hcompat i x
              have hy :
                  S.projection i (S.inverseLimitLift (fun i => φ i) hcompat y) = φ i y := by
                exact S.projection_inverseLimitLift_apply (fun i => φ i) hcompat i y
              rw [← hx, ← hy] }
    continuous_toFun := S.continuous_inverseLimitLift (fun i => φ i) (fun i => (φ
        i).continuous_toFun)
      hcompat }

/--
A dense map from a discrete group into a pro-\(C\) group is a pro-\(C\) completion as soon as
every finite discrete \(C\)-quotient of the source lifts uniquely and continuously across it.
-/
theorem isProCCompletion_of_finiteQuotientLifts
    {C : ProCGroups.FiniteGroupClass.{u}}
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Ghat : Type u} [Group Ghat] [TopologicalSpace Ghat] [IsTopologicalGroup Ghat]
    [CompactSpace Ghat] [T2Space Ghat] [TotallyDisconnectedSpace Ghat]
    (hGhat : ProCGroups.ProC.HasOpenNormalBasisInClass C (Ghat))
    {ι : G →ₜ* Ghat}
    (hιdense : DenseRange ι)
    (hfinite :
      ∀ {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
        [Finite Q] [DiscreteTopology Q],
        C Q →
        ∀ φ : G →ₜ* Q,
          ∃! φbar : Ghat →ₜ* Q, φbar.comp ι = φ) :
    IsProCCompletion
      (C) G Ghat ι := by
  refine
    { hasOpenNormalBasisInClass := by simpa using hGhat
      denseRange := hιdense
      existsUnique_lift := ?_ }
  intro H _ _ _ _ _ _ hH ψ
  let hHproC : ProCGroups.ProC.HasOpenNormalBasisInClass C H := hH
  let S : ProCGroups.InverseSystems.InverseSystem
      (I := OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H)) :=
    ProCGroups.ProC.openNormalSubgroupInClassSystem C H
  let : Nonempty (ProCGroups.ProC.OpenNormalSubgroupInClass C H) :=
    ProCGroups.ProC.HasOpenNormalBasisInClass.openNormalSubgroupInClass_nonempty hHproC
  let :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H),
        Group (S.X U) := fun U =>
    ProCGroups.ProC.instGroupOpenNormalSubgroupInClassSystemX
      (C := C) (G := H) U
  let : ProCGroups.InverseSystems.IsGroupSystem S :=
    ProCGroups.ProC.instIsGroupSystemOpenNormalSubgroupInClassSystem (C := C) (G := H)
  let :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H),
        DiscreteTopology (S.X U) := fun U => by
      dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
      exact QuotientGroup.discreteTopology
        (openNormalSubgroup_isOpen (G := H) (OrderDual.ofDual U).1)
  let :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H),
        Finite (S.X U) := fun U => by
      dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
      exact C.finite (OrderDual.ofDual U).2
  have hStageClass :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H),
        C (S.X U) := fun U => by
    dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
    exact (OrderDual.ofDual U).2
  let q :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H), H →ₜ* S.X U := fun U =>
    { toMonoidHom := ProCGroups.ProC.openNormalSubgroupInClassProj (C := C) (G := H) U
      continuous_toFun := continuous_quotient_mk' }
  let qFun :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H), H → S.X U := fun U => q U
  have hqCompat : S.CompatibleMaps qFun := by
    intro U V hUV
    funext h
    have hc :=
      congrFun
        (ProCGroups.ProC.openNormalSubgroupInClassProj_compatible
          (C := C) (G := H) U V hUV) h
    change S.map hUV (q V h) = q U h
    change S.map hUV (q V h) = q U h at hc
    exact hc
  let ψcoord :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H), Ghat →ₜ* S.X U := fun U =>
    Classical.choose (hfinite (hStageClass U) ((q U).comp ψ))
  let ψcoordFun :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H), Ghat → S.X U := fun U =>
    ψcoord U
  have hψcoordSpec :
      ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H),
        (ψcoord U).comp ι = (q U).comp ψ := by
    intro U
    exact (Classical.choose_spec (hfinite (hStageClass U) ((q U).comp ψ))).1
  have hψcoordUnique :
      ∀ (U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H))
        (φbar : Ghat →ₜ* S.X U),
        φbar.comp ι = (q U).comp ψ →
          φbar = ψcoord U := by
    intro U φbar hφbar
    exact (Classical.choose_spec (hfinite (hStageClass U) ((q U).comp ψ))).2 φbar hφbar
  have hψcoordCompat : S.CompatibleMaps ψcoordFun := by
    intro U V hUV
    have hUV' : ((OrderDual.ofDual V).1 : Subgroup H) ≤ (OrderDual.ofDual U).1 := hUV
    let qUV : S.X V →ₜ* S.X U :=
      { toMonoidHom := by
          dsimp [S, ProCGroups.ProC.openNormalSubgroupInClassSystem]
          exact ProCGroups.ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := H) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV'
        continuous_toFun := S.continuous_map hUV }
    have hEqHom : qUV.comp (ψcoord V) = ψcoord U := by
      exact hψcoordUnique U (qUV.comp (ψcoord V)) <| by
        apply ContinuousMonoidHom.toMonoidHom_injective
        ext g
        have hqg :
            qUV ((q V) (ψ g)) = (q U) (ψ g) := by
          have hc :=
            congrFun
              (ProCGroups.ProC.openNormalSubgroupInClassProj_compatible
                (C := C) (G := H) U V hUV)
              (ψ g)
          change
            S.map hUV
                (ProCGroups.ProC.openNormalSubgroupInClassProj
                  (C := C) (G := H) V (ψ g)) =
              ProCGroups.ProC.openNormalSubgroupInClassProj
                (C := C) (G := H) U (ψ g) at hc
          change
            S.map hUV
                (ProCGroups.ProC.openNormalSubgroupInClassProj
                  (C := C) (G := H) V (ψ g)) =
              ProCGroups.ProC.openNormalSubgroupInClassProj
                (C := C) (G := H) U (ψ g)
          exact hc
        calc
          ((qUV.comp (ψcoord V)).comp ι) g = qUV (ψcoord V (ι g)) := rfl
          _ = qUV ((q V) (ψ g)) := by
            exact congrArg qUV (congrArg (fun f : G →ₜ* S.X V => f g) (hψcoordSpec V))
          _ = (q U) (ψ g) := hqg
          _ = ((q U).comp ψ) g := rfl
    funext x
    exact congrArg (fun f : Ghat →ₜ* S.X U => f x) hEqHom
  let ψInv : Ghat →ₜ* S.inverseLimit :=
    lift_to_inverseLimit_of_compatible_finite_lifts S ψcoord hψcoordCompat
  let eH : H ≃ₜ* S.inverseLimit :=
    ProCGroups.ProC.HasOpenNormalBasisInClass.openNormalSubgroupInClassMulEquivInverseLimit
      (C := C) (G := H) hForm hHproC
  have hπeH :
      ∀ (U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C H)) (h : H),
        S.projection U (eH h) = (q U) h := by
    intro U h
    have hproj :=
      S.projection_inverseLimitLift_apply qFun hqCompat U h
    change S.projection U (eH h) = q U h at hproj
    exact hproj
  let ψbar : Ghat →ₜ* H :=
    { toMonoidHom := eH.symm.toMonoidHom.comp ψInv.toMonoidHom
      continuous_toFun := eH.symm.continuous_toFun.comp ψInv.continuous_toFun }
  have hψbarComp : eH.toMonoidHom.comp ψbar.toMonoidHom = ψInv.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply S.ext
    intro U
    exact congrArg (fun z : S.inverseLimit => S.projection U z) (eH.apply_symm_apply (ψInv x))
  have hψbarFac : ψbar.comp ι = ψ := by
    apply ContinuousMonoidHom.toMonoidHom_injective
    ext g
    apply eH.injective
    apply S.ext
    intro U
    calc
      S.projection U (eH (ψbar (ι g))) = S.projection U (ψInv (ι g)) := by
        exact congrArg (fun z : S.inverseLimit => S.projection U z)
          (congrArg (fun f : Ghat →* S.inverseLimit => f (ι g)) hψbarComp)
      _ = ψcoord U (ι g) := by
        have hproj :=
          S.projection_inverseLimitLift_apply ψcoordFun hψcoordCompat U (ι g)
        change S.projection U (ψInv (ι g)) = ψcoord U (ι g) at hproj
        exact hproj
      _ = (q U) (ψ g) := by
        exact congrArg (fun f : G →ₜ* S.X U => f g) (hψcoordSpec U)
      _ = S.projection U (eH (ψ g)) := by
        symm
        exact hπeH U (ψ g)
  refine ⟨ψbar, hψbarFac, ?_⟩
  intro χ hχ
  apply ContinuousMonoidHom.toMonoidHom_injective
  apply MonoidHom.ext
  intro x
  have hEqFun : (fun z : Ghat => χ z) = fun z : Ghat => ψbar z := by
    apply DenseRange.equalizer (f := ι) hιdense
    · exact χ.continuous_toFun
    · exact ψbar.continuous_toFun
    · funext g
      exact congrArg (fun f : G →ₜ* H => f g) (hχ.trans hψbarFac.symm)
  exact congrArg (fun f : Ghat → H => f x) hEqFun

end ProCGroups.Completion
