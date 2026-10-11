/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Finiteness
import Nyll.ProCGroups.FiniteGeneration.CharacteristicChainsAndIndices
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation

/-!
# Pro C Groups / Completion / Same Finite Quotients

This module compares abstract finite quotients with continuous finite discrete
quotients and constructs maps between profinite completions from that comparison.
-/

open scoped Topology

namespace ProCGroups.Completion

universe u

/-- Topological finite quotient predicate using continuous maps to finite discrete groups. -/
def HasSameContinuousFiniteDiscreteQuotients
    (G₁ : Type u) [Group G₁] [TopologicalSpace G₁]
    (G₂ : Type u) [Group G₂] [TopologicalSpace G₂] : Prop :=
  ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Finite Q] [DiscreteTopology Q],
    (∃ φ : G₁ →ₜ* Q, Function.Surjective φ) ↔
      (∃ ψ : G₂ →ₜ* Q, Function.Surjective ψ)

/--
The continuous finite quotient hypothesis yields a surjective continuous homomorphism between
topologically finitely generated profinite groups.
-/
theorem
  exists_surj_continuousMonoidHom_between_profiniteGroups_of_sameContinuousFiniteDiscreteQuotients
    {G₁ : Type u} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    {G₂ : Type u} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    [CompactSpace G₁]
    [CompactSpace G₂] [T2Space G₂] [TotallyDisconnectedSpace G₂]
    (hG₁fg : FiniteGeneration.TopologicallyFinitelyGenerated G₁)
    (hquot : HasSameContinuousFiniteDiscreteQuotients G₁ G₂) :
    ∃ φ : ContinuousMonoidHom G₁ G₂, Function.Surjective φ := by
  classical
  let C := FiniteGroupClass.allFinite
  have hG₂proC : ProC.HasOpenNormalBasisInClass C G₂ := by
    exact ProC.hasOpenNormalBasisInClass_allFinite
  let S₂ : InverseSystems.InverseSystem
      (I := OrderDual (ProC.OpenNormalSubgroupInClass C G₂)) :=
    ProC.openNormalSubgroupInClassSystem C G₂
  let SurjHom (U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂)) :=
    { φ : ContinuousMonoidHom G₁ (S₂.X U) // Function.Surjective φ }
  let : Nonempty (ProC.OpenNormalSubgroupInClass C G₂) :=
    ProC.HasOpenNormalBasisInClass.openNormalSubgroupInClass_nonempty hG₂proC
  let : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      Group (S₂.X U) := fun U =>
    ProC.instGroupOpenNormalSubgroupInClassSystemX
      (C := C) (G := G₂) U
  let : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      Finite (S₂.X U) := fun U => by
    dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
    exact (OrderDual.ofDual U).2
  let : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      DiscreteTopology (S₂.X U) := fun U => by
    dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
    exact QuotientGroup.discreteTopology
      (openNormalSubgroup_isOpen (G := G₂)
        ((OrderDual.ofDual U).1 : OpenNormalSubgroup G₂))
  let : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      Finite (ContinuousMonoidHom G₁ (S₂.X U)) := fun U => by
    exact
      FiniteGeneration.finite_continuousMonoidHom_to_finite_of_topologicallyFinitelyGenerated
        (G := G₁) (R := S₂.X U) hG₁fg
  let : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      TopologicalSpace (SurjHom U) := fun _ => ⊥
  let : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      DiscreteTopology (SurjHom U) := fun _ => ⟨rfl⟩
  let X₂ : InverseSystems.InverseSystem
      (I := OrderDual (ProC.OpenNormalSubgroupInClass C G₂)) :=
    { X := SurjHom
      topologicalSpace := fun U => inferInstanceAs (TopologicalSpace (SurjHom U))
      map := fun {U V} hUV φ => by
        have hUV' : ((OrderDual.ofDual V).1 : Subgroup G₂) ≤ (OrderDual.ofDual U).1 := hUV
        let qUV : ContinuousMonoidHom (S₂.X V) (S₂.X U) :=
          { toMonoidHom := by
              dsimp [S₂, ProC.openNormalSubgroupInClassSystem]
              exact ProC.OpenNormalSubgroupInClass.map
                (C := C) (G := G₂)
                (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV'
            continuous_toFun := continuous_of_discreteTopology }
        refine ⟨qUV.comp φ.1, ?_⟩
        intro x
        rcases (ProC.OpenNormalSubgroupInClass.map_surjective
            (C := C) (G := G₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV') x with ⟨y, hy⟩
        rcases φ.2 y with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        calc
          (qUV.comp φ.1) z = qUV (φ.1 z) := rfl
          _ = qUV y := by rw [hz]
          _ = x := hy
      continuous_map := by
        intro U V hUV
        exact continuous_of_discreteTopology
      map_id := by
        intro U
        funext φ
        apply Subtype.ext
        apply ContinuousMonoidHom.ext
        intro x
        change ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := G₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual U) (le_rfl)
            (φ.1 x) = φ.1 x
        exact congrFun
          (congrArg DFunLike.coe
            (ProC.OpenNormalSubgroupInClass.map_id
              (C := C) (G := G₂) (U := OrderDual.ofDual U)))
          (φ.1 x)
      map_comp := by
        intro U V W hUV hVW
        have hUV' : ((OrderDual.ofDual V).1 : Subgroup G₂) ≤ (OrderDual.ofDual U).1 := hUV
        have hVW' : ((OrderDual.ofDual W).1 : Subgroup G₂) ≤ (OrderDual.ofDual V).1 := hVW
        funext φ
        apply Subtype.ext
        apply ContinuousMonoidHom.ext
        intro x
        change ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := G₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV'
            (ProC.OpenNormalSubgroupInClass.map
              (C := C) (G := G₂)
              (U := OrderDual.ofDual V) (V := OrderDual.ofDual W) hVW' (φ.1 x)) =
          ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := G₂)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual W) (hVW'.trans hUV')
            (φ.1 x)
        exact
          congrArg
            (fun f : G₂ ⧸ (((OrderDual.ofDual W).1 : OpenNormalSubgroup G₂) : Subgroup G₂) →*
              G₂ ⧸ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G₂) : Subgroup G₂) =>
              f (φ.1 x))
            (ProC.OpenNormalSubgroupInClass.map_comp
              (C := C) (G := G₂)
              (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) (W := OrderDual.ofDual W)
              hUV' hVW') }
  let : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      Nonempty (X₂.X U) := fun U => by
    dsimp [X₂]
    let qU : G₂ →ₜ* S₂.X U :=
      { toMonoidHom := ProC.openNormalSubgroupInClassProj
          (C := C) (G := G₂) U
        continuous_toFun := by
          change Continuous
            (QuotientGroup.mk'
              (((OrderDual.ofDual U).1 : OpenNormalSubgroup G₂) : Subgroup G₂))
          exact continuous_quotient_mk' }
    have hqUsurj : Function.Surjective qU :=
      ProC.openNormalSubgroupInClassProj_surjective
        (C := C) (G := G₂) U
    rcases (hquot (S₂.X U)).2 ⟨qU, hqUsurj⟩ with ⟨φ, hφsurj⟩
    exact ⟨⟨φ, hφsurj⟩⟩
  have hdir₂ :
      Directed
        (α := OrderDual (ProC.OpenNormalSubgroupInClass C G₂))
        (· ≤ ·) (fun U => U) := by
    intro U V
    let W : ProC.OpenNormalSubgroupInClass C G₂ :=
      ⟨(OrderDual.ofDual U).1 ⊓ (OrderDual.ofDual V).1,
        FiniteGroupClass.Formation.quotient_inf_mem
          (C := C) (G := G₂)
          FiniteGroupClass.allFinite_formation
          (OrderDual.ofDual U).1 (OrderDual.ofDual V).1
          (OrderDual.ofDual U).2 (OrderDual.ofDual V).2⟩
    refine ⟨OrderDual.toDual W, ?_, ?_⟩
    · change ((W.1 : Subgroup G₂) ≤ ((OrderDual.ofDual U).1 : Subgroup G₂))
      exact inf_le_left
    · change ((W.1 : Subgroup G₂) ≤ ((OrderDual.ofDual V).1 : Subgroup G₂))
      exact inf_le_right
  rcases InverseSystems.InverseSystem.nonempty_inverseLimit_of_finite (S := X₂) hdir₂ with ⟨x₂⟩
  let ψ₂ : ∀ U : OrderDual (ProC.OpenNormalSubgroupInClass C G₂),
      G₁ → S₂.X U := fun U => (x₂.1 U).1
  have hψ₂cont : ∀ U, Continuous (ψ₂ U) := by
    intro U
    exact ((x₂.1 U).1).continuous_toFun
  have hψ₂compat : S₂.CompatibleMaps ψ₂ := by
    intro U V hUV
    funext x
    have hEq : X₂.map hUV (x₂.1 V) = x₂.1 U := x₂.2 U V hUV
    have hEq' : (X₂.map hUV (x₂.1 V)).1 = (x₂.1 U).1 := congrArg Subtype.val hEq
    exact congrArg (fun φ : ContinuousMonoidHom G₁ (S₂.X U) => φ x) hEq'
  have hψ₂surj : ∀ U, Function.Surjective (ψ₂ U) := by
    intro U
    exact (x₂.1 U).2
  let fToInv : ContinuousMonoidHom G₁ S₂.inverseLimit :=
    { toMonoidHom :=
        { toFun := S₂.inverseLimitLift ψ₂ hψ₂compat
          map_one' := by
            apply S₂.ext
            intro U
            calc
              S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat 1) = ψ₂ U 1 := by
                exact S₂.projection_inverseLimitLift_apply ψ₂ hψ₂compat U (1 : G₁)
              _ = 1 := by simp only [map_one, ψ₂]
          map_mul' := by
            intro x y
            apply S₂.ext
            intro U
            calc
              S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat (x * y)) = ψ₂ U (x * y) := by
                exact S₂.projection_inverseLimitLift_apply ψ₂ hψ₂compat U (x * y)
              _ = ψ₂ U x * ψ₂ U y := by simp only [map_mul, ψ₂]
              _ = S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat x) *
                    S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat y) := by
                  have hπx :
                      S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat x) = ψ₂ U x := by
                    exact S₂.projection_inverseLimitLift_apply ψ₂ hψ₂compat U x
                  have hπy :
                      S₂.projection U (S₂.inverseLimitLift ψ₂ hψ₂compat y) = ψ₂ U y := by
                    exact S₂.projection_inverseLimitLift_apply ψ₂ hψ₂compat U y
                  rw [← hπx, ← hπy] }
      continuous_toFun := S₂.continuous_inverseLimitLift ψ₂ hψ₂cont hψ₂compat }
  have hfToInv_surj : Function.Surjective (S₂.inverseLimitLift ψ₂ hψ₂compat) :=
    S₂.surjective_inverseLimitLift ψ₂ hψ₂cont hψ₂compat hψ₂surj hdir₂
  let e₂ : G₂ ≃ₜ* S₂.inverseLimit :=
    ProC.HasOpenNormalBasisInClass.openNormalSubgroupInClassMulEquivInverseLimit
      (C := C) (G := G₂)
      FiniteGroupClass.allFinite_formation hG₂proC
  let e₂symmHom : ContinuousMonoidHom S₂.inverseLimit G₂ :=
    { toMonoidHom := e₂.symm.toMonoidHom
      continuous_toFun := e₂.symm.continuous_toFun }
  refine ⟨e₂symmHom.comp fToInv, ?_⟩
  intro y
  rcases hfToInv_surj (e₂ y) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change e₂.symm (S₂.inverseLimitLift ψ₂ hψ₂compat x) = y
  rw [hx]
  exact e₂.symm_apply_apply y

/--
Topologically finitely generated profinite groups are determined by their continuous finite
discrete quotients.
-/
theorem topologicallyFinitelyGenerated_profiniteGroups_iso_of_sameContinuousFiniteQuotients
    {G₁ : Type u} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    {G₂ : Type u} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    [CompactSpace G₁] [T2Space G₁] [TotallyDisconnectedSpace G₁]
    [CompactSpace G₂] [T2Space G₂] [TotallyDisconnectedSpace G₂]
    (hfg₁ : FiniteGeneration.TopologicallyFinitelyGenerated G₁)
    (hfg₂ : FiniteGeneration.TopologicallyFinitelyGenerated G₂)
    (hquot : HasSameContinuousFiniteDiscreteQuotients G₁ G₂) :
    Nonempty (G₁ ≃ₜ* G₂) := by
  classical
  rcases
    exists_surj_continuousMonoidHom_between_profiniteGroups_of_sameContinuousFiniteDiscreteQuotients
      (G₁ := G₁) (G₂ := G₂) hfg₁ hquot with ⟨φ, hφsurj⟩
  have hquot_symm : HasSameContinuousFiniteDiscreteQuotients G₂ G₁ := by
    intro Q _ _ _ _ _
    exact (hquot Q).symm
  rcases
    exists_surj_continuousMonoidHom_between_profiniteGroups_of_sameContinuousFiniteDiscreteQuotients
      (G₁ := G₂) (G₂ := G₁) hfg₂ hquot_symm with ⟨ψ, hψsurj⟩
  let ψφ : ContinuousMonoidHom G₁ G₁ := ψ.comp φ
  have hψφsurj : Function.Surjective ψφ := by
    simpa [ψφ] using hψsurj.comp hφsurj
  rcases
    (FiniteGeneration.surjContinuousEndomorphismsAreAutomorphisms_of_topologicallyFinitelyGenerated
    (G := G₁) hfg₁ ψφ hψφsurj) with ⟨e, he⟩
  have hψφinj : Function.Injective ψφ := by
    intro x y hxy
    apply e.injective
    calc
      e x = ψφ x := he x
      _ = ψφ y := hxy
      _ = e y := (he y).symm
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hψφinj
    change ψ (φ x) = ψ (φ y)
    exact congrArg ψ hxy
  exact ⟨ContinuousMulEquiv.ofBijectiveCompactToT2
    φ.toMonoidHom φ.continuous_toFun ⟨hφinj, hφsurj⟩⟩


end ProCGroups.Completion
