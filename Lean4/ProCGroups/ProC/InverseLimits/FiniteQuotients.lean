import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup

set_option autoImplicit false

/-!
# Finite quotient objects for pro-\(C\) inverse limits

This file bundles finite discrete groups and quotients by open normal subgroups as profinite
objects. It records the induced pro-\(C\) structures and the corresponding product construction.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

section

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace HasOpenNormalBasisInClass

/-- Any finite discrete group already lying in the class \(C\) is pro-\(C\). -/
theorem of_finite_discrete (hquot : FiniteGroupClass.QuotientClosed C)
    [Finite G] [DiscreteTopology G] (hCG : C G) : HasOpenNormalBasisInClass C G := by
  refine HasOpenNormalBasisInClass.of_allOpenNormalQuotients (C := C) (G := G) ?_
  intro U
  exact hquot (N := (U : Subgroup G)) hCG

/--
If \(G\) is pro-\(C\) and \(C\) is closed under quotients, then every quotient of \(G\) by an
open normal subgroup is again pro-\(C\).
-/
theorem quotient_openNormalSubgroup
    (hForm : FiniteGroupClass.Formation C)
    [CompactSpace G] [T2Space G]
    (hG : HasOpenNormalBasisInClass C G) (U : OpenNormalSubgroup G) :
    HasOpenNormalBasisInClass C (G ⧸ (U : Subgroup G)) := by
  exact HasOpenNormalBasisInClass.of_finite_discrete (C := C) (G := G ⧸ (U : Subgroup G))
    hForm.quotientClosed (hG.quotient_mem hForm U)

/-- Quotients by open normal subgroups in the class-indexing family are pro-\(C\). -/
theorem quotient_openNormalSubgroupInClass
    (hquot : FiniteGroupClass.QuotientClosed C)
    (U : OpenNormalSubgroupInClass C G) :
    HasOpenNormalBasisInClass C (G ⧸ (U.1 : Subgroup G)) :=
  by
    let : Finite (G ⧸ (U.1 : Subgroup G)) := C.finite U.2
    exact HasOpenNormalBasisInClass.of_finite_discrete (C := C)
      (G := G ⧸ (U.1 : Subgroup G)) hquot U.2

-- Product permanence for pro-`C` groups reduces an open normal subgroup of a product to a finite
-- product of open normal subgroups, then uses formation closure for the resulting finite quotient.
/-- Arbitrary products of pro-\(C\) groups remain pro-\(C\) when \(C\) is a formation. -/
theorem pi {α : Type u} {β : α → Type u}
    [∀ a, Group (β a)] [∀ a, TopologicalSpace (β a)] [∀ a, IsTopologicalGroup (β a)]
    [∀ a, CompactSpace (β a)] [∀ a, T2Space (β a)]
    [∀ a, TotallyDisconnectedSpace (β a)]
    (hForm : FiniteGroupClass.Formation C)
    (hβ : ∀ a, HasOpenNormalBasisInClass C (β a)) :
    HasOpenNormalBasisInClass C ((a : α) → β a) := by
  classical
  let G : Type u := (a : α) → β a
  refine HasOpenNormalBasisInClass.of_allOpenNormalQuotients (C := C) (G := G) ?_
  intro U
  let hUnhds : ((U : Subgroup G) : Set G) ∈ 𝓝 (1 : G) := by
    exact U.toOpenSubgroup.isOpen'.mem_nhds U.one_mem'
  rcases mem_nhds_iff.mp hUnhds with ⟨W, hWU, hWopen, h1W⟩
  rcases (isOpen_pi_iff.mp hWopen) (1 : G) h1W with ⟨J, WJ, hJ1, hJ2⟩
  let V : ∀ j : J, OpenNormalSubgroup (β j) := fun j =>
    Classical.choose <|
      hβ j (WJ j) (hJ1 j j.property).1 (hJ1 j j.property).2
  have hVsub : ∀ j : J, ((V j : Subgroup (β j)) : Set (β j)) ⊆ WJ j := fun j =>
    (Classical.choose_spec <|
      hβ j (WJ j) (hJ1 j j.property).1 (hJ1 j j.property).2).1
  have hVquot : ∀ j : J, C (β j ⧸ (V j : Subgroup (β j))) := fun j =>
    (Classical.choose_spec <|
      hβ j (WJ j) (hJ1 j j.property).1 (hJ1 j j.property).2).2
  let M : Subgroup G :=
    iInf fun j : J =>
      ((OpenNormalSubgroup.comap
        ({ toFun := fun g : G => g j.1
           map_one' := rfl
           map_mul' := by intro x y; rfl } : G →* β j.1)
        (continuous_apply j.1) (V j) : OpenNormalSubgroup G) : Subgroup G)
  let : M.Normal := by
    exact Subgroup.normal_iInf_normal fun j : J =>
      (OpenNormalSubgroup.comap
        ({ toFun := fun g : G => g j.1
           map_one' := rfl
           map_mul' := by intro x y; rfl } : G →* β j.1)
        (continuous_apply j.1) (V j)).isNormal'
  have hMU : M ≤ (U : Subgroup G) := by
    intro x hx
    apply hWU
    apply hJ2
    intro j hj
    have hxall := hx
    simp only [M, Subgroup.mem_iInf] at hxall
    have hxj := hxall ⟨j, hj⟩
    change x j ∈ (V ⟨j, hj⟩ : Subgroup (β j)) at hxj
    have hxj' : x j ∈ (V ⟨j, hj⟩ : Subgroup (β j)) := hxj
    exact hVsub ⟨j, hj⟩ hxj'
  let φ : G →* ∀ j : J, β j ⧸ (V j : Subgroup (β j)) :=
    { toFun := fun g j => QuotientGroup.mk' (V j : Subgroup (β j)) (g j)
      map_one' := by funext j; rfl
      map_mul' := by intro x y; funext j; rfl }
  have hRange : C φ.range := by
    let ψ : φ.range →* ∀ j : J, β j ⧸ (V j : Subgroup (β j)) :=
      φ.range.subtype
    have hψinj : Function.Injective ψ := Subtype.coe_injective
    have hψsurj : ∀ j : J, Function.Surjective fun x : φ.range => ψ x j := by
      intro j y
      rcases QuotientGroup.mk'_surjective (V j : Subgroup (β j)) y with ⟨xj, rfl⟩
      let g : G := Function.update 1 j.1 xj
      refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
      change
        QuotientGroup.mk' (V j : Subgroup (β j)) (g j.1) =
          QuotientGroup.mk' (V j : Subgroup (β j)) xj
      simp only [g, Function.update_self]
    exact hForm.finiteSubdirectProductClosed ψ hψinj hψsurj hVquot
  have hKerEq : M = φ.ker := by
    ext x
    constructor
    · intro hx
      have hxM : ∀ j : J, x j.1 ∈ (V j : Subgroup (β j)) := by
        have hxall := hx
        simp only [M, Subgroup.mem_iInf] at hxall
        intro j
        have hxj := hxall j
        change x j.1 ∈ (V j : Subgroup (β j)) at hxj
        exact hxj
      change (fun j : J => QuotientGroup.mk' (V j : Subgroup (β j)) (x j.1)) = 1
      funext j
      exact (QuotientGroup.eq_one_iff (N := (V j : Subgroup (β j))) (x j.1)).2 (hxM j)
    · intro hx
      have hx' := (MonoidHom.mem_ker.mp hx)
      have hxker :
          (fun j : J => QuotientGroup.mk' (V j : Subgroup (β j)) (x j.1)) = 1 := by
        change
          (fun j : J => QuotientGroup.mk' (V j : Subgroup (β j)) (x j.1)) = 1 at hx'
        exact hx'
      have hxM : ∀ j : J, x j.1 ∈ (V j : Subgroup (β j)) := by
        intro j
        exact (QuotientGroup.eq_one_iff (N := (V j : Subgroup (β j))) (x j.1)).1
          (congrArg (fun f : (j : J) → β j ⧸ (V j : Subgroup (β j)) => f j) hxker)
      simp only [M, Subgroup.mem_iInf]
      intro j
      change x j.1 ∈ (V j : Subgroup (β j))
      exact hxM j
  have hQuotM : C (G ⧸ M) := by
    let e1 : G ⧸ M ≃* G ⧸ φ.ker :=
      QuotientGroup.quotientMulEquivOfEq hKerEq
    exact hForm.isomClosed
      ⟨(e1.trans (QuotientGroup.quotientKerEquivRange φ)).symm⟩
      hRange
  have hQuotU' :
      C ((G ⧸ M) ⧸ Subgroup.map (QuotientGroup.mk' M) (U : Subgroup G)) := by
    exact hForm.quotientClosed
      (N := Subgroup.map (QuotientGroup.mk' M) (U : Subgroup G)) hQuotM
  exact hForm.isomClosed
    ⟨QuotientGroup.quotientQuotientEquivQuotient M (U : Subgroup G) hMU⟩
    hQuotU'

end HasOpenNormalBasisInClass

/-- Every profinite group has an open-normal basis with finite quotients. -/
theorem hasOpenNormalBasisInClass_allFinite
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    HasOpenNormalBasisInClass FiniteGroupClass.allFinite G := by
  refine HasOpenNormalBasisInClass.of_allOpenNormalQuotients (C := FiniteGroupClass.allFinite) ?_
  intro U
  exact openNormalSubgroup_finiteQuotient (G := G) U

end

end ProCGroups.ProC
