import ProCGroups.ProC.InverseLimits.Limits

set_option autoImplicit false

/-!
# Closed subgroups, ranges, and extensions of pro-\(C\) groups

The pro-\(C\) basis passes to closed subgroups when \(C\) is subgroup-closed,
to Hausdorff continuous quotients when \(C\) is a formation, and across a
closed normal extension when \(C\) is extension-closed.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u

section

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace HasOpenNormalBasisInClass

omit [IsTopologicalGroup G] in
/-- A closed subgroup of a pro-\(C\) group is pro-\(C\). -/
theorem of_closedSubgroup
    (hIso : FiniteGroupClass.IsomClosed C)
    (hSub : FiniteGroupClass.SubgroupClosed C)
    (hG : HasOpenNormalBasisInClass C G) (H : ClosedSubgroup G) :
    HasOpenNormalBasisInClass C ↥(H : Subgroup G) := by
  intro W hW h1W
  have hW_nhds : W ∈ 𝓝 (1 : H) := hW.mem_nhds h1W
  rcases (mem_nhds_subtype (H : Set G) (1 : H) W).1 hW_nhds with
    ⟨W₀, hW₀_nhds, hW₀W⟩
  rcases mem_nhds_iff.mp hW₀_nhds with ⟨W', hW'W₀, hW'open, h1W'⟩
  rcases hG W' hW'open h1W' with ⟨V, hVW', hCV⟩
  let VH : OpenNormalSubgroup H :=
    OpenNormalSubgroup.comap ((H : Subgroup G).subtype) continuous_subtype_val V
  have hVHW : (((VH : Subgroup H) : Set H)) ⊆ W := by
    intro x hx
    exact hW₀W <| by
      change x.1 ∈ W₀
      exact hW'W₀ (hVW' hx)
  let ψ : H →* G ⧸ (V : Subgroup G) :=
    (QuotientGroup.mk' (V : Subgroup G)).comp ((H : Subgroup G).subtype)
  have hRange : C ψ.range := hSub ψ.range hCV
  have hKerEq : (VH : Subgroup H) = ψ.ker := by
    ext x
    constructor
    · intro hx
      change x.1 ∈ (V : Subgroup G) at hx
      rw [MonoidHom.mem_ker]
      change QuotientGroup.mk' (V : Subgroup G) x.1 = 1
      exact (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) x.1).2 hx
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      change QuotientGroup.mk' (V : Subgroup G) x.1 = 1 at hx
      change x.1 ∈ (V : Subgroup G)
      exact (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) x.1).1
        hx
  have hQuotVH : C (H ⧸ (VH : Subgroup H)) := by
    let e1 : H ⧸ (VH : Subgroup H) ≃* H ⧸ ψ.ker :=
      QuotientGroup.quotientMulEquivOfEq hKerEq
    exact hIso
      ⟨(e1.trans (QuotientGroup.quotientKerEquivRange ψ)).symm⟩
      hRange
  exact ⟨VH, hVHW, hQuotVH⟩

omit [IsTopologicalGroup G] in
/-- A closed ordinary subgroup of a pro-\(C\) group is pro-\(C\) with the induced topology. -/
theorem of_isClosed_subgroup
    (hIso : FiniteGroupClass.IsomClosed C)
    (hSub : FiniteGroupClass.SubgroupClosed C)
    (hG : HasOpenNormalBasisInClass C G) (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    HasOpenNormalBasisInClass C H := by
  let HC : ClosedSubgroup G := ⟨H, hH⟩
  exact of_closedSubgroup (C := C) hIso hSub hG HC

omit [IsTopologicalGroup G] in
/-- Closed-subgroup permanence for pro-\(C\) groups from a full formation package. -/
theorem of_closedSubgroup_of_fullFormation
    (hC : FiniteGroupClass.FullFormation C)
    (hG : HasOpenNormalBasisInClass C G) (H : ClosedSubgroup G) :
    HasOpenNormalBasisInClass C ↥(H : Subgroup G) :=
  of_closedSubgroup hC.isomClosed hC.subgroupClosed hG H

omit [IsTopologicalGroup G] in
/-- Closed-subgroup permanence in ordinary subgroup form from a full formation package. -/
theorem of_isClosed_subgroup_of_fullFormation
    (hC : FiniteGroupClass.FullFormation C)
    (hG : HasOpenNormalBasisInClass C G) (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    HasOpenNormalBasisInClass C H :=
  of_isClosed_subgroup hC.isomClosed hC.subgroupClosed hG H hH

/--
The range of a continuous homomorphism from a pro-\(C\) group to a Hausdorff topological group
is again pro-\(C\), with the induced subtype topology.
-/
theorem range
    (hIso : FiniteGroupClass.IsomClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasOpenNormalBasisInClass C G)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : G →ₜ* H) :
    HasOpenNormalBasisInClass C f.toMonoidHom.range := by
  let K : Subgroup G := f.toMonoidHom.ker
  have hKclosed : IsClosed (K : Set G) := by
    exact ContinuousMonoidHom.isClosed_ker f
  have hQuotG : HasOpenNormalBasisInClass C (G ⧸ K) :=
    quotient_closedNormalSubgroup (C := C) hIso hQuot hG K hKclosed
  have e : (G ⧸ K) ≃ₜ* f.toMonoidHom.range := by
    exact ContinuousMonoidHom.quotientKerContinuousMulEquivRange f
  exact HasOpenNormalBasisInClass.ofContinuousMulEquiv (C := C) (G := G ⧸ K) hQuotG e

end HasOpenNormalBasisInClass

/-- A Hausdorff continuous quotient of a group with an open-normal \(C\)-basis again has such a
basis. -/
theorem HasOpenNormalBasisInClass.of_surjective
    (hForm : FiniteGroupClass.Formation C)
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasOpenNormalBasisInClass C G)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : G →ₜ* H) (hf : Function.Surjective f) :
    HasOpenNormalBasisInClass C H := by
  let R : Subgroup H := f.toMonoidHom.range
  have hR : HasOpenNormalBasisInClass C R :=
    HasOpenNormalBasisInClass.range hForm.isomClosed hForm.quotientClosed hG f
  let : CompactSpace R :=
    isCompact_iff_compactSpace.mp (by
      change IsCompact (Set.range (f : G → H))
      exact isCompact_range f.continuous_toFun)
  let e : R ≃ₜ* H :=
    ContinuousMulEquiv.ofBijectiveCompactToT2 (Subgroup.subtype R)
      continuous_subtype_val
      ⟨by
        intro x y hxy
        exact Subtype.ext hxy,
       by
        intro h
        rcases hf h with ⟨g, rfl⟩
        exact ⟨⟨f g, ⟨g, rfl⟩⟩, rfl⟩⟩
  exact HasOpenNormalBasisInClass.ofContinuousMulEquiv hR e

namespace HasOpenNormalBasisInClass

variable {E : Type u} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]

/--
If E is profinite, K is a normal pro-\(C\) subgroup of E, and E/K is pro-\(C\), then E is
pro-\(C\).
-/
theorem extension
    (hIso : FiniteGroupClass.IsomClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (hExt : FiniteGroupClass.ExtensionClosed C)
    [CompactSpace E] [T2Space E] [TotallyDisconnectedSpace E]
    (K : Subgroup E) [K.Normal] (hKclosed : IsClosed (K : Set E))
    (hK : HasOpenNormalBasisInClass C K) (hQ : HasOpenNormalBasisInClass C (E ⧸ K)) :
    HasOpenNormalBasisInClass C E := by
  refine HasOpenNormalBasisInClass.of_allOpenNormalQuotients (C := C)
    ?_
  intro U
  let M : Subgroup E := K ⊔ (U : Subgroup E)
  let Wsub : Subgroup (E ⧸ K) := Subgroup.map (QuotientGroup.mk' K) M
  have hWclosed : IsClosed (Wsub : Set (E ⧸ K)) := by
    have hMclosed : IsClosed (M : Set E) := by
      have hMopen : IsOpen (M : Set E) := by
        exact Subgroup.isOpen_of_openSubgroup M (show (U : Subgroup E) ≤ M from le_sup_right)
      exact Subgroup.isClosed_of_isOpen M hMopen
    have hMcompact : IsCompact (M : Set E) := hMclosed.isCompact
    have hcont : Continuous (QuotientGroup.mk' K : E → E ⧸ K) := continuous_quotient_mk'
    have himage : IsCompact ((QuotientGroup.mk' K) '' (M : Set E)) := hMcompact.image hcont
    have hEq : (QuotientGroup.mk' K) '' (M : Set E) = (Wsub : Set (E ⧸ K)) := by
      ext x
      simp only [QuotientGroup.mk'_apply, mem_image, SetLike.mem_coe, Subgroup.coe_map, M, Wsub]
    rw [← hEq]
    exact himage.isClosed
  have hWfinite : Finite ((E ⧸ K) ⧸ Wsub) := by
    have hMopen : IsOpen (M : Set E) := by
      exact Subgroup.isOpen_of_openSubgroup M (show (U : Subgroup E) ≤ M from le_sup_right)
    have hMfinite : Finite (E ⧸ M) :=
      (subgroup_isOpen_iff_isClosed_finite_quotient (G := E) (U := M)).1 hMopen |>.2
    let e : (E ⧸ K) ⧸ Wsub ≃* E ⧸ M := by
      simpa [Wsub, M, Subgroup.map_sup] using
        (QuotientGroup.quotientQuotientEquivQuotient K M (show K ≤ M from le_sup_left))
    exact Finite.of_injective e e.injective
  have hWopen : IsOpen (Wsub : Set (E ⧸ K)) :=
    (subgroup_isOpen_iff_isClosed_finite_quotient (G := E ⧸ K) (U := Wsub)).2
      ⟨hWclosed, hWfinite⟩
  let W : OpenNormalSubgroup (E ⧸ K) :=
    { toOpenSubgroup := ⟨Wsub, hWopen⟩
      isNormal' := inferInstance }
  have hQuotM : C (E ⧸ M) := by
    let e : (E ⧸ K) ⧸ (W : Subgroup (E ⧸ K)) ≃* E ⧸ M := by
      simpa [W, Wsub, M, Subgroup.map_sup] using
        (QuotientGroup.quotientQuotientEquivQuotient K M (show K ≤ M from le_sup_left))
    exact hIso ⟨e⟩
      (HasOpenNormalBasisInClass.hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
        hIso hQuot hQ W)
  let KU : OpenNormalSubgroup K :=
    OpenNormalSubgroup.comap (K.subtype) continuous_subtype_val U
  let ψ : K →* E ⧸ (U : Subgroup E) :=
    (QuotientGroup.mk' (U : Subgroup E)).comp K.subtype
  have hKerEq : (KU : Subgroup K) = ψ.ker := by
    ext x
    constructor
    · intro hx
      simpa [MonoidHom.mem_ker, KU, ψ] using
        (QuotientGroup.eq_one_iff (N := (U : Subgroup E)) x.1).2 hx
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := (U : Subgroup E)) x.1).1
        (by simpa [MonoidHom.mem_ker, KU, ψ] using hx)
  have hKernelC : C ψ.range := by
    have hQuotKU : C (K ⧸ (KU : Subgroup K)) :=
      HasOpenNormalBasisInClass.hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
        hIso hQuot hK KU
    let e1 : K ⧸ (KU : Subgroup K) ≃* K ⧸ ψ.ker :=
      QuotientGroup.quotientMulEquivOfEq hKerEq
    exact hIso ⟨e1.trans (QuotientGroup.quotientKerEquivRange ψ)⟩ hQuotKU
  let L : Subgroup (E ⧸ (U : Subgroup E)) := Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) K
  have hRangeEq : ψ.range = L := by
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.coe_comp, QuotientGroup.coe_mk', Subgroup.coe_subtype,
  Function.comp_apply, Subtype.exists, exists_prop, Subgroup.mem_map, QuotientGroup.mk'_apply, ψ, L]
  have hLC : C L := by
    exact hIso ⟨MulEquiv.subgroupCongr hRangeEq⟩ hKernelC
  have hMapM : Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) M = L := by
    change Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) (K ⊔ (U : Subgroup E)) =
      Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) K
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hQuotL : C ((E ⧸ (U : Subgroup E)) ⧸ L) := by
    let e0 : (E ⧸ (U : Subgroup E)) ⧸ L ≃* (E ⧸ (U : Subgroup E)) ⧸
        Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) M :=
      QuotientGroup.quotientMulEquivOfEq hMapM.symm
    let e1 : (E ⧸ (U : Subgroup E)) ⧸
        Subgroup.map (QuotientGroup.mk' (U : Subgroup E)) M ≃* E ⧸ M :=
      QuotientGroup.quotientQuotientEquivQuotient (U : Subgroup E) M
        (show (U : Subgroup E) ≤ M from le_sup_right)
    exact hIso ⟨(e0.trans e1).symm⟩ hQuotM
  exact hExt L hLC hQuotL

end HasOpenNormalBasisInClass

end

end ProCGroups.ProC
