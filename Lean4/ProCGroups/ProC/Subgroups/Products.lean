import ProCGroups.ProC.Subgroups.Closed

set_option autoImplicit false

/-!
# Closed subgroups of products of pro-\(C\) groups

This file transfers an open-normal quotient basis in \(C\) from a product to a closed subgroup
when \(C\) is subgroup closed, and specializes the result to subdirect products.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u

section

variable {ι : Type u}
variable {Gs : ι → Type u}
variable {C : FiniteGroupClass.{u}}

variable [∀ i, Group (Gs i)]
variable [∀ i, TopologicalSpace (Gs i)]
variable [∀ i, IsTopologicalGroup (Gs i)]
variable [∀ i, T2Space (Gs i)]

/-- A closed subgroup of a product of groups with open-normal \(C\)-bases again has such a basis. -/
theorem HasOpenNormalBasisInClass.of_closedSubgroup_pi
    [∀ i, CompactSpace (Gs i)] [∀ i, TotallyDisconnectedSpace (Gs i)]
    {H : Subgroup ((i : ι) → Gs i)}
    (hH : IsClosed (((H : Subgroup ((i : ι) → Gs i)) : Set ((i : ι) → Gs i))))
    (hForm : FiniteGroupClass.Formation C)
    (hSub : FiniteGroupClass.SubgroupClosed C)
    (hGs : ∀ i, HasOpenNormalBasisInClass C (Gs i)) :
    HasOpenNormalBasisInClass C ↥H := by
  have hpi : HasOpenNormalBasisInClass C ((i : ι) → Gs i) :=
    HasOpenNormalBasisInClass.pi (C := C) (α := ι) (β := Gs) hForm hGs
  exact HasOpenNormalBasisInClass.of_isClosed_subgroup
      (C := C)
      (G := ((i : ι) → Gs i))
      (H := H)
      hForm.isomClosed
      hSub
      (hG := hpi)
      hH

omit [∀ i, IsTopologicalGroup (Gs i)] in
/-- A profinite group embedded as a subdirect product of groups with open-normal \(C\)-bases again
has such a basis; the coordinatewise finite-subdirect-product criterion is exposed for reuse. -/
theorem HasOpenNormalBasisInClass.of_subdirectProduct
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (φ : H →* ((i : ι) → Gs i)) (hφcont : Continuous φ)
    (hφinj : Function.Injective φ)
    (hφsurj : ∀ i, Function.Surjective (fun x : H => φ x i))
      (hForm : FiniteGroupClass.Formation C)
      (hGs : ∀ i, HasOpenNormalBasisInClass C (Gs i)) :
      HasOpenNormalBasisInClass C H := by
  classical
  let φrange : H →* ↥(φ.range : Subgroup ((i : ι) → Gs i)) := φ.rangeRestrict
  have hφrange_continuous : Continuous φrange := by
    change Continuous (fun x : H => (⟨φ x, ⟨x, rfl⟩⟩ : ↥(φ.range : Subgroup ((i : ι) → Gs i))))
    exact Continuous.subtype_mk hφcont (fun x => ⟨x, rfl⟩)
  have hφrange_bij : Function.Bijective φrange := by
    constructor
    · intro x y hxy
      apply hφinj
      exact congrArg Subtype.val hxy
    · exact φ.rangeRestrict_surjective
  let e : H ≃ₜ* ↥(φ.range : Subgroup ((i : ι) → Gs i)) :=
    ContinuousMulEquiv.ofBijectiveCompactToT2 φrange hφrange_continuous hφrange_bij
  refine HasOpenNormalBasisInClass.of_allOpenNormalQuotients (C := C) ?_
  intro U
  let imgU : Set ↥(φ.range : Subgroup ((i : ι) → Gs i)) :=
    e.toHomeomorph '' (((U : Subgroup H) : Set H))
  have himgU_open : IsOpen imgU := e.toHomeomorph.isOpenMap _ U.isOpen'
  have h1imgU : (1 : ↥(φ.range : Subgroup ((i : ι) → Gs i))) ∈ imgU := by
    refine ⟨1, U.one_mem', ?_⟩
    change e 1 = 1
    simp only [map_one]
  have himgU_nhds : imgU ∈ 𝓝 (1 : ↥(φ.range : Subgroup ((i : ι) → Gs i))) := by
    exact himgU_open.mem_nhds h1imgU
  rcases (mem_nhds_subtype
      ((φ.range : Subgroup ((i : ι) → Gs i)) : Set ((i : ι) → Gs i))
      (1 : ↥(φ.range : Subgroup ((i : ι) → Gs i))) imgU).1 himgU_nhds with
    ⟨W, hW_nhds, hWU⟩
  rcases mem_nhds_iff.mp hW_nhds with ⟨W', hW'W, hW'open, h1W'⟩
  rcases (isOpen_pi_iff.mp hW'open) (1 : (i : ι) → Gs i) h1W' with ⟨J, WJ, hJ1, hJ2⟩
  let V : ∀ j : J, OpenNormalSubgroup (Gs j) := fun j =>
    Classical.choose <|
      hGs j (WJ j) (hJ1 j j.property).1 (hJ1 j j.property).2
  have hVsub : ∀ j : J, ((V j : Subgroup (Gs j)) : Set (Gs j)) ⊆ WJ j := fun j =>
    (Classical.choose_spec <|
      hGs j (WJ j) (hJ1 j j.property).1 (hJ1 j j.property).2).1
  have hVquot : ∀ j : J, C (Gs j ⧸ (V j : Subgroup (Gs j))) := fun j =>
    (Classical.choose_spec <|
      hGs j (WJ j) (hJ1 j j.property).1 (hJ1 j j.property).2).2
  let ψ : ∀ j : J, H →* Gs j := fun j =>
    { toFun := fun h => φ h j
      map_one' := by simp only [map_one, Pi.one_apply]
      map_mul' := by intro x y; simp only [map_mul, Pi.mul_apply]}
  let M : Subgroup H :=
    iInf fun j : J =>
      ((OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j) :
        OpenNormalSubgroup H) : Subgroup H)
  let : M.Normal := by
    exact Subgroup.normal_iInf_normal fun j : J =>
      (OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j)).isNormal'
  have hMU : M ≤ (U : Subgroup H) := by
    intro x hx
    have hxM :
        ∀ j : J,
          x ∈ ((OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j) :
            OpenNormalSubgroup H) : Subgroup H) := by
      change x ∈ iInf (fun j : J =>
        ((OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j) :
          OpenNormalSubgroup H) : Subgroup H)) at hx
      exact (Subgroup.mem_iInf).1 hx
    have hxW' : φ x ∈ W' := by
      apply hJ2
      intro j hj
      have hxj : ψ ⟨j, hj⟩ x ∈ (V ⟨j, hj⟩ : Subgroup (Gs j)) := by
        have h := hxM ⟨j, hj⟩
        change ψ ⟨j, hj⟩ x ∈ (V ⟨j, hj⟩ : Subgroup (Gs j)) at h
        exact h
      exact hVsub ⟨j, hj⟩ hxj
    have hxW :
        ((e x : ↥(φ.range : Subgroup ((i : ι) → Gs i))) : ((i : ι) → Gs i)) ∈ W := by
      apply hW'W
      exact hxW'
    rcases hWU hxW with ⟨u, huU, hux⟩
    have hxu : x = u := by
      apply hφinj
      exact congrArg Subtype.val hux.symm
    exact hxu.symm ▸ huU
  let φM : H →* ∀ j : J, Gs j ⧸ (V j : Subgroup (Gs j)) :=
    { toFun := fun h j => QuotientGroup.mk' (V j : Subgroup (Gs j)) (φ h j)
      map_one' := by
        funext j
        simp only [map_one, Pi.one_apply]
      map_mul' := by
        intro x y
        funext j
        simp only [map_mul, Pi.mul_apply]}
  have hRange : C φM.range := by
    let χ : φM.range →* ∀ j : J, Gs j ⧸ (V j : Subgroup (Gs j)) := φM.range.subtype
    have hχinj : Function.Injective χ := Subtype.coe_injective
    have hχsurj : ∀ j : J, Function.Surjective fun x : φM.range => χ x j := by
      intro j y
      rcases QuotientGroup.mk'_surjective (V j : Subgroup (Gs j)) y with ⟨g, rfl⟩
      rcases hφsurj j g with ⟨x, hx⟩
      refine ⟨⟨φM x, ⟨x, rfl⟩⟩, ?_⟩
      change
        QuotientGroup.mk' (V j : Subgroup (Gs j)) (φ x j) =
          QuotientGroup.mk' (V j : Subgroup (Gs j)) g
      have hx' : φ x j = g := hx
      exact congrArg (QuotientGroup.mk' (V j : Subgroup (Gs j))) hx'
    exact hForm.finiteSubdirectProductClosed χ hχinj hχsurj hVquot
  have hKerEq : M = φM.ker := by
    ext x
    constructor
    · intro hx
      have hxM :
          ∀ j : J,
            x ∈ ((OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j) :
              OpenNormalSubgroup H) : Subgroup H) := by
        change x ∈ iInf (fun j : J =>
          ((OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j) :
            OpenNormalSubgroup H) : Subgroup H)) at hx
        exact (Subgroup.mem_iInf).1 hx
      change (fun j : J => QuotientGroup.mk' (V j : Subgroup (Gs j)) (φ x j)) = 1
      funext j
      apply (QuotientGroup.eq_one_iff (N := (V j : Subgroup (Gs j))) (φ x j)).2
      have h := hxM j
      change φ x j ∈ (V j : Subgroup (Gs j)) at h
      exact h
    · intro hx
      have hxker :
          (fun j : J => QuotientGroup.mk' (V j : Subgroup (Gs j)) (φ x j)) = 1 := by
        exact MonoidHom.mem_ker.mp hx
      have hxM :
          ∀ j : J,
            x ∈ ((OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j) :
              OpenNormalSubgroup H) : Subgroup H) := by
        intro j
        change φ x j ∈ (V j : Subgroup (Gs j))
        exact (QuotientGroup.eq_one_iff (N := (V j : Subgroup (Gs j))) (φ x j)).1
          (congrArg
            (fun f : (j : J) → Gs j ⧸ (V j : Subgroup (Gs j)) => f j)
            hxker)
      change x ∈ iInf (fun j : J =>
        ((OpenNormalSubgroup.comap (ψ j) ((continuous_apply j.1).comp hφcont) (V j) :
          OpenNormalSubgroup H) : Subgroup H))
      exact (Subgroup.mem_iInf).2 hxM
  have hQuotM : C (H ⧸ M) := by
    let e1 : H ⧸ M ≃* H ⧸ φM.ker :=
      QuotientGroup.quotientMulEquivOfEq hKerEq
    exact hForm.isomClosed
      ⟨(e1.trans (QuotientGroup.quotientKerEquivRange φM)).symm⟩
      hRange
  have hQuotU :
      C ((H ⧸ M) ⧸ Subgroup.map (QuotientGroup.mk' M) (U : Subgroup H)) := by
    exact hForm.quotientClosed
      (N := Subgroup.map (QuotientGroup.mk' M) (U : Subgroup H)) hQuotM
  exact hForm.isomClosed
    ⟨QuotientGroup.quotientQuotientEquivQuotient M (U : Subgroup H) hMU⟩
    hQuotU

end

end ProCGroups.ProC
