import Mathlib.GroupTheory.QuotientGroup.Basic
import ProCGroups.ProC.MaximalQuotients.ResidualCore
import ProCGroups.ProC.Quotients.ClosedNormal
import ProCGroups.ProC.Subgroups.Closed
import ProCGroups.Topologies.QuotientMaps

set_option autoImplicit false

/-!
# The pro-\(C\) residual quotient

For a hereditary finite-group class, continuous maps from compact groups into
pro-\(C\) targets kill the residual core and therefore factor uniquely through
the residual quotient.  The file also proves functoriality of the core and its
behaviour under continuous epimorphisms for full formations.
-/

open Set

namespace ProCGroups.ProC

universe u

variable {C : FiniteGroupClass}

/-- Any closed normal subgroup whose quotient has an open-normal quotient-in-\(C\) basis contains
the residual core. -/
theorem proCResidualCore_le_of_proCQuotient
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) [K.Normal]
    (hKclosed : IsClosed (K : Set G))
    (hK : HasOpenNormalBasisInClass C (G ⧸ K)) :
    proCResidualCore C G ≤ K := by
  let N : ProCQuotientKernel C G :=
    { toSubgroup := K
      isClosed' := hKclosed
      normal := inferInstance
      quotient_hasOpenNormalBasisInClass := hK }
  have hle : proCResidualCore C G ≤ N.toSubgroup := by
    simpa [proCResidualCore] using
      (sInf_le (Set.mem_range_self N) :
        sInf (Set.range fun N : ProCQuotientKernel C G => N.toSubgroup) ≤ N.toSubgroup)
  intro x hx
  exact hle hx

/-- A compact group's quotient by the kernel of a continuous map into a group with an open-normal
quotient-in-\(C\) basis inherits that basis property when `C` is hereditary. -/
private theorem hasOpenNormalBasisInClass_quotient_ker
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hHer : FiniteGroupClass.Hereditary C)
    (f : G →ₜ* H) (hH : HasOpenNormalBasisInClass C H) :
    HasOpenNormalBasisInClass C (G ⧸ f.toMonoidHom.ker) := by
  have hRange : HasOpenNormalBasisInClass C f.toMonoidHom.range :=
    HasOpenNormalBasisInClass.of_isClosed_subgroup
      C.isomClosed hHer.subgroupClosed hH f.toMonoidHom.range (ContinuousMonoidHom.isClosed_range f)
  exact HasOpenNormalBasisInClass.ofContinuousMulEquiv hRange
    (ContinuousMonoidHom.quotientKerContinuousMulEquivRange f).symm

/-- Under hereditary finite quotients, continuous homomorphisms from compact groups send the
residual core into the residual core. -/
theorem map_proCResidualCore_le_of_hom
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hHer : FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) :
    (proCResidualCore C G).map φ ≤ proCResidualCore C H := by
  refine le_sInf ?_
  intro N hN
  rw [Set.mem_range] at hN
  rcases hN with ⟨N, rfl⟩
  have : IsClosed (N.toSubgroup : Set H) := N.isClosed'
  refine Subgroup.map_le_iff_le_comap.2 ?_
  let α : G →ₜ* H ⧸ N.toSubgroup :=
    { toMonoidHom := (QuotientGroup.mk' N.toSubgroup).comp φ
      continuous_toFun := QuotientGroup.continuous_mk.comp hφ }
  have hαker_proC : HasOpenNormalBasisInClass C (G ⧸ α.toMonoidHom.ker) :=
    hasOpenNormalBasisInClass_quotient_ker hHer α N.quotient_hasOpenNormalBasisInClass
  have hαker_eq : α.toMonoidHom.ker = Subgroup.comap φ N.toSubgroup := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_comap, α]
  have hcore_le : proCResidualCore C G ≤ α.toMonoidHom.ker :=
    proCResidualCore_le_of_proCQuotient (C := C) α.toMonoidHom.ker
      (ContinuousMonoidHom.isClosed_ker α) hαker_proC
  rw [hαker_eq] at hcore_le
  exact hcore_le

/--
A continuous monoid homomorphism sends the pro-\(C\) residual core of the source into the
pro-\(C\) residual core of the target.
-/
theorem map_proCResidualCore_le_of_continuousMonoidHom
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hHer : FiniteGroupClass.Hereditary C)
    (φ : G →ₜ* H) :
    (proCResidualCore C G).map φ.toMonoidHom ≤ proCResidualCore C H :=
  map_proCResidualCore_le_of_hom (C := C) hHer φ.toMonoidHom φ.continuous_toFun

/-- Any continuous homomorphism from a compact group to a group with an open-normal
quotient-in-\(C\) basis kills the residual core when `C` is hereditary. -/
theorem proCResidualCore_le_ker_of_continuousMonoidHom_to_proC
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hHer : FiniteGroupClass.Hereditary C)
    (φ : G →ₜ* H) (hH : HasOpenNormalBasisInClass C H) :
    proCResidualCore C G ≤ φ.toMonoidHom.ker := by
  let K : Subgroup G := φ.toMonoidHom.ker
  have : K.Normal := MonoidHom.normal_ker φ.toMonoidHom
  have hquot : HasOpenNormalBasisInClass C (G ⧸ K) := by
    simpa [K] using hasOpenNormalBasisInClass_quotient_ker hHer φ hH
  simpa [K] using
    proCResidualCore_le_of_proCQuotient (C := C) (G := G) K (ContinuousMonoidHom.isClosed_ker φ)
        hquot

/-- Every continuous homomorphism from \(G\) to a group with an open-normal quotient-in-\(C\)
basis factors through the quotient by the pro-\(C\) residual core. -/
noncomputable def lift_proCResidualCoreQuotient
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hHer : FiniteGroupClass.Hereditary C)
    (φ : G →ₜ* H) (hH : HasOpenNormalBasisInClass C H) :
    G ⧸ proCResidualCore C G →ₜ* H := by
  let R : Subgroup G := proCResidualCore C G
  letI : R.Normal := proCResidualCore_normal C G
  have hRker : R ≤ φ.toMonoidHom.ker := by
    simpa [R] using
      proCResidualCore_le_ker_of_continuousMonoidHom_to_proC
        (C := C) hHer φ hH
  exact QuotientGroup.liftₜ R φ hRker

/--
The lifted map from the residual-core quotient agrees with the original map on quotient classes.
-/
@[simp] theorem lift_proCResidualCoreQuotient_mk
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hHer : FiniteGroupClass.Hereditary C)
    (φ : G →ₜ* H) (hH : HasOpenNormalBasisInClass C H) (x : G) :
    lift_proCResidualCoreQuotient (C := C) hHer φ hH
      (QuotientGroup.mk' (proCResidualCore C G) x) = φ x := by
  dsimp [lift_proCResidualCoreQuotient]
  rfl

/--
The lift from the residual-core quotient is unique among continuous homomorphisms agreeing on
all quotient classes.
-/
theorem lift_proCResidualCoreQuotient_unique
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hHer : FiniteGroupClass.Hereditary C)
    (φ : G →ₜ* H) (hH : HasOpenNormalBasisInClass C H)
    (ψ : G ⧸ proCResidualCore C G →ₜ* H)
    (hψ : ∀ x : G, ψ (QuotientGroup.mk' (proCResidualCore C G) x) = φ x) :
    ψ = lift_proCResidualCoreQuotient (C := C) hHer φ hH := by
  apply ContinuousMonoidHom.toMonoidHom_injective
  apply MonoidHom.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro x
  calc
    ψ (QuotientGroup.mk' (proCResidualCore C G) x) = φ x := hψ x
    _ = lift_proCResidualCoreQuotient (C := C) hHer φ hH
        (QuotientGroup.mk' (proCResidualCore C G) x) := by
          exact (lift_proCResidualCoreQuotient_mk (C := C) hHer φ hH x).symm

/-- Continuous epimorphisms carry the residual core onto the residual core for a full formation
when the source residual quotient is pro-\(C\). -/
theorem map_proCResidualCore_eq_of_surjective
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hC : FiniteGroupClass.FullFormation C)
    (φ : G →* H) (hφ : Continuous φ) (hφsurj : Function.Surjective φ)
    (hcoreQuot :
      letI : (proCResidualCore C G).Normal := proCResidualCore_normal C G
      HasOpenNormalBasisInClass C (G ⧸ proCResidualCore C G)) :
    (proCResidualCore C G).map φ = proCResidualCore C H := by
  let R : Subgroup G := proCResidualCore C G
  have : R.Normal := proCResidualCore_normal C G
  let N : Subgroup H := R.map φ
  have hNnormal : N.Normal := by
    refine ⟨?_⟩
    intro y hy h
    rcases hy with ⟨x, hx, rfl⟩
    rcases hφsurj h with ⟨g, rfl⟩
    exact (Subgroup.mem_map).2 ⟨g * x * g⁻¹, (show R.Normal from inferInstance).conj_mem x hx g, by
      simp only [mul_assoc, map_mul, map_inv]⟩
  have hRclosed : IsClosed (R : Set G) := by
    simpa [R] using proCResidualCore_isClosed C G
  have : TotallyDisconnectedSpace (G ⧸ R) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal R hRclosed
  have hNclosed : IsClosed (N : Set H) := by
    simpa [N, Subgroup.coe_map] using (hRclosed.isCompact.image hφ).isClosed
  have hmap_le :
      R.map φ ≤ proCResidualCore C H :=
    map_proCResidualCore_le_of_hom (C := C) hC.hereditary φ hφ
  have hRle : R ≤ Subgroup.comap φ N := by
    intro x hx
    exact (Subgroup.mem_comap).2 <| (Subgroup.mem_map).2 ⟨x, hx, rfl⟩
  let φₜ : G →ₜ* H :=
    { toMonoidHom := φ
      continuous_toFun := hφ }
  let βₜ : G ⧸ R →ₜ* H ⧸ N := QuotientGroup.mapₜ R N φₜ hRle
  let β : G ⧸ R →* H ⧸ N := βₜ.toMonoidHom
  have hβsurj : Function.Surjective β := by
    have hmkφ_surj : Function.Surjective (QuotientGroup.mk ∘ φ : G → H ⧸ N) := by
      intro y
      rcases QuotientGroup.mk'_surjective N y with ⟨h, rfl⟩
      rcases hφsurj h with ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    exact QuotientGroup.map_surjective_of_surjective (N := R) (M := N) φ hmkφ_surj hRle
  have hNquot : HasOpenNormalBasisInClass C (H ⧸ N) :=
    HasOpenNormalBasisInClass.of_surjective hC.melnikovFormation.formation hcoreQuot βₜ hβsurj
  have hcoreH_le : proCResidualCore C H ≤ N :=
    proCResidualCore_le_of_proCQuotient (C := C) N hNclosed hNquot
  exact le_antisymm hmap_le hcoreH_le

end ProCGroups.ProC
