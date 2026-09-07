import ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.GroupLike
import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteComparison

set_option autoImplicit false

/-!
# Completed Group Algebra / Separation

This module contains separation lemmas for completed group algebras using finite quotients.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [T2Space G] in
/--
A finite set of nontrivial elements in a profinite group can be avoided by one open-normal
finite quotient. This is the finite-support separation input in Lemma 5.3.5(a).
-/
theorem exists_completedGroupAlgebraIndex_avoids_finset
    (s : Finset G)
    (hs : ∀ x ∈ s, x ≠ 1) :
    ∃ U : CompletedGroupAlgebraIndex G,
      ∀ x ∈ s, x ∉ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _hs
    exact ⟨terminalCompletedGroupAlgebraIndex G,
      by simp only [Finset.notMem_empty, OpenSubgroup.mem_toSubgroup, IsEmpty.forall_iff,
        implies_true]⟩
  · intro a s has ih hs
    have ha : a ≠ 1 := hs a (by simp only [Finset.mem_insert, true_or])
    rcases ProCGroups.ProC.exists_openNormalSubgroup_not_mem (G := G) ha with ⟨A, hA⟩
    have hs' : ∀ x ∈ s, x ≠ 1 := by
      intro x hx
      exact hs x (by simp only [Finset.mem_insert, hx, or_true])
    rcases ih hs' with ⟨U, hU⟩
    let U0 : OpenNormalSubgroup G := (OrderDual.ofDual U).1
    let W0 : OpenNormalSubgroup G := A ⊓ U0
    let W : CompletedGroupAlgebraIndex G := OrderDual.toDual
      ⟨W0, ProCGroups.openNormalSubgroup_finiteQuotient (G := G) W0⟩
    refine ⟨W, ?_⟩
    intro x hx hxW
    change x ∈ A ⊓ U0 at hxW
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hA hxW.1
    · exact hU x hx hxW.2

omit [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space G]
    H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/--
For a finite-support group-algebra element and a chosen basis element \(g\), one finite quotient
separates the image of \(g\) from all other support points.
-/
theorem exists_completedGroupAlgebraIndex_separating_support
    (x : MonoidAlgebra R G) (g : G) :
    ∃ U : CompletedGroupAlgebraIndex G,
      ∀ h ∈ x.coeff.support, h ≠ g →
        openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U h ≠
          openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U
              g := by
  classical
  let bad : Finset G := (x.coeff.support.erase g).image fun h => h⁻¹ * g
  have hbad : ∀ y ∈ bad, y ≠ 1 := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨h, hh, rfl⟩
    intro h1
    have hg : h = g := by
      have hmul := congrArg (fun t : G => h * t) h1
      have hg' : g = h := by
        simpa [mul_assoc] using hmul
      exact hg'.symm
    exact (Finset.mem_erase.mp hh).1 hg
  rcases exists_completedGroupAlgebraIndex_avoids_finset (G := G) bad hbad with
    ⟨U, hU⟩
  refine ⟨U, ?_⟩
  intro h hh hne heq
  have hbadmem : h⁻¹ * g ∈ bad := by
    exact Finset.mem_image.mpr ⟨h, Finset.mem_erase.mpr ⟨hne, hh⟩, rfl⟩
  have hmem :
      h⁻¹ * g ∈ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G) := by
    exact QuotientGroup.eq.1 heq
  exact hU (h⁻¹ * g) hbadmem hmem

omit [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/--
If a finite quotient separates \(g\) from the other support points of \(x\), then the
coefficient of the image of \(g\) in the quotient group algebra is exactly the original
coefficient of \(g\).
-/
theorem completedGroupAlgebraStageMap_coeff_of_support_separated
    (U : CompletedGroupAlgebraIndex G) (x : MonoidAlgebra R G) (g : G)
    (hsep : ∀ h ∈ x.coeff.support, h ≠ g →
      openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U h ≠
        openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) :
    (completedGroupAlgebraStageMap R G U x).coeff
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) =
      x.coeff g := by
  classical
  change (Finsupp.mapDomain
      (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U) x.coeff)
      (openNormalSubgroupInClassProj (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) =
    x.coeff g
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single g]
  · simp only [Finsupp.single_eq_same]
  · intro h hh hne
    exact Finsupp.single_eq_of_ne fun heq =>
      hsep h (Finsupp.mem_support_iff.mpr hh) hne heq.symm
  · intro _hg
    simp only [Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]

omit R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/--
A finite set of nontrivial elements in a pro-\(C\) group can be avoided by one open normal
\(C\)-quotient. This is the \(C\)-indexed finite-support separation input in Lemma 5.3.5(a).
-/
theorem exists_completedGroupAlgebraIndexInClass_avoids_finset
    (C : ProCGroups.FiniteGroupClass.{v}) (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hG : HasOpenNormalBasisInClass C G) (s : Finset G) (hs : ∀ x ∈ s, x ≠ 1) :
    ∃ U : CompletedGroupAlgebraIndexInClass G C,
      ∀ x ∈ s, x ∉ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _hs
    let : Nonempty (OpenNormalSubgroupInClass C G) :=
      HasOpenNormalBasisInClass.openNormalSubgroupInClass_nonempty hG
    let : Nonempty (CompletedGroupAlgebraIndexInClass G C) := inferInstance
    exact ⟨Classical.choice inferInstance, by simp only [Finset.notMem_empty,
        OpenSubgroup.mem_toSubgroup, IsEmpty.forall_iff, implies_true]⟩
  · intro a s has ih hs
    have ha : a ≠ 1 := hs a (by simp only [Finset.mem_insert, true_or])
    rcases hG.exists_openNormalSubgroupInClass_not_mem ha with ⟨A, hA⟩
    have hs' : ∀ x ∈ s, x ≠ 1 := by
      intro x hx
      exact hs x (by simp only [Finset.mem_insert, hx, or_true])
    rcases ih hs' with ⟨U, hU⟩
    let Aidx : CompletedGroupAlgebraIndexInClass G C := OrderDual.toDual A
    rcases directed_openNormalSubgroupInClass (C := C) (G := G) hForm Aidx U with
      ⟨W, hAW, hUW⟩
    refine ⟨W, ?_⟩
    intro x hx hxW
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hA (hAW hxW)
    · exact hU x hx (hUW hxW)

omit R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/--
For any finitely supported family on a pro-\(C\) group and a chosen basis point \(g\), one
\(C\)-quotient separates the image of \(g\) from all other support points.
-/
theorem exists_completedGroupAlgebraIndexInClass_separating_finsupp_support
    {M : Type w} [Zero M]
    (C : ProCGroups.FiniteGroupClass.{v}) (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hG : HasOpenNormalBasisInClass C G) (x : G →₀ M) (g : G) :
    ∃ U : CompletedGroupAlgebraIndexInClass G C,
      ∀ h ∈ x.support, h ≠ g →
        openNormalSubgroupInClassProj (C := C) (G := G) U h ≠
          openNormalSubgroupInClassProj (C := C) (G := G) U g := by
  classical
  let bad : Finset G := (x.support.erase g).image fun h => h⁻¹ * g
  have hbad : ∀ y ∈ bad, y ≠ 1 := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨h, hh, rfl⟩
    intro h1
    have hg : h = g := by
      have hmul := congrArg (fun t : G => h * t) h1
      have hg' : g = h := by
        simpa [mul_assoc] using hmul
      exact hg'.symm
    exact (Finset.mem_erase.mp hh).1 hg
  rcases exists_completedGroupAlgebraIndexInClass_avoids_finset
      (G := G) C hForm hG bad hbad with
    ⟨U, hU⟩
  refine ⟨U, ?_⟩
  intro h hh hne heq
  have hbadmem : h⁻¹ * g ∈ bad := by
    exact Finset.mem_image.mpr ⟨h, Finset.mem_erase.mpr ⟨hne, hh⟩, rfl⟩
  have hmem :
      h⁻¹ * g ∈ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G) := by
    exact QuotientGroup.eq.1 heq
  exact hU (h⁻¹ * g) hbadmem hmem

omit [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/--
For a finite-support group-algebra element and a chosen basis element \(g\), one \(C\)-quotient
separates the image of \(g\) from all other support points.
-/
theorem exists_completedGroupAlgebraIndexInClass_separating_support
    (C : ProCGroups.FiniteGroupClass.{v}) (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hG : HasOpenNormalBasisInClass C G) (x : MonoidAlgebra R G) (g : G) :
    ∃ U : CompletedGroupAlgebraIndexInClass G C,
      ∀ h ∈ x.coeff.support, h ≠ g →
        openNormalSubgroupInClassProj (C := C) (G := G) U h ≠
          openNormalSubgroupInClassProj (C := C) (G := G) U g :=
  exists_completedGroupAlgebraIndexInClass_separating_finsupp_support
    (G := G) C hForm hG x.coeff g

omit [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    H [Group H] [TopologicalSpace H] [IsTopologicalGroup H] in
/--
If a \(C\)-quotient separates \(g\) from the other support points of \(x\), then the coefficient
of the image of \(g\) in the quotient group algebra is exactly the original coefficient of
\(g\).
-/
theorem completedGroupAlgebraStageMapInClass_coeff_of_support_separated
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (x : MonoidAlgebra R G) (g : G)
    (hsep : ∀ h ∈ x.coeff.support, h ≠ g →
      openNormalSubgroupInClassProj (C := C) (G := G) U h ≠
        openNormalSubgroupInClassProj (C := C) (G := G) U g) :
    (completedGroupAlgebraStageMapInClass C R G U x).coeff
        (openNormalSubgroupInClassProj (C := C) (G := G) U g) =
      x.coeff g := by
  classical
  change (Finsupp.mapDomain
      (openNormalSubgroupInClassProj (C := C) (G := G) U) x.coeff)
      (openNormalSubgroupInClassProj (C := C) (G := G) U g) =
    x.coeff g
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single g]
  · simp only [Finsupp.single_eq_same]
  · intro h hh hne
    exact Finsupp.single_eq_of_ne fun heq =>
      hsep h (Finsupp.mem_support_iff.mpr hh) hne heq.symm
  · intro _hg
    simp only [Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]

omit [T2Space G] in
/--
In Lemma 5.3.5(a), fixed-coefficient form, the canonical map from the abstract group algebra to
the completed group algebra is injective for profinite G. Equivalently, the kernels of the
finite group-quotient maps have trivial intersection.
-/
theorem injective_toCompletedGroupAlgebraRingHom
    : Function.Injective (toCompletedGroupAlgebraRingHom R G) := by
  intro x y hxy
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  have hcoeff : (x - y).coeff g = 0 := by
    rcases exists_completedGroupAlgebraIndex_separating_support (R := R) (G := G)
        (x - y) g with
      ⟨U, hsep⟩
    have hstage_eq : completedGroupAlgebraStageMap R G U x =
        completedGroupAlgebraStageMap R G U y := by
      have hp := congrArg (fun z : CompletedGroupAlgebraCarrier R G =>
        completedGroupAlgebraProjection R G U z) hxy
      change completedGroupAlgebraProjection R G U (toCompletedGroupAlgebra R G x) =
        completedGroupAlgebraProjection R G U (toCompletedGroupAlgebra R G y) at hp
      simpa [completedGroupAlgebraProjection_toCompletedGroupAlgebra] using hp
    have hstage : completedGroupAlgebraStageMap R G U (x - y) = 0 := by
      rw [map_sub, hstage_eq, sub_self]
    have hstage_coeff :
        (completedGroupAlgebraStageMap R G U (x - y)).coeff
            (openNormalSubgroupInClassProj
              (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) = 0 := by
      rw [hstage]
      exact
        (congrArg
          (fun c : CompletedGroupAlgebraQuotient G U →₀ R =>
            c (openNormalSubgroupInClassProj
              (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g))
          (MonoidAlgebra.coeff_zero
            (R := R) (M := CompletedGroupAlgebraQuotient G U))).trans
          Finsupp.zero_apply
    rw [completedGroupAlgebraStageMap_coeff_of_support_separated
      (R := R) (G := G) U (x - y) g hsep] at hstage_coeff
    simpa using hstage_coeff
  exact sub_eq_zero.mp (by simpa using hcoeff)

omit [T2Space G] in
/--
The dense map from the ordinary group algebra into the completed group algebra has trivial
kernel after separation by all finite quotient stages.
-/
theorem toCompletedGroupAlgebraRingHom_ker_eq_bot
    : RingHom.ker (toCompletedGroupAlgebraRingHom R G) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot (toCompletedGroupAlgebraRingHom R G)).mp
    (injective_toCompletedGroupAlgebraRingHom (R := R) (G := G))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The kernel of the map to \(\widehat{R[G]}\) is the intersection of the finite-stage kernels. -/
theorem toCompletedGroupAlgebraRingHom_ker_eq_iInf_stageMap_ker :
    RingHom.ker (toCompletedGroupAlgebraRingHom R G) =
      ⨅ U : CompletedGroupAlgebraIndex G, RingHom.ker (completedGroupAlgebraStageMap R G U) := by
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    rw [Submodule.mem_iInf]
    intro U
    rw [RingHom.mem_ker]
    have hU := congrArg (fun y : CompletedGroupAlgebraCarrier R G =>
      completedGroupAlgebraProjection R G U y) hx
    change completedGroupAlgebraProjection R G U (toCompletedGroupAlgebra R G x) =
      completedGroupAlgebraProjection R G U (0 : CompletedGroupAlgebraCarrier R G) at hU
    simpa [completedGroupAlgebraProjection_toCompletedGroupAlgebra] using hU
  · intro hx
    rw [RingHom.mem_ker]
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    change completedGroupAlgebraStageMap R G U x = 0
    exact (Submodule.mem_iInf
      (p := fun U : CompletedGroupAlgebraIndex G =>
        RingHom.ker (completedGroupAlgebraStageMap R G U))).1 hx U

omit [T2Space G] in
/-- Fixed-coefficient finite-stage kernel-family form of Lemma 5.3.5(a). -/
theorem iInf_completedGroupAlgebraStageMap_ker_eq_bot
    : (⨅ U : CompletedGroupAlgebraIndex G,
        RingHom.ker (completedGroupAlgebraStageMap R G U)) = ⊥ := by
  rw [← toCompletedGroupAlgebraRingHom_ker_eq_iInf_stageMap_ker (R := R) (G := G),
    toCompletedGroupAlgebraRingHom_ker_eq_bot (R := R) (G := G)]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/--
\(C\)-indexed form of Lemma 5.3.5(a): for a pro-\(C\) group, the canonical map from the abstract
group algebra to \(\widehat{R[G]}_{C}\) is injective.
-/
theorem injective_toCompletedGroupAlgebraInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    Function.Injective (toCompletedGroupAlgebraInClassRingHom C R G) := by
  intro x y hxy
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  have hcoeff : (x - y).coeff g = 0 := by
    rcases exists_completedGroupAlgebraIndexInClass_separating_support
        (R := R) (G := G) C hForm hG (x - y) g with
      ⟨U, hsep⟩
    have hstage_eq : completedGroupAlgebraStageMapInClass C R G U x =
        completedGroupAlgebraStageMapInClass C R G U y := by
      have hp := congrArg (fun z : CompletedGroupAlgebraInClass C R G =>
        completedGroupAlgebraProjectionInClass C R G U z) hxy
      change completedGroupAlgebraProjectionInClass C R G U
          (toCompletedGroupAlgebraInClass C R G x) =
        completedGroupAlgebraProjectionInClass C R G U
          (toCompletedGroupAlgebraInClass C R G y) at hp
      simpa [completedGroupAlgebraProjectionInClass_toCompletedGroupAlgebraInClass] using hp
    have hstage : completedGroupAlgebraStageMapInClass C R G U (x - y) = 0 := by
      rw [map_sub, hstage_eq, sub_self]
    have hstage_coeff :
        (completedGroupAlgebraStageMapInClass C R G U (x - y)).coeff
            (openNormalSubgroupInClassProj (C := C) (G := G) U g) = 0 := by
      rw [hstage]
      exact
        (congrArg
          (fun c : CompletedGroupAlgebraQuotientInClass G C U →₀ R =>
            c (openNormalSubgroupInClassProj (C := C) (G := G) U g))
          (MonoidAlgebra.coeff_zero
            (R := R) (M := CompletedGroupAlgebraQuotientInClass G C U))).trans
          Finsupp.zero_apply
    rw [completedGroupAlgebraStageMapInClass_coeff_of_support_separated
      (R := R) (G := G) C U (x - y) g hsep] at hstage_coeff
    simpa using hstage_coeff
  exact sub_eq_zero.mp (by simpa using hcoeff)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Kernel form of the \(C\)-indexed injectivity statement. -/
theorem toCompletedGroupAlgebraInClassRingHom_ker_eq_bot
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    RingHom.ker (toCompletedGroupAlgebraInClassRingHom C R G) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot (toCompletedGroupAlgebraInClassRingHom C R G)).mp
    (injective_toCompletedGroupAlgebraInClassRingHom (R := R) (G := G) C hForm hG)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/--
The kernel of the map to \(\widehat{R[G]}_{C}\) is the intersection of the \(C\)-indexed
finite-stage kernels.
-/
theorem toCompletedGroupAlgebraInClassRingHom_ker_eq_iInf_stageMapInClass_ker
    (C : ProCGroups.FiniteGroupClass.{v}) :
    RingHom.ker (toCompletedGroupAlgebraInClassRingHom C R G) =
      ⨅ U : CompletedGroupAlgebraIndexInClass G C,
        RingHom.ker (completedGroupAlgebraStageMapInClass C R G U) := by
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    rw [Submodule.mem_iInf]
    intro U
    rw [RingHom.mem_ker]
    have hU := congrArg (fun y : CompletedGroupAlgebraInClass C R G =>
      completedGroupAlgebraProjectionInClass C R G U y) hx
    change completedGroupAlgebraProjectionInClass C R G U
        (toCompletedGroupAlgebraInClass C R G x) =
      completedGroupAlgebraProjectionInClass C R G U
        (0 : CompletedGroupAlgebraInClass C R G) at hU
    simpa [completedGroupAlgebraProjectionInClass_toCompletedGroupAlgebraInClass] using hU
  · intro hx
    rw [RingHom.mem_ker]
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    change completedGroupAlgebraStageMapInClass C R G U x = 0
    exact (Submodule.mem_iInf
      (p := fun U : CompletedGroupAlgebraIndexInClass G C =>
        RingHom.ker (completedGroupAlgebraStageMapInClass C R G U))).1 hx U

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- \(C\)-indexed finite-stage kernel-family form of Lemma 5.3.5(a). -/
theorem iInf_completedGroupAlgebraStageMapInClass_ker_eq_bot
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    (⨅ U : CompletedGroupAlgebraIndexInClass G C,
        RingHom.ker (completedGroupAlgebraStageMapInClass C R G U)) = ⊥ := by
  rw [← toCompletedGroupAlgebraInClassRingHom_ker_eq_iInf_stageMapInClass_ker
      (R := R) (G := G) C ,
    toCompletedGroupAlgebraInClassRingHom_ker_eq_bot (R := R) (G := G) C hForm hG]

omit [T2Space G] in
/--
In Lemma 5.3.5(a), book kernel-family form, the intersection of the kernels of \(R[G] \to
(R/I)[G/U]\), over open coefficient ideals and finite group quotients, is zero.
-/
theorem iInf_groupAlgebraOpenFiniteQuotientKernel_eq_bot
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] :
    (⨅ K : CompletedGroupAlgebraOpenQuotientIndex R G,
        groupAlgebraOpenFiniteQuotientKernel R G K) = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_bot]
    have hxall :
        ∀ K : CompletedGroupAlgebraOpenQuotientIndex R G,
          x ∈ groupAlgebraOpenFiniteQuotientKernel R G K := by
      simpa using (Submodule.mem_iInf
        (p := fun K : CompletedGroupAlgebraOpenQuotientIndex R G =>
          groupAlgebraOpenFiniteQuotientKernel R G K)).1 hx
    have hxlimit :
        toCompletedGroupAlgebraOpenFiniteQuotientLimitRingHom R G x = 0 := by
      apply completedGroupAlgebraOpenFiniteQuotientLimit_ext (R := R) (G := G)
      intro K
      change groupAlgebraOpenFiniteQuotientMap R G K x = 0
      exact (mem_groupAlgebraOpenFiniteQuotientKernel_iff
        (R := R) (G := G) (K := K) (x := x)).1 (hxall K)
    have hcompleted :
        toCompletedGroupAlgebraRingHom R G x = 0 := by
      apply injective_completedGroupAlgebraToOpenFiniteQuotientLimit (R := R) (G := G)
      change completedGroupAlgebraToOpenFiniteQuotientLimit R G
          (toCompletedGroupAlgebra R G x) =
        completedGroupAlgebraToOpenFiniteQuotientLimit R G
          (0 : CompletedGroupAlgebraCarrier R G)
      calc
        completedGroupAlgebraToOpenFiniteQuotientLimit R G
            (toCompletedGroupAlgebra R G x) =
          toCompletedGroupAlgebraOpenFiniteQuotientLimit R G x :=
            completedGroupAlgebraToOpenFiniteQuotientLimit_toCompletedGroupAlgebra
              (R := R) (G := G) x
        _ = 0 := hxlimit
        _ = completedGroupAlgebraToOpenFiniteQuotientLimit R G
            (0 : CompletedGroupAlgebraCarrier R G) := by
          symm
          apply completedGroupAlgebraOpenFiniteQuotientLimit_ext (R := R) (G := G)
          intro K
          exact map_zero (completedGroupAlgebraOpenFiniteQuotientProjection R G K)
    exact (injective_toCompletedGroupAlgebraRingHom (R := R) (G := G)) (by
      simpa using hcompleted)
  · exact bot_le

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/--
Continuous ring homomorphisms out of \(\widehat{R[G]}\) into another completed group algebra are
determined by their values on the dense abstract group algebra.
-/
theorem completedGroupAlgebraRingHom_ext_of_comp_toCompleted
    [T2Space R]
    {f g : CompletedGroupAlgebraCarrier R G →+* CompletedGroupAlgebraCarrier R H}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : f.comp (toCompletedGroupAlgebraRingHom R G) =
      g.comp (toCompletedGroupAlgebraRingHom R G)) :
    f = g := by
  let : T2Space (CompletedGroupAlgebraCarrier R H) :=
    completedGroupAlgebra_t2Space (R := R) (G := H)
  have hdense : DenseRange (toCompletedGroupAlgebraRingHom R G) :=
    denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := G)
  have hcomp : (f : CompletedGroupAlgebraCarrier R G → CompletedGroupAlgebraCarrier R H) ∘
        (toCompletedGroupAlgebraRingHom R G) =
      (g : CompletedGroupAlgebraCarrier R G → CompletedGroupAlgebraCarrier R H) ∘
        (toCompletedGroupAlgebraRingHom R G) := by
    funext x
    exact congrFun (congrArg DFunLike.coe hfg) x
  have hfun : (f : CompletedGroupAlgebraCarrier R G → CompletedGroupAlgebraCarrier R H) = g :=
    DenseRange.equalizer hdense hf hg hcomp
  exact RingHom.ext fun x => congrFun hfun x

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Lemma 5.3.5(e), identity law for the completed-group-algebra functor. -/
theorem completedGroupAlgebraMap_id
    [T2Space R] :
    completedGroupAlgebraMap (G := G) (H := G) R (MonoidHom.id G) continuous_id =
      RingHom.id (CompletedGroupAlgebraCarrier R G) := by
  apply completedGroupAlgebraRingHom_ext_of_comp_toCompleted (R := R) (G := G) (H := G)
  · exact continuous_completedGroupAlgebraMap (R := R) (G := G) (H := G)
      (MonoidHom.id G) continuous_id
  · exact continuous_id
  · rw [completedGroupAlgebraMap_comp_toCompletedGroupAlgebra,
      finiteGroupAlgebra_mapDomainRingHom_id]
    rfl

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/--
Lemma 5.3.5(e), identity law for the completed-group-algebra functor, as an \(R\)-algebra
homomorphism.
-/
theorem completedGroupAlgebraMapAlgHom_id
    [T2Space R] :
    completedGroupAlgebraMapAlgHom (G := G) (H := G) R (MonoidHom.id G) continuous_id =
      AlgHom.id R (CompletedGroupAlgebraCarrier R G) := by
  apply AlgHom.ext
  intro x
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraMap_id (R := R) (G := G)))
    x
  simpa using h

end

end CompletedGroupAlgebra
