import ProCGroups.Categorical.QuotientPullbackEquivalences
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import ProCGroups.ProC.OpenNormalSubgroups.ClosedAndCosets
import ProCGroups.GroupTheory.CentralizerNormalizerCommensurator
import ProCGroups.Profinite.Basic

set_option autoImplicit false

/-!
# Separation by open normal quotients

This file detects equality and closed-subgroup membership in all open normal quotients. It also
develops refinements avoiding a chosen coset, cyclic-containment consequences, and extensionality
of continuous homomorphisms from their finite quotient maps.
-/

open scoped Topology

namespace ProCGroups

universe u

/--
Membership in a closed subset of a profinite group can be tested on all open-normal quotients.
-/
theorem mem_closed_iff_forall_openNormal_quotient
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {S : Set G} (hSclosed : IsClosed S) {x : G} :
    x ∈ S ↔
      ∀ U : OpenNormalSubgroup G,
        ∃ y ∈ S, QuotientGroup.mk' (U : Subgroup G) y =
          QuotientGroup.mk' (U : Subgroup G) x := by
  constructor
  · intro hx U
    exact ⟨x, hx, rfl⟩
  · intro hx
    by_contra hxS
    let A : Set G := (fun y : G => y⁻¹ * x) '' S
    have hAclosed : IsClosed A := by
      exact (hSclosed.isCompact.image (continuous_inv.mul continuous_const)).isClosed
    have h1A : (1 : G) ∉ A := by
      rintro ⟨y, hyS, hyx⟩
      have hxy : x = y := by
        have h := congrArg (fun z : G => y * z) hyx
        simpa [mul_assoc] using h
      exact hxS (by simpa [hxy] using hyS)
    have hAcomplOpen : IsOpen (Aᶜ) := hAclosed.isOpen_compl
    have h1Acompl : (1 : G) ∈ Aᶜ := h1A
    rcases ProC.exists_openNormalSubgroup_sub_open_nhds_of_one
        (G := G) hAcomplOpen h1Acompl with ⟨U, hUA⟩
    rcases hx U with ⟨y, hyS, hyquot⟩
    have hyU : y⁻¹ * x ∈ (U : Subgroup G) :=
      QuotientGroup.eq.1 hyquot
    have hyA : y⁻¹ * x ∈ A := ⟨y, hyS, rfl⟩
    exact hUA hyU hyA

end ProCGroups

namespace ProCGroups.ProC

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace OpenNormalSubgroup

/-- Two elements of a profinite group are equal if all their open-normal quotient projections
agree. -/
theorem eq_of_forall_quotientProj_eq [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] {x y : G}
    (hxy : ∀ U : OpenNormalSubgroup G, quotientProj U x = quotientProj U y) :
    x = y := by
  by_contra hne
  have hdiff : x⁻¹ * y ≠ 1 := by
    intro h
    exact hne (inv_mul_eq_one.mp h)
  let W : Set G := ({x⁻¹ * y} : Set G)ᶜ
  have hW : IsOpen W := by
    simp only [isOpen_compl_iff, Set.finite_singleton, Set.Finite.isClosed, W]
  have h1W : (1 : G) ∈ W := by
    simpa [W] using hdiff.symm
  rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hW h1W with ⟨U, hUW⟩
  have hmem : x⁻¹ * y ∈ (U : Subgroup G) := by
    exact QuotientGroup.eq.1 (hxy U)
  exact hdiff <| by
    have hxW : x⁻¹ * y ∈ W := hUW hmem
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false, W] at hxW

end OpenNormalSubgroup

/--
If the image of y modulo an open normal subgroup lies in the image of H, then y lies in H
\(\sqcup\) U.
-/
theorem mem_sup_of_quotient_mk_mem_map
    {Q : Type u} [TopologicalSpace Q] [Group Q]
    (H : Subgroup Q) (U : OpenNormalSubgroup Q)
    {y : Q}
    (hy :
      QuotientGroup.mk' (U : Subgroup Q) y ∈
        H.map (QuotientGroup.mk' (U : Subgroup Q))) :
    y ∈ H ⊔ (U : Subgroup Q) := by
  rcases hy with ⟨h, hh, hhy⟩
  have hU : h⁻¹ * y ∈ (U : Subgroup Q) := by
    have hq : QuotientGroup.mk' (U : Subgroup Q) (h⁻¹ * y) = 1 := by
      calc
        QuotientGroup.mk' (U : Subgroup Q) (h⁻¹ * y)
            = (QuotientGroup.mk' (U : Subgroup Q) h)⁻¹ *
                QuotientGroup.mk' (U : Subgroup Q) y := by
                  simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
                    QuotientGroup.mk_inv]
        _ = (QuotientGroup.mk' (U : Subgroup Q) h)⁻¹ *
                QuotientGroup.mk' (U : Subgroup Q) h := by rw [← hhy]
        _ = 1 := by simp only [QuotientGroup.mk'_apply, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (N := (U : Subgroup Q)) (h⁻¹ * y)).1 hq
  exact
    (Subgroup.mem_sup_of_normal_right (s := H) (t := (U : Subgroup Q))).2
      ⟨h, hh, h⁻¹ * y, hU, by simp only [mul_inv_cancel_left]⟩

/-- Closed-subgroup membership can be checked after adjoining every open normal subgroup. -/
theorem mem_closedSubgroup_of_forall_openNormal_sup
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q]
    (H : ClosedSubgroup Q) {y : Q}
    (hy : ∀ U : OpenNormalSubgroup Q,
      y ∈ (H : Subgroup Q) ⊔ (U : Subgroup Q)) :
    y ∈ (H : Subgroup Q) := by
  have hEq := closedSubgroup_eq_sInf_open (G := Q) H
  rw [hEq]
  rw [Subgroup.mem_sInf]
  intro K hK
  let Kopen : OpenSubgroup Q := ⟨K, hK.1⟩
  let U : OpenNormalSubgroup Q := OpenNormalSubgroup.normalCore Kopen
  have hyU := hy U
  have hsup_le : (H : Subgroup Q) ⊔ (U : Subgroup Q) ≤ K := by
    refine sup_le hK.2 ?_
    exact OpenNormalSubgroup.normalCore_le Kopen
  exact hsup_le hyU

/-- The intersection of two open normal subgroups is open and normal. -/
def openNormalSubgroup_inf
    {Q : Type u} [TopologicalSpace Q] [Group Q]
    (U V : OpenNormalSubgroup Q) : OpenNormalSubgroup Q where
  toOpenSubgroup :=
    { toSubgroup := (U : Subgroup Q) ⊓ (V : Subgroup Q)
      isOpen' :=
        (ProCGroups.openNormalSubgroup_isOpen (G := Q) U).inter
          (ProCGroups.openNormalSubgroup_isOpen (G := Q) V) }
  isNormal' := by
    change ((U : Subgroup Q) ⊓ (V : Subgroup Q)).Normal
    infer_instance

/-- Cofinal separation from a closed subgroup by open normal subgroups. -/
theorem exists_openNormalSubgroup_le_not_mem_sup_closedSubgroup
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q]
    (H : ClosedSubgroup Q) {x : Q} (hx : x ∉ (H : Subgroup Q))
    (U : OpenNormalSubgroup Q) :
    ∃ W : OpenNormalSubgroup Q, (W : Subgroup Q) ≤ (U : Subgroup Q) ∧
      x ∉ (H : Subgroup Q) ⊔ (W : Subgroup Q) := by
  classical
  have hEq := closedSubgroup_eq_sInf_open (G := Q) H
  have hxInf :
      x ∉ sInf {N : Subgroup Q | IsOpen (N : Set Q) ∧ (H : Subgroup Q) ≤ N} := by
    simpa [← hEq] using hx
  rw [Subgroup.mem_sInf] at hxInf
  push Not at hxInf
  rcases hxInf with ⟨N, hN, hxN⟩
  let Nopen : OpenSubgroup Q := ⟨N, hN.1⟩
  let Ncore : OpenNormalSubgroup Q := OpenNormalSubgroup.normalCore Nopen
  let W : OpenNormalSubgroup Q := openNormalSubgroup_inf Ncore U
  refine ⟨W, ?_, ?_⟩
  · intro y hy
    exact hy.2
  · intro hxSup
    have hsup_le_N : (H : Subgroup Q) ⊔ (W : Subgroup Q) ≤ N := by
      refine sup_le hN.2 ?_
      intro y hy
      exact OpenNormalSubgroup.normalCore_le Nopen hy.1
    exact hxN (hsup_le_N hxSup)

/-- The open normal subgroup K \(\sqcup\) U, where K is normal and U is open normal. -/
def openNormalSubgroup_sup_normal
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (K : Subgroup Q) [K.Normal] (U : OpenNormalSubgroup Q) :
    OpenNormalSubgroup Q where
  toOpenSubgroup :=
    { toSubgroup := K ⊔ (U : Subgroup Q)
      isOpen' :=
        Subgroup.isOpen_of_openSubgroup (K ⊔ (U : Subgroup Q))
          (show (U : Subgroup Q) ≤ K ⊔ (U : Subgroup Q) from le_sup_right) }
  isNormal' := by
    change (K ⊔ (U : Subgroup Q)).Normal
    infer_instance

/--
The cofinal quotient condition obtained from a separation statement and finite-stage cyclic
containment on quotients where \(x^n\) remains nontrivial modulo \(K\).
-/
theorem cofinal_openNormal_cyclic_containment_of_finite_lift
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q]
    (x : Q) (n : ℤ) (K : Subgroup Q) [K.Normal] (hKclosed : IsClosed (K : Set Q))
    (hnotK : x ^ n ∉ K)
    (hfinite : ∀ W : OpenNormalSubgroup Q,
      x ^ n ∉ K ⊔ (W : Subgroup Q) →
        let V : OpenNormalSubgroup Q := openNormalSubgroup_sup_normal K W
        ∀ y : Q, y ∈ ProCGroups.GroupTheory.centralizerOf (x ^ n) →
          QuotientGroup.mk' (V : Subgroup Q) y ∈
            ((ProCGroups.Generation.closedSubgroupGenerated (G := Q) ({x} : Set Q) :
              ClosedSubgroup Q) :
              Subgroup Q).map (QuotientGroup.mk' (V : Subgroup Q))) :
    ∀ U : OpenNormalSubgroup Q,
      ∃ W : OpenNormalSubgroup Q, (W : Subgroup Q) ≤ (U : Subgroup Q) ∧
        let V : OpenNormalSubgroup Q := openNormalSubgroup_sup_normal K W
        ∀ y : Q, y ∈ ProCGroups.GroupTheory.centralizerOf (x ^ n) →
          QuotientGroup.mk' (V : Subgroup Q) y ∈
            ((ProCGroups.Generation.closedSubgroupGenerated (G := Q) ({x} : Set Q) :
              ClosedSubgroup Q) :
              Subgroup Q).map (QuotientGroup.mk' (V : Subgroup Q)) := by
  intro U
  let Kclosed : ClosedSubgroup Q := ⟨K, hKclosed⟩
  rcases
      exists_openNormalSubgroup_le_not_mem_sup_closedSubgroup
        (H := Kclosed) hnotK U with
    ⟨W, hWU, hnotW⟩
  refine ⟨W, hWU, ?_⟩
  change x ^ n ∉ K ⊔ (W : Subgroup Q) at hnotW
  exact hfinite W hnotW

/--
Cofinal image criterion for bounding a centralizer by a cyclic subgroup joined with a closed
normal subgroup.
-/
theorem centralizerOf_zpow_le_cyclic_join_closedNormal_of_cofinal_openNormal_image
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (x : Q) (n : ℤ) (K : Subgroup Q) [K.Normal] (hKclosed : IsClosed (K : Set Q))
    (himage : ∀ U : OpenNormalSubgroup Q,
      ∃ W : OpenNormalSubgroup Q, (W : Subgroup Q) ≤ (U : Subgroup Q) ∧
        let V : OpenNormalSubgroup Q := openNormalSubgroup_sup_normal K W
        ∀ y : Q, y ∈ ProCGroups.GroupTheory.centralizerOf (x ^ n) →
          QuotientGroup.mk' (V : Subgroup Q) y ∈
            ((ProCGroups.Generation.closedSubgroupGenerated (G := Q) ({x} : Set Q) :
              ClosedSubgroup Q) :
              Subgroup Q).map (QuotientGroup.mk' (V : Subgroup Q))) :
    ProCGroups.GroupTheory.centralizerOf (x ^ n) ≤
      ((ProCGroups.Generation.closedSubgroupGenerated (G := Q) ({x} : Set Q) :
        ClosedSubgroup Q) :
        Subgroup Q) ⊔ K := by
  let L : Subgroup Q :=
    ((ProCGroups.Generation.closedSubgroupGenerated (G := Q) ({x} : Set Q) :
      ClosedSubgroup Q) : Subgroup Q)
  let H : ClosedSubgroup Q :=
    ⟨L ⊔ K,
      Subgroup.isClosed_sup_of_normal L K
        (ProCGroups.Generation.closedSubgroupGenerated (G := Q) ({x} : Set Q)).isClosed'
        hKclosed⟩
  intro y hy
  apply mem_closedSubgroup_of_forall_openNormal_sup H
  intro U
  rcases himage U with ⟨W, hWU, hWimage⟩
  let V : OpenNormalSubgroup Q := openNormalSubgroup_sup_normal K W
  have hyVL :
      QuotientGroup.mk' (V : Subgroup Q) y ∈
        L.map (QuotientGroup.mk' (V : Subgroup Q)) := by
    simpa [L, V] using hWimage y hy
  have hySupV : y ∈ L ⊔ (V : Subgroup Q) :=
    mem_sup_of_quotient_mk_mem_map L V hyVL
  have hle : L ⊔ (V : Subgroup Q) ≤ (H : Subgroup Q) ⊔ (U : Subgroup Q) := by
    change L ⊔ (K ⊔ (W : Subgroup Q)) ≤ (L ⊔ K) ⊔ (U : Subgroup Q)
    refine sup_le ?_ ?_
    · exact (show L ≤ L ⊔ K from le_sup_left).trans le_sup_left
    · refine sup_le ?_ ?_
      · exact (show K ≤ L ⊔ K from le_sup_right).trans le_sup_left
      · exact hWU.trans le_sup_right
  exact hle hySupV

/--
Continuous homomorphisms into a profinite group are equal if they agree after every open-normal
finite quotient of the target.
-/
theorem continuousMonoidHom_ext_openNormalQuotients
    {A : Type u} [Group A] [TopologicalSpace A]
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    {φ ψ : A →ₜ* H}
    (h : ∀ U : OpenNormalSubgroup H,
      (OpenNormalSubgroup.quotientProj U).comp φ =
        (OpenNormalSubgroup.quotientProj U).comp ψ) :
    φ = ψ := by
  ext x
  exact OpenNormalSubgroup.eq_of_forall_quotientProj_eq (G := H)
    (fun U => by
      have hU := congrArg (fun f : A →ₜ* H ⧸ (U : Subgroup H) => f x) (h U)
      simpa using hU)

end ProCGroups.ProC
