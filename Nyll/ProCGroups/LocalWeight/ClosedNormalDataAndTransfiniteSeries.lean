/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Generation.WordProductsAndClosure
import Nyll.ProCGroups.LocalWeight.MetrizabilityAndQuotients

/-!
# Closed normal chains and local weight

This file constructs ordinal-indexed descending chains of closed normal
subgroups from local-weight bounds.  Successive quotients lie in a prescribed
finite-group class, and the resulting series recovers the corresponding
cardinal bound without external assumption packages.
-/

open Set
open TopologicalSpace
open Order
open scoped Cardinal
open scoped Topology Pointwise

namespace ProCGroups.LocalWeight

universe u

open ProCGroups.ProC ProCGroups.Generation
open ProCGroups.FiniteGeneration


section ClosedNormalSeriesStatements


section ClosedNormalData

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- A closed subgroup equipped with normality, for quotient constructions. -/
structure ClosedNormalSubgroupData extends ClosedSubgroup G where
  /-- The underlying closed subgroup is normal. -/
  normal' : toSubgroup.Normal

/-- Closed-normal-subgroup data coerces to its underlying closed subgroup. -/
instance instCoeClosedNormalSubgroupData : Coe (ClosedNormalSubgroupData G) (Subgroup G) where
  coe H := H.toSubgroup

/-- The closed-normal-subgroup datum constructed by mk has the stated underlying subgroup. -/
@[simp 900] theorem ClosedNormalSubgroupData.coe_mk
    (H : Subgroup G) (hHclosed : IsClosed (H : Set G)) (hHnormal : H.Normal) :
    ((⟨⟨H, hHclosed⟩, hHnormal⟩ : ClosedNormalSubgroupData G) : Subgroup G) = H :=
  rfl

/-- The closed-normal-subgroup data define a normal subgroup. -/
instance ClosedNormalSubgroupData.instNormal
    (H : ClosedNormalSubgroupData G) : H.toSubgroup.Normal :=
  H.normal'

/-- The subgroup packaged in closed-normal subgroup data is closed. -/
@[simp 900] theorem ClosedNormalSubgroupData.isClosed
    (H : ClosedNormalSubgroupData G) : IsClosed ((H : Subgroup G) : Set G) :=
  H.isClosed'

/-- The step quotient \(H/K\) for closed-normal subgroup chains. -/
abbrev ClosedNormalSubgroupData.stepQuotient
    (H K : ClosedNormalSubgroupData G) : Type u :=
  H.toSubgroup ⧸ (K.toSubgroup.subgroupOf H.toSubgroup)

end ClosedNormalData

section TransfiniteSeries

variable (C : FiniteGroupClass.{u})
variable (G : Type u) [Group G] [TopologicalSpace G]

/-- Transfinite closed normal series with finite-class step quotients. -/
structure TransfiniteClosedNormalSeries
    (C : FiniteGroupClass.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (μ : Ordinal) where
  /-- The closed normal subgroup at each ordinal stage. -/
  series : Ordinal → ClosedNormalSubgroupData G
  /-- The series starts at the whole group. -/
  top_eq : (series 0).toSubgroup = ⊤
  /-- The series reaches the trivial subgroup at stage \(\mu\). -/
  bot_eq : (series μ).toSubgroup = ⊥
  /-- The series is antitone up to its terminal stage \(\mu\). -/
  antitone' : ∀ ⦃lam ν : Ordinal⦄, lam ≤ ν → ν ≤ μ →
    (series ν).toSubgroup ≤ (series lam).toSubgroup
  /-- Every successor-step quotient before \(\mu\) belongs to the finite-group class \(C\). -/
  step_mem' : ∀ ⦃lam : Ordinal⦄, lam < μ →
    C (ClosedNormalSubgroupData.stepQuotient (G := G) (series lam) (series (succ lam)))
  /-- At a nonzero limit stage, the series is the intersection of all preceding stages. -/
  limit_eq_iInf' : ∀ ⦃lam : Ordinal⦄, lam ≤ μ → IsSuccLimit lam →
    (series lam).toSubgroup =
      iInf (fun ν : {ν : Ordinal // ν < lam} => (series ν.1).toSubgroup)

end TransfiniteSeries



end ClosedNormalSeriesStatements


/--
Successor-step lemma for transfinite closed-normal chains: a closed normal finite-index subgroup
of a closed subgroup is obtained by intersecting that subgroup with an open normal subgroup of
the ambient profinite group. The subgroup \(H\) is assumed closed in \(G\), and \(K\) is assumed
closed and normal in \(G\).
-/
theorem closed_normal_subgroup_eq_inter_openNormal_of_finite_index
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (H K : Subgroup G)
    (hKclosed : IsClosed (K : Set G)) [K.Normal] (hKH : K ≤ H)
    [Finite (H ⧸ K.subgroupOf H)] :
    ∃ V : OpenNormalSubgroup G, K = H ⊓ (V : Subgroup G) := by
  classical
  let : TotallyDisconnectedSpace (G ⧸ K) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal K hKclosed
  let ψ : H →* G ⧸ K := (QuotientGroup.mk' K).comp H.subtype
  have hKerEq : (K.subgroupOf H) = ψ.ker := by
    ext x
    constructor
    · intro hx
      simpa [MonoidHom.mem_ker, ψ] using
        (QuotientGroup.eq_one_iff (N := K) x.1).2 hx
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := K) x.1).1
        (by simpa [MonoidHom.mem_ker, ψ] using hx)
  let e₁ : H ⧸ (K.subgroupOf H) ≃* H ⧸ ψ.ker :=
    QuotientGroup.quotientMulEquivOfEq hKerEq
  let : Finite (H ⧸ ψ.ker) := Finite.of_injective e₁.symm e₁.symm.injective
  let e₂ : H ⧸ ψ.ker ≃* ψ.range := QuotientGroup.quotientKerEquivRange ψ
  let : Finite ψ.range := Finite.of_injective e₂.symm e₂.symm.injective
  obtain ⟨W, hWbot⟩ :=
    exists_openNormalSubgroup_inf_eq_bot_of_finite (G := G ⧸ K) ψ.range
  let V : OpenNormalSubgroup G :=
    OpenNormalSubgroup.comap (QuotientGroup.mk' K) QuotientGroup.continuous_mk W
  refine ⟨V, ?_⟩
  ext x
  constructor
  · intro hxK
    refine ⟨hKH hxK, ?_⟩
    change QuotientGroup.mk' K x ∈ W
    have hmk : QuotientGroup.mk' K x = 1 :=
      (QuotientGroup.eq_one_iff (N := K) x).2 hxK
    rw [hmk]
    exact W.one_mem
  · intro hx
    have hxW : QuotientGroup.mk' K x ∈ W := by
      have hxV := hx.2
      change QuotientGroup.mk' K x ∈ W.toOpenSubgroup at hxV
      exact hxV
    have hxRange : QuotientGroup.mk' K x ∈ ψ.range := by
      exact ⟨⟨x, hx.1⟩, rfl⟩
    have hxBot : QuotientGroup.mk' K x ∈ (⊥ : Subgroup (G ⧸ K)) := by
      have hxInf : QuotientGroup.mk' K x ∈ ((W : Subgroup (G ⧸ K)) ⊓ ψ.range) :=
        ⟨hxW, hxRange⟩
      simpa [hWbot] using hxInf
    have hxOne : QuotientGroup.mk' K x = 1 := by
      simpa using hxBot
    exact (QuotientGroup.eq_one_iff (N := K) x).1 hxOne

/--
If a quotient carries a neighborhood basis indexed by a family of open normal subgroups, then
its local weight is bounded by the cardinality of that family.
-/
theorem localWeight_le_of_openNormal_family
    (G : Type u) [Group G] [TopologicalSpace G]
    {ι : Type u} {κ : Cardinal.{u}} (W : ι → OpenNormalSubgroup G)
    (hWbasis : IsNeighborhoodBasisAt (X := G) (1 : G)
      (Set.range fun i : ι => (((W i : Subgroup G) : Set G))))
    (hWcard : Cardinal.mk ι ≤ κ) : localWeight G ≤ κ := by
  classical
  let f : ι → Set G := fun i => (((W i : Subgroup G) : Set G))
  let chooseIdx : { V : Set G // V ∈ Set.range f } → ι :=
    fun V => Classical.choose V.2
  have hchoose : ∀ V : { V : Set G // V ∈ Set.range f }, f (chooseIdx V) = V.1 := by
    intro V
    exact Classical.choose_spec V.2
  have hchoose_inj : Function.Injective chooseIdx := by
    intro V₁ V₂ hEq
    apply Subtype.ext
    calc
      V₁.1 = f (chooseIdx V₁) := (hchoose V₁).symm
      _ = f (chooseIdx V₂) := by simp only [hEq]
      _ = V₂.1 := hchoose V₂
  simpa [localWeight] using
  calc
    localWeightAt (X := G) (1 : G) ≤ familyCardinal (X := G) (Set.range f) :=
      localWeightAt_le_familyCardinal_of_basis (X := G) (x := (1 : G)) hWbasis
    _ ≤ Cardinal.mk ι := by
      unfold familyCardinal
      exact Cardinal.mk_le_of_injective (f := chooseIdx) hchoose_inj
    _ ≤ κ := hWcard

/-- 6.5(d). Weight splitting formula over a closed normal subgroup. -/
theorem localWeight_split_over_closedNormalSubgroup
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (H : ClosedNormalSubgroupData G)
    (hInf : Infinite ↥H.toSubgroup ∨ Infinite (G ⧸ H.toSubgroup)) :
    localWeight G =
      localWeight ↥H.toSubgroup + quotientLocalWeight (G := G) H.toSubgroup := by
  classical
  let : CompactSpace ↥H.toSubgroup := by
    simpa using H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let : IsClosed (H.toSubgroup : Set G) := H.isClosed
  let : TotallyDisconnectedSpace (G ⧸ H.toSubgroup) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal H.toSubgroup H.isClosed
  rcases exists_openNormalNeighborhoodBasisAtOne_cardinal_le_localWeight
      (G := G) with ⟨ιG, WG, hWGbasis, hWGcard⟩
  have hHle : localWeight ↥H.toSubgroup ≤ localWeight G := by
    let WH : ιG → OpenNormalSubgroup ↥H.toSubgroup := fun i =>
      OpenNormalSubgroup.comap H.toSubgroup.subtype continuous_subtype_val (WG i)
    have hWHbasis :
        IsNeighborhoodBasisAt (X := ↥H.toSubgroup) (1 : ↥H.toSubgroup)
          (Set.range fun i : ιG => (((WH i : Subgroup ↥H.toSubgroup) : Set ↥H.toSubgroup))) := by
      refine ⟨?_, ?_⟩
      · intro U hU
        rcases hU with ⟨i, rfl⟩
        constructor
        · change IsOpen (((↑) : H.toSubgroup → G) ⁻¹' (((WG i : Subgroup G) : Set G)))
          simpa using
            (openNormalSubgroup_isOpen (G := G) (WG i)).preimage continuous_subtype_val
        · exact (WH i).one_mem'
      · intro U hUopen hUone
        rcases isOpen_induced_iff.mp hUopen with ⟨O, hOopen, hOeq⟩
        have hOone : (1 : G) ∈ O := by
          have : (1 : ↥H.toSubgroup) ∈ Subtype.val ⁻¹' O := by
            simpa [hOeq] using hUone
          simpa using this
        rcases hWGbasis.2 O hOopen hOone with ⟨V, hVrange, hVsub⟩
        rcases hVrange with ⟨i, rfl⟩
        refine ⟨_, ⟨i, rfl⟩, ?_⟩
        intro x hx
        have hxO : (x : G) ∈ O := hVsub hx
        rw [← hOeq]
        exact hxO
    exact localWeight_le_of_openNormal_family
      (G := ↥H.toSubgroup) WH hWHbasis hWGcard
  have hQle : quotientLocalWeight (G := G) H.toSubgroup ≤ localWeight G := by
    let q : G →* G ⧸ H.toSubgroup := QuotientGroup.mk' H.toSubgroup
    let BQ : Set (Set (G ⧸ H.toSubgroup)) :=
      Set.range fun i : ιG => q '' (((WG i : Subgroup G) : Set G))
    have hBQbasis :
        IsNeighborhoodBasisAt (X := G ⧸ H.toSubgroup) (1 : G ⧸ H.toSubgroup) BQ := by
      refine ⟨?_, ?_⟩
      · intro U hU
        rcases hU with ⟨i, rfl⟩
        constructor
        · exact (QuotientGroup.isOpenMap_coe (N := H.toSubgroup)) _
            (openNormalSubgroup_isOpen (G := G) (WG i))
        · refine ⟨1, ?_, ?_⟩
          · exact (WG i).one_mem'
          · simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_one, q]
      · intro U hUopen hUone
        have hpreOpen : IsOpen (q ⁻¹' U) := hUopen.preimage QuotientGroup.continuous_mk
        have hpreOne : (1 : G) ∈ q ⁻¹' U := by
          simpa [q] using hUone
        rcases hWGbasis.2 (q ⁻¹' U) hpreOpen hpreOne with ⟨V, hVrange, hVsub⟩
        rcases hVrange with ⟨i, rfl⟩
        refine ⟨q '' (((WG i : Subgroup G) : Set G)), ⟨i, rfl⟩, ?_⟩
        rintro _ ⟨g, hg, rfl⟩
        exact hVsub hg
    let chooseIdx : { U : Set (G ⧸ H.toSubgroup) // U ∈ BQ } → ιG :=
      fun U => Classical.choose U.2
    have hchoose :
        ∀ U : { U : Set (G ⧸ H.toSubgroup) // U ∈ BQ },
          q '' (((WG (chooseIdx U) : Subgroup G) : Set G)) = U.1 := by
      intro U
      exact Classical.choose_spec U.2
    have hchoose_inj : Function.Injective chooseIdx := by
      intro U₁ U₂ hEq
      apply Subtype.ext
      calc
        U₁.1 = q '' (((WG (chooseIdx U₁) : Subgroup G) : Set G)) := (hchoose U₁).symm
        _ = q '' (((WG (chooseIdx U₂) : Subgroup G) : Set G)) := by simp only [hEq,
            OpenSubgroup.coe_toSubgroup]
        _ = U₂.1 := hchoose U₂
    have hBQcard : familyCardinal (X := G ⧸ H.toSubgroup) BQ ≤ Cardinal.mk ιG := by
      unfold familyCardinal
      exact Cardinal.mk_le_of_injective (f := chooseIdx) hchoose_inj
    simpa [localWeight, quotientLocalWeight] using
      (localWeightAt_le_familyCardinal_of_basis
        (X := G ⧸ H.toSubgroup) (x := (1 : G ⧸ H.toSubgroup)) hBQbasis).trans
        (hBQcard.trans hWGcard)
  rcases exists_openNormalNeighborhoodBasisAtOne_cardinal_le_localWeight
      (G := ↥H.toSubgroup) with ⟨ιH, KH, hKHbasis, hKHcard⟩
  rcases exists_openNormalNeighborhoodBasisAtOne_cardinal_le_localWeight
      (G := G ⧸ H.toSubgroup) with ⟨ιQ, QH, hQHbasis, hQHcard0⟩
  have hQHcard : Cardinal.mk ιQ ≤ quotientLocalWeight (G := G) H.toSubgroup := by
    simpa [quotientLocalWeight_eq_localWeight] using hQHcard0
  have hιHne : Nonempty ιH := by
    rcases hKHbasis.2 Set.univ isOpen_univ (by simp only [mem_univ]) with ⟨U, hUrange, _⟩
    rcases hUrange with ⟨i, rfl⟩
    exact ⟨i⟩
  have hιQne : Nonempty ιQ := by
    rcases hQHbasis.2 Set.univ isOpen_univ (by simp only [mem_univ]) with ⟨U, hUrange, _⟩
    rcases hUrange with ⟨i, rfl⟩
    exact ⟨i⟩
  have hAmbientData :
      ∀ i : ιH, ∃ O V : Set G,
        IsOpen O ∧
        (((↑) : H.toSubgroup → G) ⁻¹' O) = (((KH i : Subgroup ↥H.toSubgroup) : Set ↥H.toSubgroup)) ∧
        IsOpen V ∧ (1 : G) ∈ V ∧
        ∀ {a b : G}, a ∈ V → b ∈ V → a⁻¹ * b ∈ O := by
    intro i
    rcases isOpen_induced_iff.mp (openNormalSubgroup_isOpen (G := ↥H.toSubgroup) (KH i)) with
      ⟨O, hOopen, hOeq⟩
    have hOone : (1 : G) ∈ O := by
      have : (1 : ↥H.toSubgroup) ∈ Subtype.val ⁻¹' O := by
        rw [hOeq]
        exact (KH i).one_mem'
      exact this
    have hOmem : O ∈ 𝓝 (1 : G) := hOopen.mem_nhds hOone
    have hcont :
        Continuous fun p : G × G => p.1⁻¹ * p.2 :=
      (continuous_inv.comp continuous_fst).mul continuous_snd
    have hmem :
        {p : G × G | p.1⁻¹ * p.2 ∈ O} ∈ 𝓝 ((1 : G), (1 : G)) := by
      exact hcont.continuousAt (by simpa using hOmem)
    rcases mem_nhds_prod_iff.mp hmem with ⟨A, hA, B, hB, hAB⟩
    rcases mem_nhds_iff.mp hA with ⟨A', hA'sub, hA'open, hA'one⟩
    rcases mem_nhds_iff.mp hB with ⟨B', hB'sub, hB'open, hB'one⟩
    refine ⟨O, A' ∩ B', hOopen, hOeq, hA'open.inter hB'open, ?_, ?_⟩
    · exact ⟨hA'one, hB'one⟩
    · intro a b ha hb
      have haA : a ∈ A := hA'sub ha.1
      have hbB : b ∈ B := hB'sub hb.2
      exact hAB (show (a, b) ∈ A ×ˢ B from ⟨haA, hbB⟩)
  choose OH VH hOHopen hOHeq hVHopen hVHone hVHdiff using hAmbientData
  let q : G →* G ⧸ H.toSubgroup := QuotientGroup.mk' H.toSubgroup
  let PH : ιQ → OpenNormalSubgroup G := fun j =>
    OpenNormalSubgroup.comap q QuotientGroup.continuous_mk (QH j)
  let B : Set (Set G) :=
    Set.range fun ij : ιH × ιQ => VH ij.1 ∩ (((PH ij.2 : Subgroup G) : Set G))
  have hBbasis : IsNeighborhoodBasisAt (X := G) (1 : G) B := by
    refine ⟨?_, ?_⟩
    · intro U hU
      rcases hU with ⟨⟨i, j⟩, rfl⟩
      constructor
      · exact (hVHopen i).inter (openNormalSubgroup_isOpen (G := G) (PH j))
      · exact ⟨hVHone i, (PH j).one_mem'⟩
    · intro U hUopen hUone
      rcases hWGbasis.2 U hUopen hUone with ⟨Nset, hNrange, hNsubU⟩
      rcases hNrange with ⟨n, rfl⟩
      have hHNopen :
          IsOpen (((↑) : H.toSubgroup → G) ⁻¹' (((WG n : Subgroup G) : Set G))) := by
        simpa using (openNormalSubgroup_isOpen (G := G) (WG n)).preimage continuous_subtype_val
      have hHNone :
          (1 : H.toSubgroup) ∈
            ((↑) : H.toSubgroup → G) ⁻¹' (((WG n : Subgroup G) : Set G)) := by
        simp only [OpenSubgroup.coe_toSubgroup, mem_preimage, OneMemClass.coe_one,
            SetLike.mem_coe, one_mem]
      rcases hKHbasis.2
          (((↑) : H.toSubgroup → G) ⁻¹' (((WG n : Subgroup G) : Set G)))
          hHNopen hHNone with ⟨Kset, hKrange, hKsub⟩
      rcases hKrange with ⟨i, rfl⟩
      have hImageOpen :
          IsOpen (((↑) : G → G ⧸ H.toSubgroup) '' ((((WG n : Subgroup G) : Set G) ∩ VH i))) := by
        exact (QuotientGroup.isOpenMap_coe (N := H.toSubgroup)) _
          ((openNormalSubgroup_isOpen (G := G) (WG n)).inter (hVHopen i))
      have hImageOne :
          (1 : G ⧸ H.toSubgroup) ∈
            ((↑) : G → G ⧸ H.toSubgroup) '' ((((WG n : Subgroup G) : Set G) ∩ VH i)) := by
        refine ⟨1, ?_, by simp only [QuotientGroup.mk_one]⟩
        exact ⟨(WG n).one_mem', hVHone i⟩
      rcases hQHbasis.2
          (((↑) : G → G ⧸ H.toSubgroup) '' ((((WG n : Subgroup G) : Set G) ∩ VH i)))
          hImageOpen hImageOne with ⟨Qset, hQrange, hQsub⟩
      rcases hQrange with ⟨j, rfl⟩
      refine ⟨VH i ∩ (((PH j : Subgroup G) : Set G)), ⟨(i, j), rfl⟩, ?_⟩
      intro x hx
      have hxV : x ∈ VH i := hx.1
      have hxQ : q x ∈ ((QH j : Subgroup (G ⧸ H.toSubgroup)) : Set (G ⧸ H.toSubgroup)) := by
        exact (OpenSubgroup.mem_comap
          (H := (QH j).toOpenSubgroup) (f := q)
          (hf := QuotientGroup.continuous_mk) (x := x)).1 hx.2
      rcases hQsub hxQ with ⟨y, hy, hyEq⟩
      have hyN : y ∈ ((WG n : Subgroup G) : Set G) := hy.1
      have hyV : y ∈ VH i := hy.2
      have hyxH : y⁻¹ * x ∈ H.toSubgroup := by
        exact (QuotientGroup.eq).1 (by simpa [q] using hyEq)
      have hyxO : y⁻¹ * x ∈ OH i := hVHdiff i hyV hxV
      have hyxK :
          (⟨y⁻¹ * x, hyxH⟩ : H.toSubgroup) ∈
            ((KH i : Subgroup ↥H.toSubgroup) : Set ↥H.toSubgroup) := by
        rw [← hOHeq i]
        exact hyxO
      have hyxN : y⁻¹ * x ∈ ((WG n : Subgroup G) : Set G) := hKsub hyxK
      have hxN : x ∈ ((WG n : Subgroup G) : Set G) := by
        have hxeq : x = y * (y⁻¹ * x) := by simp only [mul_inv_cancel_left]
        rw [hxeq]
        exact (WG n).mul_mem hyN hyxN
      exact hNsubU hxN
  let chooseIdx : { U : Set G // U ∈ B } → ιH × ιQ :=
    fun U => Classical.choose U.2
  have hchoose :
      ∀ U : { U : Set G // U ∈ B },
        VH (chooseIdx U).1 ∩ (((PH (chooseIdx U).2 : Subgroup G) : Set G)) = U.1 := by
    intro U
    exact Classical.choose_spec U.2
  have hchoose_inj : Function.Injective chooseIdx := by
    intro U₁ U₂ hEq
    apply Subtype.ext
    calc
      U₁.1 = VH (chooseIdx U₁).1 ∩ (((PH (chooseIdx U₁).2 : Subgroup G) : Set G)) :=
        (hchoose U₁).symm
      _ = VH (chooseIdx U₂).1 ∩ (((PH (chooseIdx U₂).2 : Subgroup G) : Set G)) := by
        simp only [hEq, OpenSubgroup.coe_toSubgroup]
      _ = U₂.1 := hchoose U₂
  have hBcard :
      familyCardinal (X := G) B ≤ Cardinal.mk (ιH × ιQ) := by
    unfold familyCardinal
    exact Cardinal.mk_le_of_injective (f := chooseIdx) hchoose_inj
  have hProdLe :
      Cardinal.mk (ιH × ιQ) ≤
        localWeight ↥H.toSubgroup + quotientLocalWeight (G := G) H.toSubgroup := by
    have hιHnz : Cardinal.mk ιH ≠ 0 :=
      Cardinal.mk_ne_zero_iff.mpr hιHne
    have hιQnz : Cardinal.mk ιQ ≠ 0 :=
      Cardinal.mk_ne_zero_iff.mpr hιQne
    cases hInf with
    | inl hHinf =>
        have hHaleph :
            ℵ₀ ≤ localWeight ↥H.toSubgroup :=
          aleph0_le_localWeight_of_infinite_profiniteGroup (G := ↥H.toSubgroup)
        calc
          Cardinal.mk (ιH × ιQ) = Cardinal.mk ιH * Cardinal.mk ιQ := by
            rw [Cardinal.mk_prod]
            simp only [Cardinal.lift_id]
          _ ≤ localWeight ↥H.toSubgroup * Cardinal.mk ιQ := by
            exact mul_le_mul' hKHcard le_rfl
          _ = max (localWeight ↥H.toSubgroup) (Cardinal.mk ιQ) := by
            exact Cardinal.mul_eq_max_of_aleph0_le_left hHaleph hιQnz
          _ ≤ max (localWeight ↥H.toSubgroup) (quotientLocalWeight (G := G) H.toSubgroup) := by
            exact max_le_max le_rfl hQHcard
          _ = localWeight ↥H.toSubgroup + quotientLocalWeight (G := G) H.toSubgroup := by
            symm
            exact Cardinal.add_eq_max hHaleph
    | inr hQinf =>
        have hQaleph :
            ℵ₀ ≤ quotientLocalWeight (G := G) H.toSubgroup := by
          simpa [quotientLocalWeight_eq_localWeight] using
            aleph0_le_localWeight_of_infinite_profiniteGroup
              (G := G ⧸ H.toSubgroup)
        calc
          Cardinal.mk (ιH × ιQ) = Cardinal.mk ιH * Cardinal.mk ιQ := by
            rw [Cardinal.mk_prod]
            simp only [Cardinal.lift_id]
          _ ≤ Cardinal.mk ιH * quotientLocalWeight (G := G) H.toSubgroup := by
            exact mul_le_mul' le_rfl hQHcard
          _ = max (Cardinal.mk ιH) (quotientLocalWeight (G := G) H.toSubgroup) := by
            exact Cardinal.mul_eq_max_of_aleph0_le_right hιHnz hQaleph
          _ ≤ max (localWeight ↥H.toSubgroup) (quotientLocalWeight (G := G) H.toSubgroup) := by
            exact max_le_max hKHcard le_rfl
          _ = localWeight ↥H.toSubgroup + quotientLocalWeight (G := G) H.toSubgroup := by
            symm
            exact Cardinal.add_eq_max' hQaleph
  have hUpper :
      localWeight G ≤
        localWeight ↥H.toSubgroup + quotientLocalWeight (G := G) H.toSubgroup := by
    simpa [localWeight] using
      (localWeightAt_le_familyCardinal_of_basis (X := G) (x := (1 : G)) hBbasis).trans
        (hBcard.trans hProdLe)
  have hLower :
      localWeight ↥H.toSubgroup + quotientLocalWeight (G := G) H.toSubgroup ≤ localWeight G := by
    cases hInf with
    | inl hHinf =>
        have hHaleph :
            ℵ₀ ≤ localWeight ↥H.toSubgroup :=
          aleph0_le_localWeight_of_infinite_profiniteGroup (G := ↥H.toSubgroup)
        rw [Cardinal.add_eq_max hHaleph]
        exact max_le_iff.mpr ⟨hHle, hQle⟩
    | inr hQinf =>
        have hQaleph :
            ℵ₀ ≤ quotientLocalWeight (G := G) H.toSubgroup := by
          simpa [quotientLocalWeight_eq_localWeight] using
            aleph0_le_localWeight_of_infinite_profiniteGroup
              (G := G ⧸ H.toSubgroup)
        rw [Cardinal.add_eq_max' hQaleph]
        exact max_le_iff.mpr ⟨hHle, hQle⟩
  exact le_antisymm hUpper hLower

/-- Subadditivity of quotient local weight along a chain \(H \le K \le M\). -/
theorem quotientLocalWeight_subadd_of_subgroup_chain
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H M K : ClosedNormalSubgroupData G)
    (hHK : H.toSubgroup ≤ K.toSubgroup) :
    quotientLocalWeight (G := ↥M.toSubgroup) (K.toSubgroup.subgroupOf M.toSubgroup) ≤
      quotientLocalWeight (G := ↥M.toSubgroup) (H.toSubgroup.subgroupOf M.toSubgroup) +
      quotientLocalWeight (G := ↥K.toSubgroup) (H.toSubgroup.subgroupOf K.toSubgroup) := by
  let HM : Subgroup ↥M.toSubgroup := H.toSubgroup.subgroupOf M.toSubgroup
  let KM : Subgroup ↥M.toSubgroup := K.toSubgroup.subgroupOf M.toSubgroup
  have hHMK : HM ≤ KM := by
    intro x hx
    exact hHK hx
  have hopen :
      IsOpenMap (leftQuotientProjection HM KM hHMK : (↥M.toSubgroup ⧸ HM) → (↥M.toSubgroup ⧸ KM)) :=
      by
    intro U hU
    have hpre :
        IsOpen ((QuotientGroup.mk (s := HM)) ⁻¹' U) := by
      exact ((QuotientGroup.isQuotientMap_mk HM).isOpen_preimage).2 hU
    have himage :
        leftQuotientProjection HM KM hHMK '' U =
          (QuotientGroup.mk (s := KM)) '' ((QuotientGroup.mk (s := HM)) ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨x, hxU, rfl⟩
        revert hxU
        refine Quotient.inductionOn x ?_
        intro g hgU
        refine ⟨g, hgU, ?_⟩
        simp only [leftQuotientProjection_mk]
      · rintro ⟨g, hgU, rfl⟩
        refine ⟨QuotientGroup.mk (s := HM) g, hgU, ?_⟩
        simp only [leftQuotientProjection_mk]
    rw [himage]
    exact (QuotientGroup.isOpenMap_coe (N := KM)) _ hpre
  have hmon :
      quotientLocalWeight (G := ↥M.toSubgroup) (K.toSubgroup.subgroupOf M.toSubgroup) ≤
        quotientLocalWeight (G := ↥M.toSubgroup) (H.toSubgroup.subgroupOf M.toSubgroup) := by
    have hle :=
      localWeightAt_image_le_of_continuous_open
        (X := (↥M.toSubgroup ⧸ HM)) (Y := (↥M.toSubgroup ⧸ KM))
        (x := (1 : ↥M.toSubgroup ⧸ HM))
        (f := leftQuotientProjection HM KM hHMK)
        (continuous_leftQuotientProjection HM KM hHMK) hopen
    have hmap_one :
        leftQuotientProjection HM KM hHMK (1 : ↥M.toSubgroup ⧸ HM) = 1 := by
      exact leftQuotientProjection_mk HM KM hHMK 1
    rw [hmap_one] at hle
    simpa [quotientLocalWeight, HM, KM] using hle
  exact hmon.trans (self_le_add_right _ _)

/--
Forward direction: existence of a transfinite closed normal series from the local-weight bound.
-/
theorem build_transfiniteClosedNormalSeries_of_localWeight_le
    (C : FiniteGroupClass.{u}) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (μ : Ordinal) (hForm : FiniteGroupClass.Formation C)
    (hNorm : FiniteGroupClass.NormalSubgroupClosed C) (hG : HasOpenNormalBasisInClass C G)
    (hμ : localWeight G ≤ μ.card) :
    Nonempty (TransfiniteClosedNormalSeries C G μ) := by
  classical
  let hIso : FiniteGroupClass.IsomClosed C :=
    FiniteGroupClass.Formation.isomClosed (C := C) hForm
  rcases exists_openNormalNeighborhoodBasisAtOne_inClass_cardinal_le_localWeight
      (C := C) (G := G) hG with
    ⟨ι, W, hWC, hWbasis, hWcard0⟩
  have hιne : Nonempty ι := by
    rcases hWbasis.2 Set.univ isOpen_univ (by simp only [mem_univ]) with ⟨U, hUrange, _⟩
    rcases hUrange with ⟨i, rfl⟩
    exact ⟨i⟩
  have hWcard : Cardinal.mk ι ≤ μ.card := hWcard0.trans hμ
  have hEmb : Nonempty (ι ↪ Set.Iio μ) := by
    have hWcardLift0 :
        Cardinal.lift.{u + 1} (Cardinal.mk ι) ≤ Cardinal.lift.{u + 1} μ.card := by
      exact (Cardinal.lift_le).2 hWcard
    have hWcardLift :
        Cardinal.lift.{u + 1} (Cardinal.mk ι) ≤ Cardinal.lift.{u} #(Set.Iio μ) := by
      simpa [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift] using hWcardLift0
    exact Cardinal.lift_mk_le'.mp hWcardLift
  let e : ι ↪ Set.Iio μ := Classical.choice hEmb
  let σ : Set.Iio μ → ι := Function.invFun e
  have hσ : ∀ i : ι, σ (e i) = i := by
    intro i
    exact Function.leftInverse_invFun e.injective i
  let Wμ : Set.Iio μ → OpenNormalSubgroup G := fun a => W (σ a)
  have hWμC : ∀ a : Set.Iio μ, C (G ⧸ (Wμ a : Subgroup G)) := by
    intro a
    exact hWC (σ a)
  let B : Set (Set G) := Set.range fun i : ι => (((W i : Subgroup G) : Set G))
  let Bμ : Set (Set G) := Set.range fun a : Set.Iio μ => (((Wμ a : Subgroup G) : Set G))
  have hBμeq : Bμ = B := by
    ext U
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨σ a, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp only [hσ i, OpenSubgroup.coe_toSubgroup, Wμ]⟩
  have hWμbasis : IsNeighborhoodBasisAt (X := G) (1 : G) Bμ := by
    simpa [Bμ, B, hBμeq] using hWbasis
  have hWμbot : iInf (fun a : Set.Iio μ => (Wμ a : Subgroup G)) = (⊥ : Subgroup G) := by
    simpa [Bμ] using
      iInf_eq_bot_of_openNormalNeighborhoodBasisAtOne (G := G) Wμ hWμbasis
  let seriesSub : Ordinal → Subgroup G := fun lam =>
    if hlam : lam ≤ μ then
      iInf (fun a : Set.Iio lam => (Wμ ⟨a.1, lt_of_lt_of_le a.2 hlam⟩ : Subgroup G))
    else ⊥
  have hseriesClosed : ∀ lam : Ordinal, IsClosed (seriesSub lam : Set G) := by
    intro lam
    by_cases hlam : lam ≤ μ
    · simpa [seriesSub, hlam] using
        isClosed_iInter (fun a : Set.Iio lam =>
          openNormalSubgroup_isClosed (G := G) (Wμ ⟨a.1, lt_of_lt_of_le a.2 hlam⟩))
    · dsimp [seriesSub]
      rw [dite_eq_right hlam]
      simp only [Subgroup.coe_bot, finite_singleton, Finite.isClosed]
  have hseriesNormal : ∀ lam : Ordinal, (seriesSub lam).Normal := by
    intro lam
    by_cases hlam : lam ≤ μ
    · simpa [seriesSub, hlam] using
        (show
          (iInf (fun a : Set.Iio lam =>
            (Wμ ⟨a.1, lt_of_lt_of_le a.2 hlam⟩ : Subgroup G))).Normal from
          Subgroup.normal_iInf_normal fun a : Set.Iio lam =>
            (show (Wμ ⟨a.1, lt_of_lt_of_le a.2 hlam⟩ : Subgroup G).Normal from inferInstance))
    · simp [seriesSub, hlam]
  let seriesData : Ordinal → ClosedNormalSubgroupData G := fun lam =>
    { toSubgroup := seriesSub lam
      isClosed' := hseriesClosed lam
      normal' := hseriesNormal lam }
  refine ⟨{
    series := seriesData,
    top_eq := ?_,
    bot_eq := ?_,
    antitone' := ?_,
    step_mem' := ?_,
    limit_eq_iInf' := ?_ }⟩
  · ext x
    simp only [zero_le, ↓reduceDIte, Subgroup.mem_iInf, OpenSubgroup.mem_toSubgroup,
        IsEmpty.forall_iff,
  Subgroup.mem_top, seriesSub, seriesData]
  · simpa [seriesData, seriesSub] using hWμbot
  · intro lam ν hlam hν x hx
    have hlamμ : lam ≤ μ := hlam.trans hν
    have hxall :
        ∀ a : Set.Iio ν, x ∈ (Wμ ⟨a.1, lt_of_lt_of_le a.2 hν⟩ : Subgroup G) := by
      simpa [seriesData, seriesSub, hν, Subgroup.mem_iInf] using hx
    have hrestrict :
        ∀ a : Set.Iio lam, x ∈ (Wμ ⟨a.1, lt_of_lt_of_le a.2 hlamμ⟩ : Subgroup G) := by
      intro a
      exact hxall ⟨a.1, lt_of_lt_of_le a.2 hlam⟩
    simpa [seriesData, seriesSub, hlamμ, Subgroup.mem_iInf] using hrestrict
  · intro lam hlam
    let H : ClosedNormalSubgroupData G := seriesData lam
    let K : ClosedNormalSubgroupData G := seriesData (succ lam)
    let U : OpenNormalSubgroup G := Wμ ⟨lam, hlam⟩
    let φ : H.toSubgroup →* G ⧸ (U : Subgroup G) :=
      (QuotientGroup.mk' (U : Subgroup G)).comp H.toSubgroup.subtype
    let L : Subgroup (G ⧸ (U : Subgroup G)) :=
      Subgroup.map (QuotientGroup.mk' (U : Subgroup G)) H.toSubgroup
    have hlamle : lam ≤ μ := hlam.le
    have hsuccle : succ lam ≤ μ := succ_le_of_lt hlam
    have hRangeEq : φ.range = L := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    let : L.Normal := by
      dsimp [L]
      exact Subgroup.Normal.map H.normal' (QuotientGroup.mk' (U : Subgroup G))
        (QuotientGroup.mk'_surjective (U : Subgroup G))
    have hKmem :
        ∀ {x : H.toSubgroup}, x.1 ∈ K.toSubgroup ↔ x.1 ∈ (U : Subgroup G) := by
      intro x
      constructor
      · intro hxK
        have hxall :
            ∀ a : Set.Iio (succ lam),
              x.1 ∈ (Wμ ⟨a.1, lt_of_lt_of_le a.2 hsuccle⟩ : Subgroup G) := by
          change x.1 ∈ seriesSub (succ lam) at hxK
          simp only [seriesSub, dite_eq_left hsuccle, Subgroup.mem_iInf] at hxK
          exact hxK
        simpa [U] using hxall ⟨lam, show lam ∈ Set.Iio (succ lam) from lt_succ lam⟩
      · intro hxU
        have hxH : x.1 ∈ H.toSubgroup := x.2
        have hxHall :
            ∀ a : Set.Iio lam,
              x.1 ∈ (Wμ ⟨a.1, lt_of_lt_of_le a.2 hlamle⟩ : Subgroup G) := by
          simpa [H, seriesData, seriesSub, hlamle, Subgroup.mem_iInf] using hxH
        have hxKall :
            ∀ a : Set.Iio (succ lam),
              x.1 ∈ (Wμ ⟨a.1, lt_of_lt_of_le a.2 hsuccle⟩ : Subgroup G) := by
            intro a
            rcases eq_or_lt_of_le (lt_succ_iff.mp (show a.1 < succ lam from a.2)) with haEq | ha
            · simpa [U, haEq] using hxU
            · exact hxHall ⟨a.1, show a.1 ∈ Set.Iio lam from ha⟩
        change x.1 ∈ seriesSub (succ lam)
        simp only [seriesSub, dite_eq_left hsuccle, Subgroup.mem_iInf]
        exact hxKall
    have hKerEq : K.toSubgroup.subgroupOf H.toSubgroup = φ.ker := by
      ext x
      constructor
      · intro hx
        have hxU : x.1 ∈ (U : Subgroup G) := by
          exact hKmem.1 (by simpa [Subgroup.mem_subgroupOf] using hx)
        simpa [MonoidHom.mem_ker, φ] using
          (QuotientGroup.eq_one_iff (N := (U : Subgroup G)) x.1).2 hxU
      · intro hx
        have hxU : x.1 ∈ (U : Subgroup G) := by
          exact (QuotientGroup.eq_one_iff (N := (U : Subgroup G)) x.1).1
            (by simpa [MonoidHom.mem_ker, φ] using hx)
        have hxK : x.1 ∈ K.toSubgroup := hKmem.2 hxU
        simpa [Subgroup.mem_subgroupOf] using hxK
    have hL : C L := hNorm L (hWμC ⟨lam, hlam⟩)
    have hStep : C (H.toSubgroup ⧸ K.toSubgroup.subgroupOf H.toSubgroup) := by
      let e₁ : H.toSubgroup ⧸ K.toSubgroup.subgroupOf H.toSubgroup ≃* H.toSubgroup ⧸ φ.ker :=
        QuotientGroup.quotientMulEquivOfEq hKerEq
      exact hIso
        ⟨(MulEquiv.subgroupCongr hRangeEq).symm.trans
          (e₁.trans (QuotientGroup.quotientKerEquivRange φ)).symm⟩
        hL
    simpa [ClosedNormalSubgroupData.stepQuotient, H, K] using hStep
  · intro lam hlam hLimit
    ext x
    constructor
    · intro hx
      have hxall :
          ∀ a : Set.Iio lam, x ∈ (Wμ ⟨a.1, lt_of_lt_of_le a.2 hlam⟩ : Subgroup G) := by
        simpa [seriesData, seriesSub, hlam, Subgroup.mem_iInf] using hx
      have hxseries : ∀ ν : Set.Iio lam, x ∈ (seriesData ν.1).toSubgroup := by
        intro ν
        have hνμ : ν.1 ≤ μ := ν.2.le.trans hlam
        have hrestrict :
            ∀ a : Set.Iio ν.1,
              x ∈ (Wμ ⟨a.1, lt_of_lt_of_le a.2 hνμ⟩ : Subgroup G) := by
          intro a
          exact hxall ⟨a.1, show a.1 < lam from lt_of_lt_of_le a.2 ν.2.le⟩
        simpa [seriesData, seriesSub, hνμ, Subgroup.mem_iInf] using hrestrict
      simpa [Subgroup.mem_iInf] using hxseries
    · intro hx
      have hxseries : ∀ ν : Set.Iio lam, x ∈ (seriesData ν.1).toSubgroup := by
        simpa [Subgroup.mem_iInf] using hx
      have hxall :
          ∀ a : Set.Iio lam, x ∈ (Wμ ⟨a.1, lt_of_lt_of_le a.2 hlam⟩ : Subgroup G) := by
        intro a
        have hs : succ a.1 < lam := hLimit.succ_lt a.2
        have hsμ : succ a.1 ≤ μ := hs.le.trans hlam
        have hxin : x ∈ (seriesData (succ a.1)).toSubgroup := hxseries ⟨succ a.1, hs⟩
        have hxsucc :
            ∀ b : Set.Iio (succ a.1),
              x ∈ (Wμ ⟨b.1, lt_of_lt_of_le b.2 hsμ⟩ : Subgroup G) := by
          change x ∈ seriesSub (succ a.1) at hxin
          simp only [seriesSub, dite_eq_left hsμ, Subgroup.mem_iInf] at hxin
          exact hxin
        simpa using hxsucc ⟨a.1, show a.1 ∈ Set.Iio (succ a.1) from lt_succ a.1⟩
      simpa [seriesData, seriesSub, hlam, Subgroup.mem_iInf] using hxall

end ProCGroups.LocalWeight
