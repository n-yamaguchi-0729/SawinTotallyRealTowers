import Mathlib.Topology.Algebra.ProperAction.Basic
import ProCGroups.ProC.Quotients.ClosedSubgroupNeighborhoods

set_option autoImplicit false

/-!
# Sections for quotients by open subgroups

Finite quotients by open subgroups admit normalized choice sections, which are continuous because
the quotient is discrete. This file records their right-inverse property and derives sections of
left-quotient projections with an open lower subgroup.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

variable {G : Type u} [Group G]

/--
A normalized set-theoretic section of the quotient map by an open subgroup. Since the quotient
is discrete, this section is automatically continuous.
-/
noncomputable def quotientOpenSubgroupSection (U : Subgroup G) :
    (G ⧸ U) → G := by
  classical
  intro q
  exact if hq : q = QuotientGroup.mk (s := U) (1 : G) then 1
    else Classical.choose (Quotient.exists_rep q)

/-- The normalized set-theoretic section sends the identity coset to the identity. -/
@[simp] theorem quotientOpenSubgroupSection_one
    (U : Subgroup G) :
    quotientOpenSubgroupSection U (QuotientGroup.mk (s := U) (1 : G)) = 1 := by
  classical
  simp only [quotientOpenSubgroupSection, ↓reduceDIte]

/-- The normalized section is a genuine right inverse to the quotient map. -/
theorem quotientOpenSubgroupSection_rightInverse
    (U : Subgroup G) :
    Function.RightInverse (quotientOpenSubgroupSection U)
      (QuotientGroup.mk (s := U)) := by
  classical
  intro q
  by_cases hq : q = QuotientGroup.mk (s := U) (1 : G)
  · subst hq
    simp only [quotientOpenSubgroupSection, ↓reduceDIte]
  · simpa [quotientOpenSubgroupSection, hq] using
      (Classical.choose_spec (Quotient.exists_rep q))

/-- The normalized section by an open subgroup is continuous because the quotient is discrete. -/
theorem continuous_quotientOpenSubgroupSection
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    Continuous (quotientOpenSubgroupSection U) := by
  let : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  exact continuous_of_discreteTopology

/--
Helper for the finite/open case: the canonical quotient map by an open normal subgroup of a
profinite group admits a continuous section normalized by \(s(1)=1\). The actual section data is
provided by quotientOpenSubgroupSection.
-/
theorem quotient_openNormalSubgroup_hasContinuousSection
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) :
    ∃ σ : (G ⧸ (U : Subgroup G)) → G,
      Continuous σ ∧
        Function.RightInverse σ (QuotientGroup.mk' (U : Subgroup G)) ∧
        σ 1 = 1 := by
  let hU : IsOpen ((U : Subgroup G) : Set G) := openNormalSubgroup_isOpen (G := G) U
  refine ⟨quotientOpenSubgroupSection (U : Subgroup G), ?_, ?_, ?_⟩
  · exact continuous_quotientOpenSubgroupSection (G := G) (U : Subgroup G) hU
  · intro q
    change QuotientGroup.mk (s := (U : Subgroup G))
      (quotientOpenSubgroupSection (U : Subgroup G) q) = q
    exact quotientOpenSubgroupSection_rightInverse (G := G) (U : Subgroup G) q
  · change quotientOpenSubgroupSection (U : Subgroup G)
      (QuotientGroup.mk (s := (U : Subgroup G)) (1 : G)) = 1
    exact quotientOpenSubgroupSection_one (G := G) (U : Subgroup G)

/-- Finite-index case of the section theorem for left quotient projections. -/
theorem leftQuotientProjection_hasContinuousSection_of_openSubgroup
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (K H : ClosedSubgroup G)
    (hKH : (K : Subgroup G) ≤ (H : Subgroup G))
    (hKopen : IsOpen (((K : Subgroup G).subgroupOf (H : Subgroup G)) : Set H)) :
    ∃ σ : G ⧸ (H : Subgroup G) → G ⧸ (K : Subgroup G),
    Continuous σ ∧
      Function.RightInverse σ
        (leftQuotientProjection (K : Subgroup G) (H : Subgroup G) hKH) ∧
      σ (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) =
        QuotientGroup.mk (s := (K : Subgroup G)) (1 : G) := by
  classical
  let : IsClosed (((H : ClosedSubgroup G) : Subgroup G) : Set G) := H.isClosed'
  let UH : OpenSubgroup H :=
    ⟨((K : Subgroup G).subgroupOf (H : Subgroup G)), hKopen⟩
  obtain ⟨V, hVHK⟩ :=
    exists_openNormalSubgroup_inter_closedSubgroup_le (G := G) H UH
  have hVcapHK : ((V : Subgroup G) ⊓ (H : Subgroup G)) ≤ (K : Subgroup G) := by
    intro x hx
    exact hVHK <| show (⟨x, hx.2⟩ : H) ∈
      (OpenNormalSubgroup.comap ((H : Subgroup G).subtype) continuous_subtype_val V : Subgroup H)
      by
        change x ∈ (V : Subgroup G)
        exact hx.1
  let J : Subgroup G := (H : Subgroup G) ⊔ (V : Subgroup G)
  have hHJ : (H : Subgroup G) ≤ J := le_sup_left
  have hKJ : (K : Subgroup G) ≤ J := hKH.trans hHJ
  have hJopen : IsOpen (J : Set G) := by
    exact Subgroup.isOpen_of_openSubgroup J (show (V : Subgroup G) ≤ J from le_sup_right)
  let ρ : G ⧸ J → G := quotientOpenSubgroupSection J
  have hρcont : Continuous ρ := continuous_quotientOpenSubgroupSection J hJopen
  have hρright : Function.RightInverse ρ (QuotientGroup.mk (s := J)) :=
    quotientOpenSubgroupSection_rightInverse J
  let WK : Set (G ⧸ (K : Subgroup G)) :=
    (QuotientGroup.mk (s := (K : Subgroup G))) ''
      ((((V : OpenNormalSubgroup G) : Subgroup G) : Set G))
  let BH : Set (G ⧸ (H : Subgroup G)) :=
    (QuotientGroup.mk (s := (H : Subgroup G))) ''
      ((((V : OpenNormalSubgroup G) : Subgroup G) : Set G))
  have hVclosed : IsClosed ((((V : OpenNormalSubgroup G) : Subgroup G) : Set G)) :=
    openNormalSubgroup_isClosed (G := G) V
  have hWKcompact : IsCompact WK := by
    exact hVclosed.isCompact.image (QuotientGroup.continuous_mk :
      Continuous (QuotientGroup.mk (s := (K : Subgroup G)) : G → G ⧸ (K : Subgroup G)))
  have hBHcompact : IsCompact BH := by
    exact hVclosed.isCompact.image (QuotientGroup.continuous_mk :
      Continuous (QuotientGroup.mk (s := (H : Subgroup G)) : G → G ⧸ (H : Subgroup G)))
  have hBHclosed : IsClosed BH := by
    exact hBHcompact.isClosed
  let πloc : WK → BH := fun x =>
    ⟨leftQuotientProjection (K : Subgroup G) (H : Subgroup G) hKH x.1, by
      rcases x with ⟨x, hx⟩
      rcases hx with ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩⟩
  have hπloc_continuous : Continuous πloc := by
    exact Continuous.subtype_mk
      ((continuous_leftQuotientProjection
        (K : Subgroup G) (H : Subgroup G) hKH).comp continuous_subtype_val)
      (by
        rintro ⟨x, hx⟩
        rcases hx with ⟨g, hg, rfl⟩
        exact ⟨g, hg, rfl⟩)
  have hπloc_bij : Function.Bijective πloc := by
    constructor
    · intro x y hxy
      rcases x with ⟨x, hx⟩
      rcases y with ⟨y, hy⟩
      rcases hx with ⟨gx, hgx, rfl⟩
      rcases hy with ⟨gy, hgy, rfl⟩
      apply Subtype.ext
      apply QuotientGroup.eq.2
      have hHmem : gx⁻¹ * gy ∈ (H : Subgroup G) := by
        exact QuotientGroup.eq.1 (congrArg Subtype.val hxy)
      have hVmem : gx⁻¹ * gy ∈ (V : Subgroup G) := by
        exact (V : Subgroup G).mul_mem ((V : Subgroup G).inv_mem hgx) hgy
      exact hVcapHK ⟨hVmem, hHmem⟩
    · intro y
      rcases y with ⟨y, hy⟩
      rcases hy with ⟨g, hg, rfl⟩
      refine ⟨⟨QuotientGroup.mk (s := (K : Subgroup G)) g, ⟨g, hg, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
  let : CompactSpace WK := isCompact_iff_compactSpace.mp hWKcompact
  let eTop : WK ≃ₜ BH :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective πloc hπloc_bij) hπloc_continuous
  let σB : BH → G ⧸ (K : Subgroup G) := fun y => (eTop.symm y).1
  have hσB_continuous : Continuous σB := continuous_subtype_val.comp eTop.continuous_invFun
  have hσB_right : ∀ y : BH,
      leftQuotientProjection (K : Subgroup G) (H : Subgroup G) hKH (σB y) = y.1 := by
    intro y
    exact congrArg Subtype.val (eTop.right_inv y)
  have hσB_one :
      σB ⟨QuotientGroup.mk (s := (H : Subgroup G)) (1 : G), ⟨1, V.one_mem', rfl⟩⟩ =
        QuotientGroup.mk (s := (K : Subgroup G)) (1 : G) := by
    let y0 : BH :=
      ⟨QuotientGroup.mk (s := (H : Subgroup G)) (1 : G), ⟨1, V.one_mem', rfl⟩⟩
    have hσB_mem : σB y0 ∈ WK := (eTop.symm y0).2
    have h1_mem : QuotientGroup.mk (s := (K : Subgroup G)) (1 : G) ∈ WK := ⟨1, V.one_mem', rfl⟩
    have hs : (⟨σB y0, hσB_mem⟩ : WK) =
        ⟨QuotientGroup.mk (s := (K : Subgroup G)) (1 : G), h1_mem⟩ := by
      apply hπloc_bij.1
      apply Subtype.ext
      simpa [πloc, y0] using hσB_right y0
    exact congrArg Subtype.val hs
  let c : G ⧸ (H : Subgroup G) → G ⧸ J :=
    leftQuotientProjection (H : Subgroup G) J hHJ
  have hc_continuous : Continuous c :=
    continuous_leftQuotientProjection (H : Subgroup G) J hHJ
  let r : G ⧸ (H : Subgroup G) → G := ρ ∘ c
  have hr_continuous : Continuous r := hρcont.comp hc_continuous
  let z : G ⧸ (H : Subgroup G) → BH := fun y =>
    ⟨(r y)⁻¹ • y, by
      rcases Quotient.exists_rep y with ⟨g, rfl⟩
      change
        QuotientGroup.mk (s := (H : Subgroup G))
            ((r (QuotientGroup.mk (s := (H : Subgroup G)) g))⁻¹ * g) ∈
          BH
      have hsame :
          QuotientGroup.mk (s := J) (r (QuotientGroup.mk (s := (H : Subgroup G)) g)) =
            QuotientGroup.mk (s := J) g := by
        simpa [r, c, Function.comp] using
          hρright (leftQuotientProjection (H : Subgroup G) J hHJ
            (QuotientGroup.mk (s := (H : Subgroup G)) g))
      have hmemJ :
          (r (QuotientGroup.mk (s := (H : Subgroup G)) g))⁻¹ * g ∈ J := by
        exact QuotientGroup.eq.1 hsame
      have hmemJ' :
          (r (QuotientGroup.mk (s := (H : Subgroup G)) g))⁻¹ * g ∈
            (H : Subgroup G) ⊔ (V : Subgroup G) := by
        simpa [J] using hmemJ
      have hmemJ'' :
          (r (QuotientGroup.mk (s := (H : Subgroup G)) g))⁻¹ * g ∈
            (V : Subgroup G) ⊔ (H : Subgroup G) := by
        simpa [sup_comm] using hmemJ'
      have hmemSet :
          (r (QuotientGroup.mk (s := (H : Subgroup G)) g))⁻¹ * g ∈
            ((V : Subgroup G) : Set G) * ((H : Subgroup G) : Set G) := by
        change (r (QuotientGroup.mk (s := (H : Subgroup G)) g))⁻¹ * g ∈
          (((V : Subgroup G) ⊔ (H : Subgroup G) : Subgroup G) : Set G) at hmemJ''
        rwa [Subgroup.normal_mul (V : Subgroup G) (H : Subgroup G)] at hmemJ''
      rcases hmemSet with ⟨v, hv, h, hh, hEq⟩
      refine ⟨v, hv, ?_⟩
      rw [← hEq]
      exact (QuotientGroup.mk_mul_of_mem v hh).symm⟩
  have hz_continuous : Continuous z := by
    exact Continuous.subtype_mk ((continuous_inv.comp hr_continuous).smul continuous_id) (by
      intro y
      exact (z y).2)
  let σ : G ⧸ (H : Subgroup G) → G ⧸ (K : Subgroup G) := fun y =>
    r y • σB (z y)
  have hσ_continuous : Continuous σ := by
    exact hr_continuous.smul (hσB_continuous.comp hz_continuous)
  refine ⟨σ, hσ_continuous, ?_, ?_⟩
  · intro y
    calc
      leftQuotientProjection (K : Subgroup G) (H : Subgroup G) hKH (σ y)
          = r y • leftQuotientProjection (K : Subgroup G) (H : Subgroup G) hKH (σB (z y)) := by
              simp only [leftQuotientProjection_smul, σ]
      _ = r y • (z y).1 := by rw [hσB_right]
      _ = y := by
            change r y • ((r y)⁻¹ • y) = y
            simp only [smul_smul, mul_inv_cancel, one_smul]
  · have hc_one :
        c (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) =
          QuotientGroup.mk (s := J) (1 : G) := rfl
    have hr_one : r (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) = 1 := by
      exact quotientOpenSubgroupSection_one J
    have hz_one :
        z (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) =
          ⟨QuotientGroup.mk (s := (H : Subgroup G)) (1 : G), ⟨1, V.one_mem', rfl⟩⟩ := by
      apply Subtype.ext
      simp only [hr_one, inv_one, one_smul, z]
    simp only [hr_one, hz_one, hσB_one, one_smul, σ]

end ProCGroups.ProC
