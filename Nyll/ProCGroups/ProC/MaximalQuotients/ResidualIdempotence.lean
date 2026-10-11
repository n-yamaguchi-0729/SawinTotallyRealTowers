/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Nyll.ProCGroups.Topologies.Conjugation

/-!
# The residual core has no further pro-C quotient

For a full formation, taking the residual core inside the residual core gives the whole
subgroup. The proof uses closure under extensions and continuous conjugation; no finite
generation or abstract characteristic-subgroup hypothesis is required.
-/

namespace ProCGroups.ProC

universe u

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The residual core of a profinite group's residual core is the whole subgroup. -/
theorem proCResidualCore_self_eq_top
    (hC : FiniteGroupClass.FullFormation C) :
    proCResidualCore C (proCResidualCore C G) = ⊤ := by
  let R : Subgroup G := proCResidualCore C G
  have hRclosed : IsClosed (R : Set G) := proCResidualCore_isClosed C G
  have : CompactSpace R := hRclosed.isClosedEmbedding_subtypeVal.compactSpace
  let S₀ : Subgroup R := proCResidualCore C R
  have hS₀closed : IsClosed (S₀ : Set R) := proCResidualCore_isClosed C R
  let S : Subgroup G := S₀.map R.subtype
  have hSR : S ≤ R := Subgroup.map_subtype_le S₀
  have hSclosed : IsClosed (S : Set G) := by
    change IsClosed (R.subtype '' (S₀ : Set R))
    exact (hS₀closed.isCompact.image continuous_subtype_val).isClosed
  have hSnormal : S.Normal := by
    refine ⟨?_⟩
    intro x hx g
    rcases hx with ⟨r, hr, rfl⟩
    let e : R ≃ₜ* R := Subgroup.conjNormalContinuousMulEquiv R g
    have he : S₀.map e.toMulEquiv.toMonoidHom ≤ S₀ :=
      map_proCResidualCore_le_of_hom
        hC.hereditary e.toMulEquiv.toMonoidHom e.continuous_toFun
    refine ⟨e r, he ⟨r, hr, rfl⟩, ?_⟩
    exact MulAut.conjNormal_apply g r
  have : TotallyDisconnectedSpace (G ⧸ S) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal S hSclosed
  have : TotallyDisconnectedSpace (R ⧸ S₀) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal S₀ hS₀closed
  let q : G →ₜ* G ⧸ S := ContinuousMonoidHom.quotientMk S
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective S
  let P : Subgroup (G ⧸ S) := R.map q.toMonoidHom
  have : P.Normal :=
    (inferInstance : R.Normal).map q.toMonoidHom hqsurj
  have hPclosed : IsClosed (P : Set (G ⧸ S)) := by
    change IsClosed (q '' (R : Set G))
    exact (hRclosed.isCompact.image q.continuous_toFun).isClosed
  let f : R →ₜ* P :=
    { toMonoidHom :=
        { toFun := fun r => ⟨q r.1, ⟨r.1, r.2, rfl⟩⟩
          map_one' := Subtype.ext q.map_one
          map_mul' := fun r s => Subtype.ext (q.map_mul r.1 s.1) }
      continuous_toFun :=
        (q.continuous_toFun.comp continuous_subtype_val).subtype_mk
          (fun r => ⟨r.1, r.2, rfl⟩) }
  have hfsurj : Function.Surjective f := by
    intro x
    rcases x.2 with ⟨g, hg, hqx⟩
    exact ⟨⟨g, hg⟩, Subtype.ext hqx⟩
  have hS₀ker : S₀ ≤ f.toMonoidHom.ker := by
    intro r hr
    apply Subtype.ext
    change QuotientGroup.mk' S r.1 = 1
    exact (QuotientGroup.eq_one_iff (N := S) r.1).2 ⟨r, hr, rfl⟩
  let fbar : R ⧸ S₀ →ₜ* P := QuotientGroup.liftₜ S₀ f hS₀ker
  have hfbarsurj : Function.Surjective fbar := by
    intro x
    rcases hfsurj x with ⟨r, rfl⟩
    exact ⟨QuotientGroup.mk' S₀ r, QuotientGroup.liftₜ_apply_mk S₀ f hS₀ker r⟩
  have hRquot : HasOpenNormalBasisInClass C (R ⧸ S₀) :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass hC.melnikovFormation.formation
  have hP : HasOpenNormalBasisInClass C P :=
    HasOpenNormalBasisInClass.of_surjective
      hC.melnikovFormation.formation hRquot fbar hfbarsurj
  have hqker : q.toMonoidHom.ker ≤ R := by
    intro x hx
    exact hSR ((QuotientGroup.eq_one_iff (N := S) x).1 hx)
  let eQ : G ⧸ R ≃ₜ* (G ⧸ S) ⧸ P :=
    QuotientGroup.mapContinuousMulEquivOfSurjective q hqsurj
      (show R.map q.toMonoidHom = P from rfl) hqker
  have hQ : HasOpenNormalBasisInClass C ((G ⧸ S) ⧸ P) :=
    HasOpenNormalBasisInClass.ofContinuousMulEquiv
      (proCResidualCoreQuotient_hasOpenNormalBasisInClass hC.melnikovFormation.formation) eQ
  have hE : HasOpenNormalBasisInClass C (G ⧸ S) :=
    HasOpenNormalBasisInClass.extension
      hC.isomClosed hC.quotientClosed hC.extensionClosed P hPclosed hP hQ
  have hRS : R ≤ S :=
    proCResidualCore_le_of_proCQuotient S hSclosed hE
  change S₀ = ⊤
  apply top_unique
  intro r _hr
  rcases hRS r.2 with ⟨s, hs, hsr⟩
  exact (Subtype.ext hsr : s = r) ▸ hs

/-- Every continuous homomorphism from the residual core to a Hausdorff pro-C target is trivial. -/
theorem continuousHom_from_proCResidualCore_eq_one
    (hC : FiniteGroupClass.FullFormation C)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : proCResidualCore C G →ₜ* H) (hH : HasOpenNormalBasisInClass C H)
    (r : proCResidualCore C G) : f r = 1 := by
  have hRclosed := proCResidualCore_isClosed C G
  have : CompactSpace (proCResidualCore C G) :=
    hRclosed.isClosedEmbedding_subtypeVal.compactSpace
  have hker :=
    proCResidualCore_le_ker_of_continuousMonoidHom_to_proC hC.hereditary f hH
  rw [proCResidualCore_self_eq_top hC] at hker
  exact hker (Subgroup.mem_top r)

/-- A closed subgroup containing the ambient residual core has that same residual core,
viewed as a subgroup of the smaller group. -/
theorem proCResidualCore_eq_comap_of_le
    (hC : FiniteGroupClass.FullFormation C)
    (J : Subgroup G) (hJclosed : IsClosed (J : Set G))
    (hRJ : proCResidualCore C G ≤ J) :
    proCResidualCore C J = (proCResidualCore C G).comap J.subtype := by
  have : CompactSpace J := hJclosed.isClosedEmbedding_subtypeVal.compactSpace
  have hle :
      proCResidualCore C J ≤ (proCResidualCore C G).comap J.subtype :=
    Subgroup.map_le_iff_le_comap.1
      (map_proCResidualCore_le_of_hom hC.hereditary J.subtype continuous_subtype_val)
  let R : Subgroup G := proCResidualCore C G
  have hRclosed : IsClosed (R : Set G) := proCResidualCore_isClosed C G
  have : CompactSpace R := hRclosed.isClosedEmbedding_subtypeVal.compactSpace
  let i : R →* J := Subgroup.inclusion hRJ
  have hi : Continuous i :=
    continuous_subtype_val.subtype_mk (fun r : R => hRJ r.2)
  have hmap : (proCResidualCore C R).map i ≤ proCResidualCore C J :=
    map_proCResidualCore_le_of_hom hC.hereditary i hi
  have hRcore : proCResidualCore C R = ⊤ := proCResidualCore_self_eq_top (G := G) hC
  rw [hRcore] at hmap
  refine le_antisymm hle ?_
  intro x hx
  let r : R := ⟨x.1, hx⟩
  exact hmap ⟨r, Subgroup.mem_top r, Subtype.ext rfl⟩

end ProCGroups.ProC
