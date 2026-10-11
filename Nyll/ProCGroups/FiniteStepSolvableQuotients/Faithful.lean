/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
import Nyll.ProCGroups.FiniteStepSolvableQuotients.AbFaithfulness
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Abelianization
import Nyll.ProCGroups.ProC.Quotients.ClosedNormal

/-!
# Faithful actions on topological abelianizations

This module defines abelianization-faithfulness for open subgroups and proves that it is preserved
under continuous multiplicative equivalences and passage between suitable quotients.
-/

open scoped Topology

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.Abelian

universe u v

/-- An action has no nontrivial fixed points if every globally fixed element is trivial. -/
def HasNoNontrivialFixedPoints
    {Q : Type u} [Group Q]
    {A : Type v} [Group A]
    (ρ : Q →* MulAut A) : Prop :=
  ∀ a : A, (∀ q : Q, ρ q a = a) → a = 1

/-- Faithfulness of the quotient-conjugation action pulls back across a continuous
multiplicative equivalence, with the open normal subgroup pushed forward along
the equivalence. -/
theorem quotientConjAbelianization_injective_of_continuousMulEquiv_image
    {G : Type u} {H : Type v}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (N : OpenNormalSubgroup G)
    (hinjH :
      Function.Injective
        (quotientConjugationTopologicalAbelianizationMap
          (G := H)
          (N := (ProCGroups.ProC.OpenNormalSubgroup.map
            (ContinuousMonoidHom.toContinuousMonoidHom e) (Homeomorph.isOpenMap e.toHomeomorph)
            e.surjective N : Subgroup H)))) :
    Function.Injective
      (quotientConjugationTopologicalAbelianizationMap
        (G := G) (N := (N : Subgroup G))) := by
  let Nmap : OpenNormalSubgroup H :=
    ProCGroups.ProC.OpenNormalSubgroup.map
      (ContinuousMonoidHom.toContinuousMonoidHom e) (Homeomorph.isOpenMap e.toHomeomorph)
      e.surjective N
  let eN : ((N : Subgroup G) : Type u) ≃ₜ*
      ((Nmap : Subgroup H) : Type v) :=
    { toMulEquiv :=
        { toFun := fun x => ⟨e x.1, by
            change e x.1 ∈
              (N : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom
            exact ⟨x.1, x.2, rfl⟩⟩
          invFun := fun y => ⟨e.symm y.1, by
            have hy : y.1 ∈
                (N : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom := by
              exact y.property
            rcases hy with ⟨x, hxN, hxy⟩
            have hs : e.symm y.1 = x := by
              apply e.injective
              simpa using hxy.symm
            rw [hs]
            exact hxN⟩
          left_inv := by
            intro x
            ext
            simp
          right_inv := by
            intro y
            ext
            simp
          map_mul' := by
            intro x y
            ext
            simp }
      continuous_toFun := by
        exact Continuous.subtype_mk
          (e.continuous_toFun.comp continuous_subtype_val)
          (fun x => by
            change e x.1 ∈
              (N : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom
            exact ⟨x.1, x.2, rfl⟩)
      continuous_invFun := by
        exact Continuous.subtype_mk
          (e.symm.continuous_toFun.comp continuous_subtype_val)
          (fun y => by
            change e.symm y.1 ∈ (N : Subgroup G)
            have hy : y.1 ∈
                (N : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom := by
              exact y.property
            rcases hy with ⟨x, hxN, hxy⟩
            have hs : e.symm y.1 = x := by
              apply e.injective
              simpa using hxy.symm
            rw [hs]
            exact hxN) }
  let eAb :
      TopologicalAbelianization ((N : Subgroup G) : Type u) ≃ₜ*
        TopologicalAbelianization ((Nmap : Subgroup H) : Type v) :=
    TopologicalAbelianization.congr eN
  let qMap : G ⧸ (N : Subgroup G) →*
      H ⧸ (Nmap : Subgroup H) :=
    QuotientGroup.map (N := (N : Subgroup G)) (M := (Nmap : Subgroup H))
      (f := (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom) (by
        intro x hx
        change e x ∈
          (N : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom
        exact ⟨x, hx, rfl⟩)
  have hqMapKer : qMap.ker = ⊥ := by
    exact TopologicalGroup.ker_map_eq_bot_of_comap_eq
      (f := (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom)
      (N := (N : Subgroup G))
      (M := (Nmap : Subgroup H))
      (h := by
        intro x hx
        change e x ∈
          (N : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom
        exact ⟨x, hx, rfl⟩)
      (hcomap := by
        ext x
        constructor
        · intro hx
          have hx' : e x ∈
              (N : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom := by
            exact hx
          rcases hx' with ⟨y, hyN, hyx⟩
          have hxy : x = y := by
            apply e.injective
            simpa using hyx.symm
          simpa [hxy] using hyN
        · intro hx
          change e x ∈ (Nmap : Subgroup H)
          change e x ∈
            (N : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom
          exact ⟨x, hx, rfl⟩)
  have hqMapInj : Function.Injective qMap := by
    exact (MonoidHom.ker_eq_bot_iff (f := qMap)).1 hqMapKer
  let ρG : G ⧸ (N : Subgroup G) →*
      MulAut (TopologicalAbelianization ((N : Subgroup G) : Type u)) :=
    quotientConjugationTopologicalAbelianizationMap
      (G := G) (N := (N : Subgroup G))
  let ρH : H ⧸ (Nmap : Subgroup H) →*
      MulAut (TopologicalAbelianization ((Nmap : Subgroup H) : Type v)) :=
    quotientConjugationTopologicalAbelianizationMap
      (G := H) (N := (Nmap : Subgroup H))
  have haction_mk
      (g : G) (x : ((N : Subgroup G) : Type u)) :
      eAb
        (ρG (QuotientGroup.mk' (N : Subgroup G) g)
          (TopologicalAbelianization.mk
            ((N : Subgroup G) : Type u) x)) =
      ρH (QuotientGroup.mk' (Nmap : Subgroup H) (e g))
        (eAb
          (TopologicalAbelianization.mk
            ((N : Subgroup G) : Type u) x)) := by
    have hconj :
        eN ((MulAut.conjNormal g) x) =
          (MulAut.conjNormal (e g)) (eN x) := by
      ext
      simp [eN]
    rw [show
        ρG (QuotientGroup.mk' (N : Subgroup G) g)
          (TopologicalAbelianization.mk
            ((N : Subgroup G) : Type u) x) =
          TopologicalAbelianization.mk
            ((N : Subgroup G) : Type u) ((MulAut.conjNormal g) x) by
          simpa [ρG] using
            (quotientConjugationTopologicalAbelianizationMap_mk_apply_mk
              (N := (N : Subgroup G)) (g := g) (n := x))]
    rw [show
        eAb (TopologicalAbelianization.mk
          ((N : Subgroup G) : Type u) ((MulAut.conjNormal g) x)) =
        TopologicalAbelianization.mk
          ((Nmap : Subgroup H) : Type v) (eN ((MulAut.conjNormal g) x)) by
        rfl]
    rw [show
        eAb (TopologicalAbelianization.mk
          ((N : Subgroup G) : Type u) x) =
        TopologicalAbelianization.mk
          ((Nmap : Subgroup H) : Type v) (eN x) by
        rfl]
    rw [hconj]
    change
      TopologicalAbelianization.mk
          ((Nmap : Subgroup H) : Type v)
          ((MulAut.conjNormal (e g)) (eN x)) =
        quotientConjugationTopologicalAbelianizationMap
          (G := H) (N := (Nmap : Subgroup H))
          (QuotientGroup.mk' (Nmap : Subgroup H) (e g))
          (TopologicalAbelianization.mk
            ((Nmap : Subgroup H) : Type v) (eN x))
    exact
      (quotientConjugationTopologicalAbelianizationMap_mk_apply_mk
        (N := (Nmap : Subgroup H)) (g := e g) (n := eN x)).symm
  have hcomp :
      ∀ q : G ⧸ (N : Subgroup G),
        ρH (qMap q) = (MulAut.congr eAb.toMulEquiv) (ρG q) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N : Subgroup G) q
    ext a
    obtain ⟨apre, rfl⟩ := eAb.surjective a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.closedCommutator (N : Subgroup G)) apre
    have hqMap_mk :
        qMap (QuotientGroup.mk' (N : Subgroup G) g) =
          QuotientGroup.mk' (Nmap : Subgroup H) (e g) := by
      exact QuotientGroup.map_mk' (N : Subgroup G) (Nmap : Subgroup H)
        (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom
        (fun x hx => show e x ∈ (N : Subgroup G).map
          (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom from ⟨x, hx, rfl⟩) g
    have hcongr_apply
        (a₀ : TopologicalAbelianization ((N : Subgroup G) : Type u)) :
        (MulAut.congr eAb.toMulEquiv)
            (ρG (QuotientGroup.mk' (N : Subgroup G) g))
            (eAb a₀) =
          eAb
            (ρG (QuotientGroup.mk' (N : Subgroup G) g)
              a₀) := by
      change
        eAb.toMulEquiv
            (ρG (QuotientGroup.mk' (N : Subgroup G) g)
              (eAb.toMulEquiv.symm (eAb.toMulEquiv a₀))) =
          eAb.toMulEquiv
            (ρG (QuotientGroup.mk' (N : Subgroup G) g) a₀)
      rw [eAb.toMulEquiv.symm_apply_apply]
    rw [hqMap_mk, hcongr_apply]
    exact (haction_mk g x).symm
  intro q₁ q₂ hq
  have hcongr : ρH (qMap q₁) = ρH (qMap q₂) := by
    simpa [hcomp q₁, hcomp q₂] using
      congrArg (MulAut.congr eAb.toMulEquiv) hq
  exact hqMapInj (hinjH hcongr)

/-- `IsAbFaithful` is transported by a continuous multiplicative equivalence. -/
theorem isAbFaithful_of_continuousMulEquiv
    {G : Type u} {H : Type v}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (hH : IsAbFaithful H) :
    IsAbFaithful G := by
  intro K N
  let Kmap : OpenSubgroup H := by
    refine
      { toSubgroup := (K : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom
        isOpen' := ?_ }
    change IsOpen (e '' ((K : Subgroup G) : Set G))
    exact Homeomorph.isOpenMap e.toHomeomorph _ K.isOpen'
  let eK : ((K : Subgroup G) : Type u) ≃ₜ* ((Kmap : Subgroup H) : Type v) :=
    { toMulEquiv :=
        { toFun := fun x => ⟨e x.1, by
            change e x.1 ∈
              (K : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom
            exact ⟨x.1, x.2, rfl⟩⟩
          invFun := fun y => ⟨e.symm y.1, by
            have hy : y.1 ∈
                (K : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom := by
              exact y.property
            rcases hy with ⟨x, hxK, hxy⟩
            have hs : e.symm y.1 = x := by
              apply e.injective
              simpa using hxy.symm
            rw [hs]
            exact hxK⟩
          left_inv := by
            intro x
            ext
            simp
          right_inv := by
            intro y
            ext
            simp
          map_mul' := by
            intro x y
            ext
            simp }
      continuous_toFun := by
        exact Continuous.subtype_mk
          (e.continuous_toFun.comp continuous_subtype_val)
          (fun x => by
            change e x.1 ∈
              (K : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom
            exact ⟨x.1, x.2, rfl⟩)
      continuous_invFun := by
        exact Continuous.subtype_mk
          (e.symm.continuous_toFun.comp continuous_subtype_val)
          (fun y => by
            change e.symm y.1 ∈ (K : Subgroup G)
            have hy : y.1 ∈
                (K : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom := by
              exact y.property
            rcases hy with ⟨x, hxK, hxy⟩
            have hs : e.symm y.1 = x := by
              apply e.injective
              simpa using hxy.symm
            rw [hs]
            exact hxK) }
  exact quotientConjAbelianization_injective_of_continuousMulEquiv_image
    (e := eK) (N := N)
    (hH Kmap
      (ProCGroups.ProC.OpenNormalSubgroup.map (ContinuousMonoidHom.toContinuousMonoidHom eK)
        (Homeomorph.isOpenMap eK.toHomeomorph) eK.surjective N))

/-- Continuous multiplicative equivalence invariance of `IsAbFaithful`. -/
theorem isAbFaithful_iff_continuousMulEquiv
    {G : Type u} {H : Type v}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) :
    IsAbFaithful G ↔ IsAbFaithful H :=
  ⟨fun hG => isAbFaithful_of_continuousMulEquiv e.symm hG,
    fun hH => isAbFaithful_of_continuousMulEquiv e hH⟩

/-- Open subgroups of an `ab`-faithful topological group are `ab`-faithful. -/
theorem isAbFaithful_openSubgroup
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (hG : IsAbFaithful G) (U : OpenSubgroup G) :
    IsAbFaithful ((U : Subgroup G) : Type u) := by
  intro H N
  let Hmap : OpenSubgroup G := by
    refine
      { toSubgroup :=
          (H : Subgroup ((U : Subgroup G) : Type u)).map
            ((U : Subgroup G).subtype)
        isOpen' := ?_ }
    change IsOpen
      (((fun x : ((U : Subgroup G) : Type u) => (x : G)) ''
        ((H : Subgroup ((U : Subgroup G) : Type u)) :
          Set ((U : Subgroup G) : Type u))) : Set G)
    exact U.isOpen'.isOpenMap_subtype_val _ H.isOpen'
  have hHmap_le_U : (Hmap : Subgroup G) ≤ (U : Subgroup G) := by
    intro x hx
    rcases hx with ⟨y, _hyH, rfl⟩
    exact y.2
  have hsubgroupOf_eq :
      (Hmap : Subgroup G).subgroupOf (U : Subgroup G) =
        (H : Subgroup ((U : Subgroup G) : Type u)) := by
    ext x
    constructor
    · intro hx
      change (x : G) ∈ (Hmap : Subgroup G) at hx
      rcases hx with ⟨y, hyH, hyx⟩
      have hyxU : y = x := Subtype.ext hyx
      simpa [hyxU] using hyH
    · intro hx
      change (x : G) ∈ (Hmap : Subgroup G)
      exact ⟨x, hx, rfl⟩
  let eEq : ((H : Subgroup ((U : Subgroup G) : Type u)) : Type u) ≃ₜ*
      (((Hmap : Subgroup G).subgroupOf (U : Subgroup G)) : Type u) :=
    { toMulEquiv :=
        { toFun := fun x => ⟨x.1, by
            exact hsubgroupOf_eq.symm ▸ x.2⟩
          invFun := fun x => ⟨x.1, by
            exact hsubgroupOf_eq ▸ x.2⟩
          left_inv := by
            intro x
            ext
            rfl
          right_inv := by
            intro x
            ext
            rfl
          map_mul' := by
            intro x y
            rfl }
      continuous_toFun := by
        exact Continuous.subtype_mk continuous_subtype_val
          (fun x => hsubgroupOf_eq.symm ▸ x.2)
      continuous_invFun := by
        exact Continuous.subtype_mk continuous_subtype_val
          (fun x => hsubgroupOf_eq ▸ x.2) }
  let eH : ((H : Subgroup ((U : Subgroup G) : Type u)) : Type u) ≃ₜ*
      ((Hmap : Subgroup G) : Type u) :=
    eEq.trans (Subgroup.subgroupOfContinuousMulEquivOfLe hHmap_le_U)
  exact quotientConjAbelianization_injective_of_continuousMulEquiv_image
    (e := eH) (N := N)
    (hG Hmap
      (ProCGroups.ProC.OpenNormalSubgroup.map (ContinuousMonoidHom.toContinuousMonoidHom eH)
        (Homeomorph.isOpenMap eH.toHomeomorph) eH.surjective N))

/-- The same open normal subgroup viewed inside the \(\top\) open subgroup. -/
def openNormalSubgroupTop
    {G : Type u} [TopologicalSpace G] [Group G]
    (U : OpenNormalSubgroup G) :
    OpenNormalSubgroup ↥((⊤ : OpenSubgroup G) : Subgroup G) where
  toOpenSubgroup :=
    OpenSubgroup.comap ((⊤ : Subgroup G).subtype) continuous_subtype_val U.toOpenSubgroup
  isNormal' := by
    change ((U : Subgroup G).comap ((⊤ : Subgroup G).subtype)).Normal
    infer_instance

/-- Injectivity on the top-open-subgroup model implies injectivity in the ambient group. -/
theorem inj_quotientConjugationTopologicalAbelianizationMap_of_openNormalSubgroupTop
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G)
    (hTop :
      Function.Injective
        (quotientConjugationTopologicalAbelianizationMap
          (G := ↥((⊤ : OpenSubgroup G) : Subgroup G))
          (N := (openNormalSubgroupTop U : Subgroup ↥((⊤ : OpenSubgroup G) : Subgroup G))))) :
    Function.Injective
      (quotientConjugationTopologicalAbelianizationMap
        (G := G) (N := (U : Subgroup G))) := by
  let Gtop : Type u := ↥((⊤ : OpenSubgroup G) : Subgroup G)
  let UTop : OpenNormalSubgroup Gtop := openNormalSubgroupTop U
  let eG : Gtop ≃ₜ* G := OpenSubgroup.topContinuousMulEquiv G
  let eU : ↥(UTop : Subgroup Gtop) ≃ₜ* ↥(U : Subgroup G) :=
    { toMulEquiv :=
        { toFun := fun x => ⟨x.1.1, by
              change x.1.1 ∈ U.toOpenSubgroup
              have hx := x.2
              change x.1.1 ∈ U.toOpenSubgroup at hx
              exact hx⟩
          invFun := fun x => ⟨⟨x.1, Subgroup.mem_top x.1⟩, by
              change x.1 ∈ U.toOpenSubgroup
              exact x.2⟩
          left_inv := by
            intro x
            apply Subtype.ext
            rfl
          right_inv := by
            intro x
            apply Subtype.ext
            rfl
          map_mul' := by
            intro x y
            apply Subtype.ext
            rfl }
      continuous_toFun := by
        exact Continuous.subtype_mk
          (continuous_subtype_val.comp continuous_subtype_val)
          (fun x => by
            change x.1.1 ∈ U.toOpenSubgroup
            have hx := x.2
            change x.1.1 ∈ U.toOpenSubgroup at hx
            exact hx)
      continuous_invFun := by
        exact Continuous.subtype_mk
          (Continuous.subtype_mk continuous_subtype_val
            (fun x => Subgroup.mem_top x.1))
          (fun x => by
            change x.1 ∈ U.toOpenSubgroup
            exact x.2) }
  let eAb : TopologicalAbelianization ↥(UTop : Subgroup Gtop) ≃ₜ*
      TopologicalAbelianization ↥(U : Subgroup G) :=
    TopologicalAbelianization.congr (G := ↥(UTop : Subgroup Gtop))
      (H := ↥(U : Subgroup G)) eU
  let qMap : G ⧸ (U : Subgroup G) →*
      Gtop ⧸ (UTop : Subgroup Gtop) :=
    QuotientGroup.map (N := (U : Subgroup G)) (M := (UTop : Subgroup Gtop))
      (f := eG.symm.toMonoidHom) (by
        intro x hx
        change ((eG.symm x : Gtop) : G) ∈ U.toOpenSubgroup
        have hval : ((eG.symm x : Gtop) : G) = x := by
          exact eG.apply_symm_apply x
        rw [hval]
        exact hx)
  have hqMapKer : qMap.ker = ⊥ := by
    exact TopologicalGroup.ker_map_eq_bot_of_comap_eq
      (f := eG.symm.toMonoidHom)
      (N := (U : Subgroup G))
      (M := (UTop : Subgroup Gtop))
      (h := by
        intro x hx
        change ((eG.symm x : Gtop) : G) ∈ U.toOpenSubgroup
        have hval : ((eG.symm x : Gtop) : G) = x := by
          exact eG.apply_symm_apply x
        rw [hval]
        exact hx)
      (hcomap := by
        ext x
        constructor
        · intro hx
          change ((eG.symm x : Gtop) : G) ∈ U.toOpenSubgroup at hx
          have hval : ((eG.symm x : Gtop) : G) = x := by
            exact eG.apply_symm_apply x
          rw [hval] at hx
          exact hx
        · intro hx
          change ((eG.symm x : Gtop) : G) ∈ U.toOpenSubgroup
          have hval : ((eG.symm x : Gtop) : G) = x := by
            exact eG.apply_symm_apply x
          rw [hval]
          exact hx)
  have hqMapInj : Function.Injective qMap := by
    exact (MonoidHom.ker_eq_bot_iff (f := qMap)).1 hqMapKer
  let ρTop : Gtop ⧸ (UTop : Subgroup Gtop) →*
      MulAut (TopologicalAbelianization ↥(UTop : Subgroup Gtop)) :=
    quotientConjugationTopologicalAbelianizationMap
      (G := Gtop) (N := (UTop : Subgroup Gtop))
  let ρU : G ⧸ (U : Subgroup G) →*
      MulAut (TopologicalAbelianization ↥(U : Subgroup G)) :=
    quotientConjugationTopologicalAbelianizationMap
      (G := G) (N := (U : Subgroup G))
  have haction_mk
      (g : G)
      (x : ↥(UTop : Subgroup Gtop)) :
      eAb
        (ρTop (QuotientGroup.mk' (UTop : Subgroup Gtop) (eG.symm g))
          (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x)) =
      ρU (QuotientGroup.mk' (U : Subgroup G) g)
        (eAb (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x)) := by
    have hconj :
        eU ((MulAut.conjNormal (eG.symm g)) x) =
          (MulAut.conjNormal g) (eU x) := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply]
      have hval : ((eG.symm g : Gtop) : G) = g := by
        exact eG.apply_symm_apply g
      change
        ((eG.symm g : Gtop) : G) * x.1.1 * ((eG.symm g : Gtop) : G)⁻¹ =
          g * x.1.1 * g⁻¹
      rw [hval]
    rw [show ρTop (QuotientGroup.mk' (UTop : Subgroup Gtop) (eG.symm g))
        (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x) =
          TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop)
            ((MulAut.conjNormal (eG.symm g)) x) by
          simpa [ρTop] using
            (quotientConjugationTopologicalAbelianizationMap_mk_apply_mk
              (N := (UTop : Subgroup Gtop)) (g := eG.symm g) (n := x))]
    rw [show
        eAb (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop)
          ((MulAut.conjNormal (eG.symm g)) x)) =
        TopologicalAbelianization.mk ↥(U : Subgroup G)
          (eU ((MulAut.conjNormal (eG.symm g)) x)) by
        rfl]
    rw [show
        eAb (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x) =
        TopologicalAbelianization.mk ↥(U : Subgroup G) (eU x) by
        rfl]
    rw [hconj]
    change TopologicalAbelianization.mk ↥(U : Subgroup G)
        ((MulAut.conjNormal g) (eU x)) =
      quotientConjugationTopologicalAbelianizationMap (G := G) (N := (U : Subgroup G))
        (QuotientGroup.mk' (U : Subgroup G) g)
        (TopologicalAbelianization.mk ↥(U : Subgroup G) (eU x))
    exact (quotientConjugationTopologicalAbelianizationMap_mk_apply_mk
      (N := (U : Subgroup G)) (g := g) (n := eU x)).symm
  have hcomp :
      ∀ q : G ⧸ (U : Subgroup G),
        ρU q = (MulAut.congr eAb.toMulEquiv) (ρTop (qMap q)) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup G) q
    ext a
    obtain ⟨apre, rfl⟩ := eAb.surjective a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.closedCommutator (UTop : Subgroup Gtop)) apre
    change
      ρU (QuotientGroup.mk' (U : Subgroup G) g)
          (eAb (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x)) =
        eAb
          (ρTop (QuotientGroup.mk' (UTop : Subgroup Gtop) (eG.symm g))
            (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x))
    exact (haction_mk g x).symm
  intro q₁ q₂ hq
  have hcongr : (MulAut.congr eAb.toMulEquiv) (ρTop (qMap q₁)) =
      (MulAut.congr eAb.toMulEquiv) (ρTop (qMap q₂)) := by
    simpa [ρU, hcomp q₁, hcomp q₂] using hq
  have htopEq : ρTop (qMap q₁) = ρTop (qMap q₂) :=
    (MulAut.congr eAb.toMulEquiv).injective hcongr
  exact hqMapInj (hTop htopEq)

/--
Injectivity in the ambient group transfers to the corresponding open normal subgroup inside the
\(\top\) open subgroup model.
-/
theorem inj_quotientConjugationTopologicalAbelianizationMap_on_openNormalSubgroupTop
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G)
    (hU :
      Function.Injective
        (quotientConjugationTopologicalAbelianizationMap
          (G := G) (N := (U : Subgroup G)))) :
    Function.Injective
      (quotientConjugationTopologicalAbelianizationMap
        (G := ↥((⊤ : OpenSubgroup G) : Subgroup G))
        (N := (openNormalSubgroupTop U : Subgroup ↥((⊤ : OpenSubgroup G) : Subgroup G)))) := by
  let Gtop : Type u := ↥((⊤ : OpenSubgroup G) : Subgroup G)
  let UTop : OpenNormalSubgroup Gtop := openNormalSubgroupTop U
  let eG : Gtop ≃ₜ* G := OpenSubgroup.topContinuousMulEquiv G
  let eU : ↥(UTop : Subgroup Gtop) ≃ₜ* ↥(U : Subgroup G) :=
    { toMulEquiv :=
        { toFun := fun x => ⟨x.1.1, by
              change x.1.1 ∈ U.toOpenSubgroup
              have hx := x.2
              change x.1.1 ∈ U.toOpenSubgroup at hx
              exact hx⟩
          invFun := fun x => ⟨⟨x.1, Subgroup.mem_top x.1⟩, by
              change x.1 ∈ U.toOpenSubgroup
              exact x.2⟩
          left_inv := by
            intro x
            apply Subtype.ext
            rfl
          right_inv := by
            intro x
            apply Subtype.ext
            rfl
          map_mul' := by
            intro x y
            apply Subtype.ext
            rfl }
      continuous_toFun := by
        exact Continuous.subtype_mk
          (continuous_subtype_val.comp continuous_subtype_val)
          (fun x => by
            change x.1.1 ∈ U.toOpenSubgroup
            have hx := x.2
            change x.1.1 ∈ U.toOpenSubgroup at hx
            exact hx)
      continuous_invFun := by
        exact Continuous.subtype_mk
          (Continuous.subtype_mk continuous_subtype_val
            (fun x => Subgroup.mem_top x.1))
          (fun x => by
            change x.1 ∈ U.toOpenSubgroup
            exact x.2) }
  let eAb : TopologicalAbelianization ↥(UTop : Subgroup Gtop) ≃ₜ*
      TopologicalAbelianization ↥(U : Subgroup G) :=
    TopologicalAbelianization.congr (G := ↥(UTop : Subgroup Gtop))
      (H := ↥(U : Subgroup G)) eU
  let qMap : Gtop ⧸ (UTop : Subgroup Gtop) →* G ⧸ (U : Subgroup G) :=
    QuotientGroup.map (N := (UTop : Subgroup Gtop)) (M := (U : Subgroup G))
      (f := eG.toMonoidHom) (by
        intro x hx
        change eG x ∈ U.toOpenSubgroup
        change x.1 ∈ U.toOpenSubgroup at hx
        have hval : eG x = x.1 := by
          exact OpenSubgroup.topContinuousMulEquiv_apply G x
        rw [hval]
        exact hx)
  have hqMapKer : qMap.ker = ⊥ := by
    exact TopologicalGroup.ker_map_eq_bot_of_comap_eq
      (f := eG.toMonoidHom)
      (N := (UTop : Subgroup Gtop))
      (M := (U : Subgroup G))
      (h := by
        intro x hx
        change eG x ∈ U.toOpenSubgroup
        change x.1 ∈ U.toOpenSubgroup at hx
        have hval : eG x = x.1 := by
          exact OpenSubgroup.topContinuousMulEquiv_apply G x
        rw [hval]
        exact hx)
      (hcomap := by
        ext x
        constructor
        · intro hx
          change eG x ∈ U.toOpenSubgroup at hx
          change x.1 ∈ U.toOpenSubgroup
          have hval : eG x = x.1 := by
            exact OpenSubgroup.topContinuousMulEquiv_apply G x
          rw [hval] at hx
          exact hx
        · intro hx
          change x.1 ∈ U.toOpenSubgroup at hx
          change eG x ∈ U.toOpenSubgroup
          have hval : eG x = x.1 := by
            exact OpenSubgroup.topContinuousMulEquiv_apply G x
          rw [hval]
          exact hx)
  have hqMapInj : Function.Injective qMap := by
    exact (MonoidHom.ker_eq_bot_iff (f := qMap)).1 hqMapKer
  let ρTop : Gtop ⧸ (UTop : Subgroup Gtop) →*
      MulAut (TopologicalAbelianization ↥(UTop : Subgroup Gtop)) :=
    quotientConjugationTopologicalAbelianizationMap
      (G := Gtop) (N := (UTop : Subgroup Gtop))
  let ρU : G ⧸ (U : Subgroup G) →*
      MulAut (TopologicalAbelianization ↥(U : Subgroup G)) :=
    quotientConjugationTopologicalAbelianizationMap
      (G := G) (N := (U : Subgroup G))
  have haction_mk
      (g : Gtop)
      (x : ↥(UTop : Subgroup Gtop)) :
      eAb
        (ρTop (QuotientGroup.mk' (UTop : Subgroup Gtop) g)
          (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x)) =
      ρU (QuotientGroup.mk' (U : Subgroup G) (eG g))
        (eAb (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x)) := by
    have hconj :
        eU ((MulAut.conjNormal g) x) =
          (MulAut.conjNormal (eG g)) (eU x) := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply]
      have hval : eG g = g.1 := by
        exact OpenSubgroup.topContinuousMulEquiv_apply G g
      change
        g.1 * x.1.1 * g.1⁻¹ =
          eG g * x.1.1 * (eG g)⁻¹
      rw [hval]
    rw [show ρTop (QuotientGroup.mk' (UTop : Subgroup Gtop) g)
        (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x) =
          TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop)
            ((MulAut.conjNormal g) x) by
          simpa [ρTop] using
            (quotientConjugationTopologicalAbelianizationMap_mk_apply_mk
              (N := (UTop : Subgroup Gtop)) (g := g) (n := x))]
    rw [show eAb (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop)
          ((MulAut.conjNormal g) x)) =
            TopologicalAbelianization.mk ↥(U : Subgroup G) (eU ((MulAut.conjNormal g) x)) by
          rfl]
    rw [show eAb (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x) =
          TopologicalAbelianization.mk ↥(U : Subgroup G) (eU x) by
          rfl]
    rw [hconj]
    change TopologicalAbelianization.mk ↥(U : Subgroup G)
        ((MulAut.conjNormal (eG g)) (eU x)) =
      quotientConjugationTopologicalAbelianizationMap (G := G) (N := (U : Subgroup G))
        (QuotientGroup.mk' (U : Subgroup G) (eG g))
        (TopologicalAbelianization.mk ↥(U : Subgroup G) (eU x))
    exact (quotientConjugationTopologicalAbelianizationMap_mk_apply_mk
      (N := (U : Subgroup G)) (g := eG g) (n := eU x)).symm
  have hcomp :
      ∀ q : Gtop ⧸ (UTop : Subgroup Gtop),
        ρU (qMap q) = (MulAut.congr eAb.toMulEquiv) (ρTop q) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (UTop : Subgroup Gtop) q
    ext a
    obtain ⟨apre, rfl⟩ := eAb.surjective a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.closedCommutator (UTop : Subgroup Gtop)) apre
    change
      ρU (QuotientGroup.mk' (U : Subgroup G) (eG g))
          (eAb (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x)) =
        eAb
          (ρTop (QuotientGroup.mk' (UTop : Subgroup Gtop) g)
            (TopologicalAbelianization.mk ↥(UTop : Subgroup Gtop) x))
    exact (haction_mk g x).symm
  intro q₁ q₂ hq
  have hcongr :
      ρU (qMap q₁) = ρU (qMap q₂) := by
    simpa [hcomp q₁, hcomp q₂] using congrArg (MulAut.congr eAb.toMulEquiv) hq
  exact hqMapInj (hU hcongr)

/-- A nontrivial element is omitted by some open normal subgroup. -/
theorem exists_openNormalSubgroup_not_mem_of_ne_one
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {x : G} (hx : x ≠ 1) :
    ∃ U : OpenNormalSubgroup G, x ∉ (U : Subgroup G) := by
  let W : Set G := ({x} : Set G)ᶜ
  have hWOpen : IsOpen W := isClosed_singleton.isOpen_compl
  have h1W : (1 : G) ∈ W := by
    simpa [W, eq_comm] using hx
  rcases ProCGroups.ProC.exists_openNormalSubgroup_sub_open_nhds_of_one
      (G := G) hWOpen h1W with ⟨U, hUW⟩
  refine ⟨U, ?_⟩
  intro hxU
  have hxW : x ∈ W := hUW hxU
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false, W] at hxW

/--
Faithfulness of the conjugation action on every open normal subgroup of the \(\top\) open
subgroup forces the ambient center to be trivial.
-/
theorem center_eq_bot_of_injective_action_on_openNormalsTop
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q]
    (hfaithful :
      ∀ U : OpenNormalSubgroup ↥((⊤ : OpenSubgroup Q) : Subgroup Q),
        Function.Injective
          (quotientConjugationTopologicalAbelianizationMap
            (G := ↥((⊤ : OpenSubgroup Q) : Subgroup Q))
            (N := (U : Subgroup ↥((⊤ : OpenSubgroup Q) : Subgroup Q))))) :
    Subgroup.center Q = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  by_contra hzne
  rcases exists_openNormalSubgroup_not_mem_of_ne_one (G := Q) (x := z) hzne with ⟨U, hzU⟩
  let Gtop : Type u := ↥((⊤ : OpenSubgroup Q) : Subgroup Q)
  let zTop : Gtop := ⟨z, by simp only [OpenSubgroup.toSubgroup_top, Subgroup.mem_top]⟩
  let UTop : OpenNormalSubgroup Gtop := openNormalSubgroupTop U
  let ρ : (Gtop ⧸ (UTop : Subgroup Gtop)) →*
      MulAut (TopologicalAbelianization ↥(UTop : Subgroup Gtop)) :=
    quotientConjugationTopologicalAbelianizationMap
      (G := Gtop)
      (N := (UTop : Subgroup Gtop))
  have hzTop : zTop ∈ Subgroup.center Gtop := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    ext
    exact hz y
  have hρz :
      ρ (QuotientGroup.mk' (UTop : Subgroup Gtop) zTop) = 1 := by
    dsimp [ρ]
    exact
      quotientConjugationTopologicalAbelianizationMap_mk_eq_one_of_mem_center
        (G := Gtop) (N := (UTop : Subgroup Gtop)) (x := zTop) hzTop
  have hzTop_mem :
      zTop ∈ (UTop : Subgroup Gtop) := by
    apply (QuotientGroup.eq_one_iff
      (N := (UTop : Subgroup Gtop)) zTop).mp
    apply hfaithful UTop
    simpa using hρz
  have hzU' : z ∈ (U : Subgroup Q) := by
    change z ∈ U.toOpenSubgroup
    change z ∈ U.toOpenSubgroup at hzTop_mem
    exact hzTop_mem
  exact hzU hzU'

/-- An abelianization-faithful profinite group has trivial center. -/
theorem center_eq_bot_of_isAbFaithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbFaithful G) :
    Subgroup.center G = ⊥ := by
  refine center_eq_bot_of_injective_action_on_openNormalsTop (Q := G) ?_
  intro U
  simpa using hG ⊤ U

/-- Every open subgroup of an abelianization-faithful profinite group has trivial center. -/
theorem openSubgroup_center_eq_bot_of_isAbFaithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbFaithful G) (H : OpenSubgroup G) :
    Subgroup.center ↥((H : Subgroup G)) = ⊥ := by
  have hHClosed : IsClosed (((H : OpenSubgroup G) : Set G)) := H.isClosed
  have : CompactSpace ↥((H : OpenSubgroup G) : Subgroup G) := by
    exact
      (show IsClosed (((H : Subgroup G) : Set G)) from
          hHClosed).isClosedEmbedding_subtypeVal.compactSpace
  exact
    center_eq_bot_of_injective_action_on_openNormalsTop
      (Q := ↥((H : OpenSubgroup G) : Subgroup G))
      (fun U => by
        let Q : Type u := ↥((H : OpenSubgroup G) : Subgroup G)
        let e : ↥((⊤ : OpenSubgroup Q) : Subgroup Q) ≃ₜ* Q :=
          OpenSubgroup.topContinuousMulEquiv Q
        let U' : OpenNormalSubgroup Q :=
          OpenNormalSubgroup.comap (e.symm : Q →* ↥((⊤ : OpenSubgroup Q) : Subgroup Q))
            e.symm.continuous_toFun U
        have hUTopEq : openNormalSubgroupTop U' = U := by
          ext x
          rfl
        have hU' :
            Function.Injective
              (quotientConjugationTopologicalAbelianizationMap
                (G := Q) (N := (U' : Subgroup Q))) := hG H U'
        have hTop :
            Function.Injective
              (quotientConjugationTopologicalAbelianizationMap
                (G := ↥((⊤ : OpenSubgroup Q) : Subgroup Q))
                (N := (openNormalSubgroupTop U' :
                  Subgroup ↥((⊤ : OpenSubgroup Q) : Subgroup Q)))) :=
          inj_quotientConjugationTopologicalAbelianizationMap_on_openNormalSubgroupTop
            (G := Q) U' hU'
        exact hUTopEq ▸ hTop)

/-- If an open normal subgroup in an open subgroup of a maximal finite-step solvable quotient
contains the last derived term, then the quotient conjugation action on its topological
abelianization is faithful. -/
theorem
    injective_quotientConjAbelianization_of_containsLastDerived_of_isClosedMap
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (hG : IsAbFaithful G)
    {m : ℕ} (hm : 2 ≤ m)
    (hclosedπ : IsClosedMap (continuousToMaxSolvQuot G m))
    (H : OpenSubgroup (MaxSolvQuot G m))
    (N : OpenNormalSubgroup ↥(H : Subgroup (MaxSolvQuot G m)))
    (hContain : containsLastDerived m H N) :
    Function.Injective
      (quotientConjugationTopologicalAbelianizationMap
        (G := ↥(H : Subgroup (MaxSolvQuot G m)))
        (N := (N : Subgroup ↥(H : Subgroup (MaxSolvQuot G m))))) := by
  let Q : Type u := MaxSolvQuot G m
  let π : G →ₜ* Q := continuousToMaxSolvQuot G m
  let Hpre : OpenSubgroup G := preimageOpenSubgroup π H
  have hHpreOpen : IsOpen ((Hpre : Subgroup G) : Set G) := Hpre.isOpen'
  let φH : ↥(Hpre : Subgroup G) →ₜ* ↥(H : Subgroup Q) :=
    ProCGroups.ContinuousMonoidHom.restrictPreimage π (H : Subgroup Q)
  let Npre : OpenNormalSubgroup ↥(Hpre : Subgroup G) := by
    refine
      { toOpenSubgroup := OpenSubgroup.comap (φH : ↥(Hpre : Subgroup G) →* ↥(H : Subgroup Q))
          φH.continuous_toFun N.toOpenSubgroup
        isNormal' := ?_ }
    change ((N : Subgroup ↥(H : Subgroup Q)).comap
      (φH : ↥(Hpre : Subgroup G) →* ↥(H : Subgroup Q))).Normal
    infer_instance
  let _ : (Npre : Subgroup ↥(Hpre : Subgroup G)).Normal := Npre.isNormal'
  have hρpre :
      Function.Injective
        (quotientConjugationTopologicalAbelianizationMap
          (G := ↥(Hpre : Subgroup G))
          (N := (Npre : Subgroup ↥(Hpre : Subgroup G)))) := hG Hpre Npre
  let Nrealized : OpenSubgroup Q := by
    refine
      ⟨(N : Subgroup ↥(H : Subgroup Q)).map ((H : Subgroup Q).subtype), ?_⟩
    change IsOpen
      (((fun y : ↥(H : Subgroup Q) => (y : Q)) ''
        ((N : Subgroup ↥(H : Subgroup Q)) : Set ↥(H : Subgroup Q))))
    exact H.isOpen'.isOpenMap_subtype_val _ N.isOpen'
  have hNpreMap :
      (Npre : Subgroup ↥(Hpre : Subgroup G)).map ((Hpre : Subgroup G).subtype) =
        ((Nrealized : Subgroup Q).comap (π : G →* Q)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change π y.1 ∈ Nrealized
      exact ⟨φH y, hy, rfl⟩
    · intro hx
      change π x ∈ Nrealized at hx
      rcases hx with ⟨⟨q, hqH⟩, hqN, hqx⟩
      have hxHpre : x ∈ Hpre := by
        change π x ∈ H
        simpa [← hqx] using hqH
      refine ⟨⟨x, hxHpre⟩, ?_, rfl⟩
      change φH ⟨x, hxHpre⟩ ∈ N
      have hqEq : (⟨q, hqH⟩ : H) = φH ⟨x, hxHpre⟩ := by
        apply Subtype.ext
        change q = π x
        exact hqx
      exact hqEq ▸ hqN
  have hπsurj : Function.Surjective π := by
    simpa [π, Q] using continuousToMaxSolvQuot_surjective (G := G) m
  have hφHsurj : Function.Surjective φH := by
    intro y
    rcases hπsurj y.1 with ⟨x, hx⟩
    have hxHpre : x ∈ Hpre := by
      change π x ∈ H
      rw [hx]
      exact y.2
    refine ⟨⟨x, hxHpre⟩, ?_⟩
    apply Subtype.ext
    change π x = y.1
    exact hx
  have hclosedφH : IsClosedMap φH := by
    exact
      TopologicalGroup.restrictPreimage_isClosedMap_of_isClosedMap
        (π := π) (Q₁ := (H : Subgroup Q)) hclosedπ
        (Subgroup.isClosed_of_isOpen (H : Subgroup Q) H.isOpen')
  have hclosedN :
      IsClosedMap
        (ProCGroups.ContinuousMonoidHom.restrictPreimage φH (N : Subgroup ↥(H : Subgroup Q))) := by
    exact
      TopologicalGroup.restrictPreimage_isClosedMap_of_isClosedMap
        (π := φH) (Q₁ := (N : Subgroup ↥(H : Subgroup Q))) hclosedφH
        (Subgroup.isClosed_of_isOpen (N : Subgroup ↥(H : Subgroup Q)) N.isOpen')
  have hder_preN :
      topDerivedTop G (m - 1) ≤ ((Nrealized : Subgroup Q).comap (π : G →* Q)) := by
    intro x hx
    change π x ∈ Nrealized
    have hxQ : π x ∈ topDerivedTop Q (m - 1) := by
      exact (topDerivedTop_le_comap (f := π) (m := m - 1)) hx
    rcases hContain (π x) hxQ with ⟨hxH, hxN⟩
    exact ⟨⟨π x, hxH⟩, hxN, rfl⟩
  have hkerN :
      (ProCGroups.ContinuousMonoidHom.restrictPreimage φH (N : Subgroup ↥(H : Subgroup Q))).ker ≤
        topDerivedTop ↥((Npre : Subgroup ↥(Hpre : Subgroup G))) 1 := by
    intro x hx
    have hxφ : φH x.1 = 1 := by
      exact
        (ProCGroups.ContinuousMonoidHom.restrictPreimage_eq_one_iff (f := φH)
          (H := (N : Subgroup ↥(H : Subgroup Q))) (x := x)).1 hx
    have hxπ : π x.1.1 = 1 := by
      exact congrArg Subtype.val hxφ
    have hxder : x.1.1 ∈ topDerivedTop G m := by
      simpa [π, Q] using
        (continuousToMaxSolvQuot_eq_one_iff (G := G) (m := m) (x := x.1.1)).1 hxπ
    have hxder' :
        x.1.1 ∈ closedDerivedSeries (G := G) ((Nrealized : Subgroup Q).comap (π : G →* Q)) 1 := by
      have hm1 : 1 ≤ m := le_trans (by decide) hm
      simpa [topDerivedTop] using
        (mem_topDerived_one_of_mem_topDerived_of_le
          (G := G) hm1 hder_preN (by simpa [topDerivedTop] using hxder))
    have hmapN2 :
        (closedDerivedSeries (G := ↥((Hpre : Subgroup G)))
          (Npre : Subgroup ↥(Hpre : Subgroup G)) 1).map
            ((Hpre : Subgroup G).subtype) =
          closedDerivedSeries (G := G)
            ((Npre : Subgroup ↥(Hpre : Subgroup G)).map ((Hpre : Subgroup G).subtype)) 1 := by
      simpa [Hpre] using
        (topDerived_one_map_subtype_eq_of_isClosed_subgroup
          (G := G) (H := (Hpre : Subgroup G))
          (K := (Npre : Subgroup ↥(Hpre : Subgroup G)))
          (Subgroup.isClosed_of_isOpen _ hHpreOpen))
    have hmapN1 :
        (topDerivedTop ↥((Npre : Subgroup ↥(Hpre : Subgroup G))) 1).map
          ((Npre : Subgroup ↥(Hpre : Subgroup G)).subtype) =
          closedDerivedSeries (G := ↥((Hpre : Subgroup G)))
            (Npre : Subgroup ↥(Hpre : Subgroup G)) 1 := by
      have hmapTop :
          ((⊤ : Subgroup ↥((Npre : Subgroup ↥(Hpre : Subgroup G)))).map
            ((Npre : Subgroup ↥(Hpre : Subgroup G)).subtype)) =
            (Npre : Subgroup ↥(Hpre : Subgroup G)) := by
        ext y
        constructor
        · rintro ⟨x, -, rfl⟩
          exact x.2
        · intro hy
          exact ⟨⟨y, hy⟩, by simp only [Subgroup.coe_top, Set.mem_univ], rfl⟩
      calc
        (topDerivedTop ↥((Npre : Subgroup ↥(Hpre : Subgroup G))) 1).map
            ((Npre : Subgroup ↥(Hpre : Subgroup G)).subtype) =
            closedDerivedSeries (G := ↥((Hpre : Subgroup G)))
              (((⊤ : Subgroup ↥((Npre : Subgroup ↥(Hpre : Subgroup G)))).map
                ((Npre : Subgroup ↥(Hpre : Subgroup G)).subtype))) 1 := by
              simpa [topDerivedTop] using
                (topDerived_one_map_subtype_eq_of_isClosed_subgroup
                  (G := ↥((Hpre : Subgroup G)))
                  (H := (Npre : Subgroup ↥(Hpre : Subgroup G)))
                  (K := (⊤ : Subgroup ↥((Npre : Subgroup ↥(Hpre : Subgroup G)))))
                  (Subgroup.isClosed_of_isOpen _ Npre.isOpen'))
        _ = closedDerivedSeries (G := ↥((Hpre : Subgroup G)))
              (Npre : Subgroup ↥(Hpre : Subgroup G)) 1 := by
              simp only [hmapTop, closedDerivedSeries_succ, closedDerivedSeries_zero]
    have hxderMap :
        x.1.1 ∈ closedDerivedSeries (G := G)
          ((Npre : Subgroup ↥(Hpre : Subgroup G)).map ((Hpre : Subgroup G).subtype)) 1 := by
      simpa [hNpreMap] using hxder'
    have hxderHpre :
        x.1 ∈ closedDerivedSeries (G := ↥((Hpre : Subgroup G)))
          (Npre : Subgroup ↥(Hpre : Subgroup G)) 1 := by
      rw [← hmapN2] at hxderMap
      rcases hxderMap with ⟨y, hy, hyx⟩
      exact Subtype.ext hyx ▸ hy
    have hxderNpreMap :
        x.1 ∈ (topDerivedTop ↥((Npre : Subgroup ↥(Hpre : Subgroup G))) 1).map
          ((Npre : Subgroup ↥(Hpre : Subgroup G)).subtype) := by
      rw [hmapN1]
      exact hxderHpre
    rcases hxderNpreMap with ⟨y, hy, hyx⟩
    exact Subtype.ext hyx ▸ hy
  let qMap :
      (↥(Hpre : Subgroup G) ⧸ (Npre : Subgroup ↥(Hpre : Subgroup G))) →*
        (↥(H : Subgroup Q) ⧸ (N : Subgroup ↥(H : Subgroup Q))) :=
    QuotientGroup.map
      (N := (Npre : Subgroup ↥(Hpre : Subgroup G)))
      (M := (N : Subgroup ↥(H : Subgroup Q)))
      (f := (φH : ↥(Hpre : Subgroup G) →* ↥(H : Subgroup Q)))
      (by
        intro x hx
        exact hx)
  have hqMap_mk (g : ↥(Hpre : Subgroup G)) :
      qMap (QuotientGroup.mk' (Npre : Subgroup ↥(Hpre : Subgroup G)) g) =
        QuotientGroup.mk' (N : Subgroup ↥(H : Subgroup Q)) (φH g) :=
    QuotientGroup.map_mk' (Npre : Subgroup ↥(Hpre : Subgroup G))
      (N : Subgroup ↥(H : Subgroup Q)) φH.toMonoidHom (fun x hx => hx) g
  have hqMapKer : qMap.ker = ⊥ := by
    exact
      TopologicalGroup.ker_map_eq_bot_of_comap_eq
        (f := (φH : ↥(Hpre : Subgroup G) →* ↥(H : Subgroup Q)))
        (N := (Npre : Subgroup ↥(Hpre : Subgroup G)))
        (M := (N : Subgroup ↥(H : Subgroup Q)))
        (h := by
          intro x hx
          exact hx)
        (hcomap := by
          rfl)
  have hqMapInj : Function.Injective qMap := by
    exact (MonoidHom.ker_eq_bot_iff (f := qMap)).1 hqMapKer
  have hqMapSurj : Function.Surjective qMap := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (N : Subgroup ↥(H : Subgroup Q)) q
    rcases hφHsurj h with ⟨g, rfl⟩
    refine ⟨QuotientGroup.mk' (Npre : Subgroup ↥(Hpre : Subgroup G)) g, ?_⟩
    exact hqMap_mk g
  let eQ :
      (↥(Hpre : Subgroup G) ⧸ (Npre : Subgroup ↥(Hpre : Subgroup G))) ≃*
        (↥(H : Subgroup Q) ⧸ (N : Subgroup ↥(H : Subgroup Q))) :=
    MulEquiv.ofBijective qMap ⟨hqMapInj, hqMapSurj⟩
  let eA :
      TopologicalAbelianization ↥(Npre : Subgroup ↥(Hpre : Subgroup G)) ≃*
        TopologicalAbelianization ↥(N : Subgroup ↥(H : Subgroup Q)) :=
    TopologicalGroup.restrictPreimage_topMaxSolvQuot_mulEquiv
      (π := φH) (Q₁ := (N : Subgroup ↥(H : Subgroup Q))) (m := 1)
      hφHsurj hclosedN hkerN
  have heA_mk (x : ↥(Npre : Subgroup ↥(Hpre : Subgroup G))) :
      eA (TopologicalAbelianization.mk ↥(Npre : Subgroup ↥(Hpre : Subgroup G)) x) =
        TopologicalAbelianization.mk ↥(N : Subgroup ↥(H : Subgroup Q))
          (ProCGroups.ContinuousMonoidHom.restrictPreimage φH (N : Subgroup ↥(H : Subgroup Q))
              x) := by
    dsimp [eA, TopologicalGroup.restrictPreimage_topMaxSolvQuot_mulEquiv]
    rfl
  let ρpre :
      (↥(Hpre : Subgroup G) ⧸ (Npre : Subgroup ↥(Hpre : Subgroup G))) →*
        MulAut (TopologicalAbelianization ↥(Npre : Subgroup ↥(Hpre : Subgroup G))) :=
    quotientConjugationTopologicalAbelianizationMap
      (G := ↥(Hpre : Subgroup G))
      (N := (Npre : Subgroup ↥(Hpre : Subgroup G)))
  let ρ :
      (↥(H : Subgroup Q) ⧸ (N : Subgroup ↥(H : Subgroup Q))) →*
        MulAut (TopologicalAbelianization ↥(N : Subgroup ↥(H : Subgroup Q))) :=
    quotientConjugationTopologicalAbelianizationMap
      (G := ↥(H : Subgroup Q))
      (N := (N : Subgroup ↥(H : Subgroup Q)))
  have haction_mk
      (g : ↥(Hpre : Subgroup G))
      (x : ↥(Npre : Subgroup ↥(Hpre : Subgroup G))) :
      eA
        (ρpre (QuotientGroup.mk' (Npre : Subgroup ↥(Hpre : Subgroup G)) g)
          (TopologicalAbelianization.mk ↥(Npre : Subgroup ↥(Hpre : Subgroup G)) x)) =
      ρ (QuotientGroup.mk' (N : Subgroup ↥(H : Subgroup Q)) (φH g))
        (eA (TopologicalAbelianization.mk ↥(Npre : Subgroup ↥(Hpre : Subgroup G)) x)) := by
    have hρpre_eval :
      ρpre (QuotientGroup.mk' (Npre : Subgroup ↥(Hpre : Subgroup G)) g)
          (TopologicalAbelianization.mk ↥(Npre : Subgroup ↥(Hpre : Subgroup G)) x) =
        TopologicalAbelianization.mk ↥(Npre : Subgroup ↥(Hpre : Subgroup G))
          ((MulAut.conjNormal g) x) := by
      simpa [ρpre] using
        (quotientConjugationTopologicalAbelianizationMap_mk_apply_mk
          (N := (Npre : Subgroup ↥(Hpre : Subgroup G))) (g := g) (n := x))
    have hconj :
        ProCGroups.ContinuousMonoidHom.restrictPreimage φH (N : Subgroup ↥(H : Subgroup Q))
          ((MulAut.conjNormal g) x) =
        (MulAut.conjNormal (φH g))
          (ProCGroups.ContinuousMonoidHom.restrictPreimage φH (N : Subgroup ↥(H : Subgroup Q))
              x) := by
      ext
      rfl
    rw [hρpre_eval, heA_mk (x := (MulAut.conjNormal g) x), heA_mk (x := x)]
    calc
      TopologicalAbelianization.mk ↥(N : Subgroup ↥(H : Subgroup Q))
          (ProCGroups.ContinuousMonoidHom.restrictPreimage φH (N : Subgroup ↥(H : Subgroup Q))
            ((MulAut.conjNormal g) x))
          =
        TopologicalAbelianization.mk ↥(N : Subgroup ↥(H : Subgroup Q))
          ((MulAut.conjNormal (φH g))
            (ProCGroups.ContinuousMonoidHom.restrictPreimage φH (N : Subgroup ↥(H : Subgroup Q))
                x)) := by
              exact congrArg (TopologicalAbelianization.mk ↥(N : Subgroup ↥(H : Subgroup Q))) hconj
      _ =
        ρ (QuotientGroup.mk' (N : Subgroup ↥(H : Subgroup Q)) (φH g))
          (TopologicalAbelianization.mk ↥(N : Subgroup ↥(H : Subgroup Q))
            (ProCGroups.ContinuousMonoidHom.restrictPreimage φH (N : Subgroup ↥(H : Subgroup Q))
                x)) := by
              exact (quotientConjugationTopologicalAbelianizationMap_mk_apply_mk
                (N := (N : Subgroup ↥(H : Subgroup Q))) (g := φH g)
                (n := ProCGroups.ContinuousMonoidHom.restrictPreimage φH (N : Subgroup ↥(H :
                    Subgroup Q)) x)).symm
  have hρpre_inj : Function.Injective ρpre := by
    simpa [ρpre] using hρpre
  have hcomp :
      ∀ p : ↥(Hpre : Subgroup G) ⧸ (Npre : Subgroup ↥(Hpre : Subgroup G)),
        ρ (eQ p) = (MulAut.congr eA) (ρpre p) := by
    intro p
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      (Npre : Subgroup ↥(Hpre : Subgroup G)) p
    ext z
    obtain ⟨zpre, rfl⟩ := eA.surjective z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.topologicalClosure
        (commutator ↥(Npre : Subgroup ↥(Hpre : Subgroup G)))) zpre
    have heQ_mk :
        eQ (QuotientGroup.mk' (Npre : Subgroup ↥(Hpre : Subgroup G)) g) =
          QuotientGroup.mk' (N : Subgroup ↥(H : Subgroup Q)) (φH g) := by
      change
        qMap (QuotientGroup.mk' (Npre : Subgroup ↥(Hpre : Subgroup G)) g) =
          QuotientGroup.mk' (N : Subgroup ↥(H : Subgroup Q)) (φH g)
      exact hqMap_mk g
    have hcongr_apply
        (a₀ : TopologicalAbelianization
          ↥(Npre : Subgroup ↥(Hpre : Subgroup G))) :
        (MulAut.congr eA)
            (ρpre (QuotientGroup.mk' (Npre : Subgroup ↥(Hpre : Subgroup G)) g))
            (eA a₀) =
          eA
            (ρpre
              (QuotientGroup.mk' (Npre : Subgroup ↥(Hpre : Subgroup G)) g)
              a₀) := by
      change
        eA
            (ρpre
              (QuotientGroup.mk' (Npre : Subgroup ↥(Hpre : Subgroup G)) g)
              (eA.symm (eA a₀))) =
          eA
            (ρpre
              (QuotientGroup.mk' (Npre : Subgroup ↥(Hpre : Subgroup G)) g)
              a₀)
      rw [eA.symm_apply_apply]
    rw [heQ_mk, hcongr_apply]
    exact (haction_mk g x).symm
  have hcomp_inj :
      Function.Injective (fun p : ↥(Hpre : Subgroup G) ⧸
          (Npre : Subgroup ↥(Hpre : Subgroup G)) => ρ (eQ p)) := by
    intro p₁ p₂ hp
    have hp' :
        (MulAut.congr eA) (ρpre p₁) = (MulAut.congr eA) (ρpre p₂) := by
      simpa [hcomp p₁, hcomp p₂] using hp
    have hp'' : ρpre p₁ = ρpre p₂ := (MulAut.congr eA).injective hp'
    exact hρpre_inj hp''
  intro q₁ q₂ hq
  rcases eQ.surjective q₁ with ⟨p₁, rfl⟩
  rcases eQ.surjective q₂ with ⟨p₂, rfl⟩
  exact congrArg eQ (hcomp_inj hq)

/--
Open normal subgroups inside open subgroups of a maximal finite-step solvable quotient inherit
faithful quotient conjugation actions once they contain the last derived subgroup.
-/
theorem injective_quotientConjAbelianization_of_containsLastDerived_of_abFaithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    (hG : IsAbFaithful G)
    {m : ℕ} (hm : 2 ≤ m)
    (H : OpenSubgroup (MaxSolvQuot G m))
    (N : OpenNormalSubgroup ↥(H : Subgroup (MaxSolvQuot G m)))
    (hContain : containsLastDerived (G := G) m H N) :
    Function.Injective
      (quotientConjugationTopologicalAbelianizationMap
        (G := ↥(H : Subgroup (MaxSolvQuot G m)))
        (N := (N : Subgroup ↥(H : Subgroup (MaxSolvQuot G m))))) := by
  exact
    injective_quotientConjAbelianization_of_containsLastDerived_of_isClosedMap
      (G := G) hG hm
      ((continuousToMaxSolvQuot G m).continuous_toFun.isClosedMap)
      H N hContain

/--
Ambient containment form of faithful quotient conjugation for open normal subgroups inside open
subgroups of a maximal finite-step solvable quotient.
-/
theorem inj_quotientConjAbelianization_of_lastDerivedSubgroup_le_map_subtype_of_abFaithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    (hG : IsAbFaithful G)
    {m : ℕ} (hm : 2 ≤ m)
    (H : OpenSubgroup (MaxSolvQuot G m))
    (N : OpenNormalSubgroup ↥(H : Subgroup (MaxSolvQuot G m)))
    (hN :
      lastDerivedSubgroup (G := G) m ≤
        (N : Subgroup ↥(H : Subgroup (MaxSolvQuot G m))).map
          ((H : Subgroup (MaxSolvQuot G m)).subtype)) :
    Function.Injective
      (quotientConjugationTopologicalAbelianizationMap
        (G := ↥(H : Subgroup (MaxSolvQuot G m)))
        (N := (N : Subgroup ↥(H : Subgroup (MaxSolvQuot G m))))) := by
  exact
    injective_quotientConjAbelianization_of_containsLastDerived_of_abFaithful
      (G := G) hG hm H N
      (containsLastDerived_of_lastDerivedSubgroup_le_map_subtype (G := G) hN)

/--
Open normal supergroups above the last derived subgroup inherit faithful quotient conjugation
actions under the ambient abelianization-faithful hypothesis.
-/
theorem injective_quotientConjAbelianization_of_openNormalSupergroup_of_abFaithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    (hG : IsAbFaithful G)
    {m : ℕ} (hm : 2 ≤ m)
    (U : OpenNormalSubgroup (MaxSolvQuot G m))
    (hU : lastDerivedSubgroup (G := G) m ≤ (U : Subgroup (MaxSolvQuot G m))) :
    Function.Injective
      (quotientConjugationTopologicalAbelianizationMap
        (G := MaxSolvQuot G m) (N := (U : Subgroup (MaxSolvQuot G m)))) := by
  let Q : Type u := MaxSolvQuot G m
  let UTop : OpenNormalSubgroup ↥((⊤ : OpenSubgroup Q) : Subgroup Q) := openNormalSubgroupTop U
  have hContain : containsLastDerived m (⊤ : OpenSubgroup Q) UTop := by
    intro x hx
    refine ⟨by simp only [OpenSubgroup.mem_top], ?_⟩
    have hxU : x ∈ U.toOpenSubgroup := hU hx
    change x ∈ U.toOpenSubgroup
    exact hxU
  have hTop :
      Function.Injective
        (quotientConjugationTopologicalAbelianizationMap
          (G := ↥((⊤ : OpenSubgroup Q) : Subgroup Q))
          (N := (UTop : Subgroup ↥((⊤ : OpenSubgroup Q) : Subgroup Q)))) := by
    exact
      injective_quotientConjAbelianization_of_containsLastDerived_of_abFaithful
        (G := G) (m := m) hG hm
        (H := (⊤ : OpenSubgroup Q)) (N := UTop) hContain
  exact
    inj_quotientConjugationTopologicalAbelianizationMap_of_openNormalSubgroupTop
      (G := Q) U hTop

/--
In a maximal finite-step solvable quotient, the center lies in the last derived subgroup under
the ambient abelianization-faithful hypothesis.
-/
theorem center_le_lastDerivedSubgroup_of_isAbFaithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbFaithful G)
    {m : ℕ} (hm : 1 ≤ m) :
    Subgroup.center (MaxSolvQuot G m) ≤ lastDerivedSubgroup (G := G) m := by
  by_cases hm1 : m = 1
  · subst hm1
    change Subgroup.center (MaxSolvQuot G 1) ≤ (⊤ : Subgroup (MaxSolvQuot G 1))
    exact le_top
  have hm2 : 2 ≤ m := Nat.succ_le_of_lt (lt_of_le_of_ne hm (Ne.symm hm1))
  intro z hz
  let Q : Type u := MaxSolvQuot G m
  let : TotallyDisconnectedSpace Q := by
    dsimp [Q, MaxSolvQuot]
    exact ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (topDerivedTop G m)
      (show IsClosed ((topDerivedTop G m : Subgroup G) : Set G) by infer_instance)
  let K : Subgroup Q := lastDerivedSubgroup (G := G) m
  have hKNormal : K.Normal := by
    dsimp [K, lastDerivedSubgroup]
    infer_instance
  have hKClosed : IsClosed ((K : Subgroup Q) : Set Q) := by
    dsimp [K, lastDerivedSubgroup]
    infer_instance
  let Kclosed : ClosedSubgroup Q := ⟨K, hKClosed⟩
  change z ∈ K
  have hK_eq :
      K = sInf {N : Subgroup Q | IsOpen (N : Set Q) ∧ K ≤ N ∧ N.Normal} := by
    change (Kclosed : Subgroup Q) =
      sInf {N : Subgroup Q | IsOpen (N : Set Q) ∧ K ≤ N ∧ N.Normal}
    exact ProCGroups.ProC.closedSubgroup_eq_sInf_openNormal (G := Q) Kclosed
  rw [hK_eq]
  simp only [Subgroup.mem_sInf]
  intro N hN
  let U : OpenNormalSubgroup Q :=
    { toSubgroup := N
      isOpen' := hN.1
      isNormal' := hN.2.2 }
  have hUNormal : (U : Subgroup Q).Normal := U.isNormal'
  have hρinj :
      Function.Injective
        (quotientConjugationTopologicalAbelianizationMap
          (G := Q) (N := (U : Subgroup Q))) :=
    injective_quotientConjAbelianization_of_openNormalSupergroup_of_abFaithful
      (G := G) (m := m) hG hm2 U hN.2.1
  have hρz :
      quotientConjugationTopologicalAbelianizationMap
          (G := Q) (N := (U : Subgroup Q))
          (QuotientGroup.mk' (U : Subgroup Q) z) = 1 :=
    quotientConjugationTopologicalAbelianizationMap_mk_eq_one_of_mem_center
      (G := Q) (N := (U : Subgroup Q)) (x := z) hz
  have hzU : z ∈ (U : Subgroup Q) := by
    apply (QuotientGroup.eq_one_iff (N := (U : Subgroup Q)) z).mp
    apply hρinj
    simpa using hρz
  simpa [U] using hzU

/--
If the center lies in a normal subgroup whose topological abelianization action has no
nontrivial fixed points, then injectivity of the natural map to topological abelianization
forces the ambient center to be trivial.
-/
theorem center_eq_bot_of_center_le_of_noNontrivialFixedPoints_of_inj_topologicalAbelianization
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    {K : Subgroup Q} [K.Normal]
    (hcenter : Subgroup.center Q ≤ K)
    (hfixed :
      HasNoNontrivialFixedPoints
        (quotientConjugationTopologicalAbelianizationMap (G := Q) (N := K)))
    (hinj : Function.Injective (TopologicalAbelianization.mk ↥K)) :
    Subgroup.center Q = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hzK : z ∈ K := hcenter hz
  let zK : K := ⟨z, hzK⟩
  have hzfix :
      ∀ q : Q ⧸ K,
        quotientConjugationTopologicalAbelianizationMap (G := Q) (N := K) q
          (TopologicalAbelianization.mk ↥K zK) =
            TopologicalAbelianization.mk ↥K zK := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K q
    exact
      quotientConjAbMap_apply_mk_of_commute
        (G := Q) (N := K) (g := g) (x := zK)
        ((Subgroup.mem_center_iff.mp hz) g)
  have hzab1 : TopologicalAbelianization.mk ↥K zK = 1 := by
    exact hfixed (TopologicalAbelianization.mk ↥K zK) hzfix
  have hzK1 : zK = 1 := by
    exact hinj hzab1
  simpa [zK] using congrArg Subtype.val hzK1

end ProCGroups.FiniteStepSolvableQuotients
