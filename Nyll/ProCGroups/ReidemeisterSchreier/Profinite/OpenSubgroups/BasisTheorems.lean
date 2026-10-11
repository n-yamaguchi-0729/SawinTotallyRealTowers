/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Completion.FiniteQuotientLifts
import Nyll.ProCGroups.Topologies.TopologicallyCharacteristicSubgroups
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.ExactRightSchreierGeneration

/-!
# From exact Schreier generators to free pro-\(C\) bases

This module turns the exact right-Schreier generation theorem into completion
and basis statements.  It isolates finite-quotient lifting, compares dense
abstract free groups with their pro-\(C\) completions, and constructs compact
pointed and converging-set bases for open subgroups.
-/

open scoped Topology Pointwise

namespace ReidemeisterSchreier
namespace Profinite

open ProCGroups
open ProCGroups.FreeProC
open ProCGroups.ProC

universe u


/--
Finite-discrete quotient lift property for a dense abstract Schreier model of an open subgroup.
-/
def DenseAbstractSchreierFiniteQuotientLiftProperty
    (C : ProCGroups.FiniteGroupClass.{u})
    {F : Type u} [Group F] [TopologicalSpace F]
    (H : OpenSubgroup F)
    {Y : Type u}
    (φY : FreeGroup Y →* ↥(H : Subgroup F)) : Prop :=
  ∀ {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
      [Finite Q] [DiscreteTopology Q],
      C Q →
      ∀ ψQ : FreeGroup Y →* Q,
        ∃! φbar : ↥(H : Subgroup F) →* Q,
          Continuous φbar ∧ φbar.comp φY = ψQ

/-- Transport the finite-quotient lift property across an abstract free-group equivalence. -/
theorem denseAbstractSchreierFiniteQuotientLiftProperty_of_equiv
    (C : ProCGroups.FiniteGroupClass.{u})
    {F : Type u} [Group F] [TopologicalSpace F]
    (H : OpenSubgroup F)
    {L : Type u} [Group L]
    {Y : Type u}
    (eY : FreeGroup Y ≃* L)
    (ψ : L →* ↥(H : Subgroup F))
    (hψfinite :
      ∀ {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
        [Finite Q] [DiscreteTopology Q],
        C Q →
        ∀ χL : L →* Q,
          ∃! φbar : ↥(H : Subgroup F) →* Q,
            Continuous φbar ∧ φbar.comp ψ = χL) :
    DenseAbstractSchreierFiniteQuotientLiftProperty
      (C := C) H (ψ.comp eY.toMonoidHom) := by
  intro Q _ _ _ _ _ hQ ψQ
  let χL : L →* Q := ψQ.comp eY.symm.toMonoidHom
  have hχLFac : χL.comp eY.toMonoidHom = ψQ := by
    apply MonoidHom.ext
    intro w
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_ofClass,
        Function.comp_apply,
  MulEquiv.symm_apply_apply, χL]
  rcases hψfinite hQ χL with ⟨φbar, hφbar, hφbarUnique⟩
  refine ⟨φbar, ?_, ?_⟩
  · refine ⟨hφbar.1, ?_⟩
    apply MonoidHom.ext
    intro w
    calc
      (φbar.comp (ψ.comp eY.toMonoidHom)) w = (φbar.comp ψ) (eY w) := rfl
      _ = χL (eY w) := by
        exact congrArg (fun f : L →* Q => f (eY w)) hφbar.2
      _ = ψQ w := by
        exact congrArg (fun f : FreeGroup Y →* Q => f w) hχLFac
  · intro φbar' hφbar'
    apply hφbarUnique
    refine ⟨hφbar'.1, ?_⟩
    apply MonoidHom.ext
    intro l
    rcases eY.surjective l with ⟨w, rfl⟩
    have hw' :
        (φbar'.comp (ψ.comp eY.toMonoidHom)) w = ψQ w :=
      congrArg (fun f : FreeGroup Y →* Q => f w) hφbar'.2
    calc
      (φbar'.comp ψ) (eY w) = (φbar'.comp (ψ.comp eY.toMonoidHom)) w := rfl
      _ = ψQ w := hw'
      _ = χL (eY w) := by simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp,
          MonoidHom.coe_ofClass, Function.comp_apply,
  MulEquiv.symm_apply_apply, χL]

/--
A dense abstract Schreier model with the finite-discrete quotient lift property is the pro-\(C\)
completion of that abstract free group.
-/
theorem isProCCompletion_denseAbstractSchreier_of_finiteQuotientLifts
    (C : ProCGroups.FiniteGroupClass.{u})
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (H : OpenSubgroup F)
    {Y : Type u}
    [TopologicalSpace (FreeGroup Y)] [IsTopologicalGroup (FreeGroup Y)]
    {φY : FreeGroup Y →ₜ* ↥(H : Subgroup F)}
    (hφYdense : DenseRange φY)
    (hfinite :
      DenseAbstractSchreierFiniteQuotientLiftProperty (C := C) H φY.toMonoidHom) :
    ProCGroups.Completion.IsProCCompletion
      (C)
      (FreeGroup Y) ↥(H : Subgroup F) φY := by
  have hHproC : ProCGroups.ProC.HasOpenNormalBasisInClass C ↥(H : Subgroup F) := by
    exact
      ProCGroups.ProC.HasOpenNormalBasisInClass.of_isClosed_subgroup
        (C := C) hIso hSub hF.hasOpenNormalBasisInClass (H : Subgroup F)
        (Subgroup.isClosed_of_isOpen (H : Subgroup F) H.isOpen')
  refine ProCGroups.Completion.isProCCompletion_of_finiteQuotientLifts
    (C := C) (hForm := hForm) (G := FreeGroup Y) (Ghat := ↥(H : Subgroup F))
    hHproC (ι := φY) hφYdense ?_
  intro Q _ _ _ _ _ hQ ψQ
  rcases hfinite hQ ψQ.toMonoidHom with ⟨φbar, hφbar, hφbarUnique⟩
  let φbarCont : ↥(H : Subgroup F) →ₜ* Q :=
    { toMonoidHom := φbar
      continuous_toFun := hφbar.1 }
  refine ⟨φbarCont, ?_, ?_⟩
  · apply ContinuousMonoidHom.toMonoidHom_injective
    exact hφbar.2
  · intro φbarCont' hφbarCont'
    apply ContinuousMonoidHom.toMonoidHom_injective
    exact hφbarUnique φbarCont'.toMonoidHom
      ⟨φbarCont'.continuous_toFun, congrArg ContinuousMonoidHom.toMonoidHom hφbarCont'⟩



/--
A topologically generating subset of an open subgroup generates a dense subgroup after including
it into the ambient group.
-/
theorem subgroup_le_topologicalClosure_of_topologicallyGenerates_local
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : OpenSubgroup G)
    {S : Set ↥(H : Subgroup G)}
    (hS : Generation.TopologicallyGenerates (G := ↥(H : Subgroup G)) S) :
    (H : Subgroup G) ≤
      (Subgroup.closure (((↑) : ↥(H : Subgroup G) → G) '' S)).topologicalClosure := by
  let D : Subgroup ↥(H : Subgroup G) := Subgroup.closure S
  have hDense : Dense (D : Set ↥(H : Subgroup G)) :=
    (Generation.topologicallyGenerates_iff_dense (G := ↥(H : Subgroup G)) (X := S)).1 hS
  rw [Subtype.dense_iff] at hDense
  have hmap :
      D.map (H : Subgroup G).subtype =
        Subgroup.closure (((↑) : ↥(H : Subgroup G) → G) '' S) := by
    simpa [TopologicalGroup.image_subtype_eq_map] using ((H : Subgroup G).subtype.map_closure S)
  have himage :
      ((↑) : ↥(H : Subgroup G) → G) '' (D : Set ↥(H : Subgroup G)) =
        ((D.map (H : Subgroup G).subtype : Subgroup G) : Set G) := by
    exact TopologicalGroup.image_subtype_eq_map (H : Subgroup G).subtype D
  intro g hg
  have hg' :
      g ∈ closure (((D.map (H : Subgroup G).subtype : Subgroup G) : Set G)) := by
    have : g ∈ closure (((↑) : ↥(H : Subgroup G) → G) '' (D : Set ↥(H : Subgroup G))) :=
      hDense hg
    rwa [himage] at this
  have hg'' :
      g ∈ ((D.map (H : Subgroup G).subtype).topologicalClosure : Set G) := by
    simpa [Subgroup.topologicalClosure_coe] using hg'
  rw [← hmap]
  exact hg''

/-- If an open subgroup is topologically finitely generated,
then so is the ambient compact group. -/
theorem topologicallyFinitelyGenerated_of_openSubgroup_local
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G]
    (H : OpenSubgroup G)
    (hH : ProCGroups.FiniteGeneration.TopologicallyFinitelyGenerated ↥(H : Subgroup G)) :
    ProCGroups.FiniteGeneration.TopologicallyFinitelyGenerated G := by
  classical
  rcases hH with ⟨sH, hsH⟩
  let τ := openSubgroupRightCosetSection (F := G) H
  let sReps : Finset G := Finset.univ.image τ
  let s : Finset G := sReps ∪ sH.image Subtype.val
  let K : Subgroup G := Subgroup.closure (s : Set G)
  have hHle' :
      (H : Subgroup G) ≤
        (Subgroup.closure
          (((↑) : ↥(H : Subgroup G) → G) ''
            ((sH : Finset ↥(H : Subgroup G)) : Set ↥(H : Subgroup G)))).topologicalClosure :=
    subgroup_le_topologicalClosure_of_topologicallyGenerates_local H (by simpa using hsH)
  have hImageLe : Subgroup.closure
      (((↑) : ↥(H : Subgroup G) → G) ''
        ((sH : Finset ↥(H : Subgroup G)) : Set ↥(H : Subgroup G))) ≤ K := by
    refine Subgroup.closure_mono ?_
    intro g hg
    rcases hg with ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ sH.image Subtype.val := by
      exact Finset.mem_image.mpr ⟨x, by simpa using hx, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_union_right sReps hx')
  have hImageLe' :
      (Subgroup.closure
        (((↑) : ↥(H : Subgroup G) → G) ''
          ((sH : Finset ↥(H : Subgroup G)) : Set ↥(H : Subgroup G)))).topologicalClosure ≤
        K.topologicalClosure :=
    Subgroup.topologicalClosure_minimal _
      (hImageLe.trans (Subgroup.le_topologicalClosure _))
      (Subgroup.isClosed_topologicalClosure _)
  have hHle : (H : Subgroup G) ≤ K.topologicalClosure := fun g hg => hImageLe' (hHle' hg)
  have htop : K.topologicalClosure = ⊤ := by
    apply top_unique
    intro g _hg
    let q : OpenSubgroupRightQuotient H := openSubgroupRightCoset H g
    have hEq0 : openSubgroupRightCoset H (τ q) = q :=
      openSubgroupRightCosetSection_spec (F := G) H q
    have hEq :
        openSubgroupRightCoset H g = openSubgroupRightCoset H (τ q) := by
      simpa [q] using hEq0.symm
    have hrel : QuotientGroup.rightRel (H : Subgroup G) g (τ q) :=
      Quotient.exact' hEq
    have hgH0 : τ q * g⁻¹ ∈ (H : Subgroup G) := by
      simpa using (QuotientGroup.rightRel_apply.mp hrel)
    have hgH : g * (τ q)⁻¹ ∈ (H : Subgroup G) := by
      simpa [mul_inv_rev, mul_assoc] using ((H : Subgroup G).inv_mem hgH0)
    have hgH' : g * (τ q)⁻¹ ∈ (K.topologicalClosure : Subgroup G) :=
      hHle hgH
    have hτK : τ q ∈ (K.topologicalClosure : Subgroup G) := by
      have hτmem : τ q ∈ (sReps : Set G) := by
        exact Finset.mem_coe.2 <| Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
      have hτmem' : τ q ∈ (s : Set G) := by
        exact Finset.mem_coe.2 (Finset.mem_union_left _ hτmem)
      exact Subgroup.le_topologicalClosure K (Subgroup.subset_closure hτmem')
    have hmul :
        (g * (τ q)⁻¹) * τ q ∈ (K.topologicalClosure : Subgroup G) :=
      (K.topologicalClosure).mul_mem hgH' hτK
    simpa [mul_assoc] using hmul
  refine ⟨s, ?_⟩
  simpa [Generation.TopologicallyGenerates, K, s] using htop



/--
A finite converging-set free pro-\(C\) basis realizes the pro-\(C\) completion of the abstract
free group on the same basis.
-/
theorem isProCCompletion_freeGroupLift_of_finiteBasis
    {C : ProCGroups.FiniteGroupClass.{u}}
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    {X : Type u} [Finite X]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι) :
    ProCGroups.Completion.IsProCCompletion
      (C)
      (FreeGroup X) F
      { toMonoidHom := FreeGroup.lift ι
        continuous_toFun := continuous_of_discreteTopology } := by
  let φ : FreeGroup X →ₜ* F :=
    { toMonoidHom := FreeGroup.lift ι
      continuous_toFun := continuous_of_discreteTopology }
  change ProCGroups.Completion.IsProCCompletion
    (C) (FreeGroup X) F φ
  refine
    { hasOpenNormalBasisInClass := hF.hasOpenNormalBasisInClass
      denseRange := ?_
      existsUnique_lift := ?_ }
  · change DenseRange (FreeGroup.lift ι)
    exact denseRange_freeGroupLift_of_topologicallyGenerates
      (F := F) (X := X) hF.generates_range
  · intro G _ _ _ _ _ _ hG ψ
    let φX : X → G := fun x => ψ (FreeGroup.of x)
    let S : Subgroup G := (Subgroup.closure (Set.range φX)).topologicalClosure
    let : CompactSpace S :=
      (Subgroup.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal.compactSpace
    have hSproC : ProCGroups.ProC.HasOpenNormalBasisInClass C (S) := by
      exact
        ProCGroups.ProC.HasOpenNormalBasisInClass.of_isClosed_subgroup
          (C := C) hIso hSub hG S (Subgroup.isClosed_topologicalClosure _)
    let φS : X → S := fun x =>
      ⟨φX x, Subgroup.le_topologicalClosure _
        (Subgroup.subset_closure ⟨x, rfl⟩)⟩
    have hφSconv : FamilyConvergesToOneAlongOpenSubgroups (G := S) φS := by
      exact FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := S) φS
    have hφSgen :
        Generation.TopologicallyGenerates (G := S) (Set.range φS) := by
      simpa [S, φS, φX] using
        topologicallyGenerates_topologicalClosure_of_range φX
    rcases hF.existsUnique_lift hSproC φS hφSconv hφSgen with
      ⟨σS, hσS, _⟩
    let σ : F →ₜ* G :=
      { toMonoidHom := S.subtype.comp σS
        continuous_toFun := by
          simpa using continuous_subtype_val.comp hσS.1 }
    have hσfac : σ.comp φ = ψ := by
      apply ContinuousMonoidHom.toMonoidHom_injective
      apply FreeGroup.ext_hom
      intro x
      change (S.subtype.comp σS) (FreeGroup.lift ι (FreeGroup.of x)) = ψ (FreeGroup.of x)
      simpa [φS, φX] using congrArg Subtype.val (hσS.2 x)
    refine ⟨σ, hσfac, ?_⟩
    intro g hg
    apply ContinuousMonoidHom.toMonoidHom_injective
    apply continuousMonoidHom_eq_of_agrees_on_topologicallyGeneratingSet
      (G := F) (A := G) hF.generates_range g.continuous_toFun σ.continuous_toFun
    intro y hy
    rcases hy with ⟨x, rfl⟩
    have hσx := congrArg (fun k : FreeGroup X →ₜ* G => k (FreeGroup.of x)) hσfac
    have hgx := congrArg (fun k : FreeGroup X →ₜ* G => k (FreeGroup.of x)) hg
    have hσx' : σ (ι x) = ψ (FreeGroup.of x) := by
      change σ (FreeGroup.lift ι (FreeGroup.of x)) = ψ (FreeGroup.of x) at hσx
      simpa using hσx
    have hgx' : g (ι x) = ψ (FreeGroup.of x) := by
      change g (FreeGroup.lift ι (FreeGroup.of x)) = ψ (FreeGroup.of x) at hgx
      simpa using hgx
    exact hgx'.trans hσx'.symm

/--
If a finite generating family has the same cardinality as an abstract free model whose
completion is the target, then that family realizes the same pro-C completion. The finite index
type is arbitrary in the ambient universe.
-/
theorem isProCCompletion_freeGroupLift_of_exactGeneratingFamily_of_completion
    {C : ProCGroups.FiniteGroupClass.{u}}
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    {Y Z : Type u} [Finite Z]
    [TopologicalSpace (FreeGroup Y)] [IsTopologicalGroup (FreeGroup Y)]
    [DiscreteTopology (FreeGroup Y)]
    [TopologicalSpace (FreeGroup Z)] [IsTopologicalGroup (FreeGroup Z)]
    [DiscreteTopology (FreeGroup Z)]
    (hYZcard : Nat.card Y = Nat.card Z)
    {φY : FreeGroup Y →ₜ* H}
    (hCompY :
      ProCGroups.Completion.IsProCCompletion
        (C) (FreeGroup Y) H φY)
    {κ : Z → H}
    (hκ : Generation.GeneratesAndConvergesToOneAlongOpenSubgroups (G := H) (Set.range κ)) :
    ProCGroups.Completion.IsProCCompletion
      (C)
      (FreeGroup Z) H
      { toMonoidHom := FreeGroup.lift κ
        continuous_toFun := continuous_of_discreteTopology } := by
  have hYfin : Finite Y := by
    by_cases h0 : Nat.card Z = 0
    · have : IsEmpty Z :=
        (Nat.card_eq_zero.1 h0).resolve_right <| Finite.not_infinite ‹_›
      have hκrange : Set.range κ = (∅ : Set H) := by
        ext z
        constructor
        · rintro ⟨x, rfl⟩
          exact isEmptyElim x
        · intro hz
          simp only [Set.mem_empty_iff_false] at hz
      have hHtriv : ∀ x : H, x = 1 := by
        intro x
        have hxmem :
            x ∈ ((Subgroup.closure (Set.range κ)).topologicalClosure : Set H) := by
          have hκgen : Generation.TopologicallyGenerates (G := H) (Set.range κ) := hκ.1
          rw [Generation.TopologicallyGenerates] at hκgen
          rw [hκgen]
          simp only [Subgroup.coe_top, Set.mem_univ]
        have hxmemEmpty :
            x ∈ ((Subgroup.closure ((∅ : Set H))).topologicalClosure : Set H) := by
          simpa [hκrange] using hxmem
        simpa [Subgroup.coe_topologicalClosure_bot, closure_singleton] using hxmemEmpty
      have hYempty : IsEmpty Y := by
        refine ⟨fun y => ?_⟩
        rcases
            exists_nontrivial_topologicallyCyclic_proC_of_finiteGroupClass
              C hQuot hcyc with
          ⟨A, _instGroupA, _instTopA, _instTopGroupA, _instCompactA, _instT2A,
            _instTDA, hA, a, ha1, _hgena⟩
        let ψY : FreeGroup Y →ₜ* A :=
          { toMonoidHom := FreeGroup.lift (fun _ : Y => a)
            continuous_toFun := continuous_of_discreteTopology }
        have hψYne : ψY (FreeGroup.of y) ≠ 1 := by
          change FreeGroup.lift (fun _ : Y => a) (FreeGroup.of y) ≠ 1
          simpa using ha1
        rcases hCompY.existsUnique_lift hA ψY with
          ⟨σ, hσ, _⟩
        have hyfac :=
          congrArg (fun f : FreeGroup Y →ₜ* A => f (FreeGroup.of y)) hσ
        have hyEq : ψY (FreeGroup.of y) = 1 := by
          calc
            ψY (FreeGroup.of y) = σ (φY (FreeGroup.of y)) := hyfac.symm
            _ = σ 1 := by rw [hHtriv (φY (FreeGroup.of y))]
            _ = 1 := map_one σ
        exact hψYne hyEq
      let : IsEmpty Y := hYempty
      infer_instance
    · exact Nat.finite_of_card_ne_zero (α := Y) (by rw [hYZcard]; exact h0)
  let : Finite Y := hYfin
  have hFreeY :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C)
        Y H (fun y => φY (FreeGroup.of y)) := by
    exact
      proCCompletionOfAbstractFreeGroup_is_free
        (C := C)
        (X := Y) (Fhat := H) (ι := φY) hCompY
  have hcardinal : Cardinal.mk Y = Cardinal.mk Z := by
    exact Cardinal.mk_congr
      ((Finite.equivFinOfCardEq hYZcard).trans
        (Finite.equivFinOfCardEq (α := Z) rfl).symm)
  have hFreeκ :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) Z H κ := by
    exact
      finite_generatingFamily_is_basis_of_finiteGroupClass
        (C := C) (X := Y) (Y := Z) hFreeY hcardinal hκ.1
  exact
    isProCCompletion_freeGroupLift_of_finiteBasis
      (C := C) hSub hIso hFreeκ


/--
Compact pointed basis bridge: adjoining the point at infinity to a discrete converging basis,
the open subgroup inherits a compact pointed right Schreier basis.
-/
theorem exists_compactPointedBasis_openSubgroup_of_freeProCOnConvergingSet
    (C : ProCGroups.FiniteGroupClass.{u})
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    {X : Type u}
    [TopologicalSpace X] [DiscreteTopology X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (H : OpenSubgroup F) :
    ∃ κ : OpenSubgroupRightQuotient H × OnePoint X → ↥(H : Subgroup F),
      Continuous κ ∧
      (∀ q : OpenSubgroupRightQuotient H, κ (q, OnePoint.infty) = 1) ∧
      κ (openSubgroupRightCoset H (1 : F), OnePoint.infty) = 1 ∧
      IsCompact (Set.range κ) ∧
      IsClosed (Set.range κ) ∧
      IsEpimorphicallyPointedFreeProCGroupOn
        (C := C)
        (Set.range κ)
        ⟨κ (openSubgroupRightCoset H (1 : F), OnePoint.infty),
          ⟨(openSubgroupRightCoset H (1 : F), OnePoint.infty), rfl⟩⟩
        ↥(H : Subgroup F) Subtype.val := by
  classical
  let iInf : OnePoint X → F := fun z => z.elim 1 ι
  have hιTendsto : Filter.Tendsto ι Filter.cofinite (𝓝 (1 : F)) := by
    rw [Filter.tendsto_def]
    intro s hs
    rcases mem_nhds_iff.mp hs with ⟨W, hWs, hWopen, h1W⟩
    rcases ProCGroups.ProC.exists_openNormalSubgroup_sub_open_nhds_of_one
        (G := F) hWopen h1W with
      ⟨U, hUW⟩
    have hfinite : {x : X | ι x ∉ (U : Set F)}.Finite :=
      hF.convergesToOneAlongOpenSubgroups U.toOpenSubgroup
    have hcof : ∀ᶠ x : X in Filter.cofinite, ι x ∈ (U : Set F) :=
      Filter.eventually_cofinite.2 hfinite
    exact hcof.mono fun x hx => hWs (hUW hx)
  have hPointed :
      IsEpimorphicallyPointedFreeProCGroupOn
        (C := C)
        (OnePoint X) OnePoint.infty F iInf := by
    refine ⟨hF.hasOpenNormalBasisInClass, ?_, by simp only [OnePoint.elim_infty, iInf], ?_, ?_⟩
    · rw [OnePoint.continuous_iff_from_discrete]
      simpa [iInf] using hιTendsto
    · have hsub : Set.range ι ⊆ Set.range iInf := by
        rintro y ⟨x, rfl⟩
        exact ⟨(x : OnePoint X), rfl⟩
      exact Generation.topologicallyGenerates_mono (G := F) hF.generates_range hsub
    · intro G _ _ _ _ _ _ hG φ hφ hφ0 hgenφ
      let ψ : X → G := fun x => φ x
      have hψTendsto : Filter.Tendsto ψ Filter.cofinite (𝓝 (1 : G)) := by
        have hraw := (OnePoint.continuous_iff_from_discrete (f := φ)).1 hφ
        simpa [ψ, hφ0] using hraw
      have hψconv : FamilyConvergesToOneAlongOpenSubgroups (G := G) ψ := by
        intro U
        exact Filter.eventually_cofinite.mp <|
          hψTendsto (U.isOpen'.mem_nhds U.one_mem')
      have hφrange : Set.range φ = Set.range ψ ∪ ({1} : Set G) := by
        ext z
        constructor
        · rintro ⟨x, rfl⟩
          refine OnePoint.rec ?_ ?_ x
          · right
            simpa [iInf] using hφ0
          · intro y
            left
            exact ⟨y, rfl⟩
        · intro hz
          rcases hz with hz | hz
          · rcases hz with ⟨y, rfl⟩
            exact ⟨(y : OnePoint X), rfl⟩
          · exact ⟨OnePoint.infty, hφ0.trans hz.symm⟩
      have hψgen : Generation.TopologicallyGenerates (G := G) (Set.range ψ) := by
        have hgenφ' :
            Generation.TopologicallyGenerates (G := G) (Set.range ψ ∪ ({1} : Set G)) := by
          simpa [hφrange] using hgenφ
        exact (Generation.topologicallyGenerates_union_one_iff (G := G) (X := Set.range ψ)).1
          hgenφ'
      rcases hF.existsUnique_lift hG ψ hψconv hψgen with ⟨f, hf, huniq⟩
      refine ⟨f, ⟨hf.1, ?_⟩, ?_⟩
      · intro x
        refine OnePoint.rec ?_ ?_ x
        · calc
            f (iInf OnePoint.infty) = f 1 := rfl
            _ = 1 := map_one f
            _ = φ OnePoint.infty := hφ0.symm
        · intro y
          exact hf.2 y
      · intro g hg
        apply huniq g
        refine ⟨hg.1, ?_⟩
        intro y
        simpa [iInf, ψ] using hg.2 (y : OnePoint X)
  exact
    exists_pointedFreeRightSchreierGeneratorFamily_of_openSubgroup
      (C := C) hForm hSub hIso hExt hPointed H



end Profinite
end ReidemeisterSchreier
