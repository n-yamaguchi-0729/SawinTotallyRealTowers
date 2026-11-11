/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Data.Finsupp.Ext
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import Nyll.GaloisCohomology.Cyclic.IntegralCoefficientCohomology
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology
public import Nyll.GaloisCohomology.GroupTheory.GroupEquivComplexComparison
public import Nyll.GaloisCohomology.GroupTheory.RepresentationUniverseLift

/-!
# Connecting maps for the independent-universe integral owner

The existing group/carrier lift is removed by its actual cochain reindexing and coefficient
map. These maps form a natural isomorphism of the original complexes. Naturality of the same
snake diagram identifies their connecting morphisms. Composing with the already specified
integer coefficient comparison recovers the literal integer connecting map in universe zero.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Category

namespace IntegralGroupCohomology.Universe

variable (G : Type u) [Group G]

/-- Removing the same group/carrier lift is natural on the actual cochains. -/
def nativeCochainsCommonNatIso :
    nativeFunctor.{u, u} G ⋙ groupCohomology.cochainsFunctor (ULift.{u} ℤ) (ULift.{u} G) ≅
      IntegralGroupCohomology.coefficientFunctor G ⋙
        groupCohomology.cochainsFunctor (ULift.{u} ℤ) G :=
  NatIso.ofComponents (fun A => groupCohomology.groupEquivComplexIso
    (MulEquiv.ulift : ULift.{u} G ≃* G) (nativeCarrierEquiv A)
    (nativeCarrierEquiv_comm A)) (by
      intro A B f
      apply HomologicalComplex.hom_ext
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

variable {G}

/-- The existing common-universe comparison preserves the actual connecting map. -/
theorem δ_cohomologyIsoCommon {X : ShortComplex (Rep.{u} ℤ G)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ (cohomologyIsoCommon X.X₁ j).hom =
      (cohomologyIsoCommon X.X₃ i).hom ≫ IntegralGroupCohomology.δ hX i j hij := by
  let X' := X.map (nativeFunctor G)
  let Y := X.map (IntegralGroupCohomology.coefficientFunctor G)
  have hX' : X'.ShortExact := by
    simpa only [X', nativeFunctor, ShortComplex.map_comp] using
      IntegralGroupCohomology.coefficient_shortExact
        (S := X.map (Rep.universeLiftFunctor ℤ G))
        (Rep.universeLiftFunctor_shortExact ℤ G hX)
  have hY : Y.ShortExact := IntegralGroupCohomology.coefficient_shortExact hX
  let E : X'.map (groupCohomology.cochainsFunctor (ULift.{u} ℤ) (ULift.{u} G)) ≅
      Y.map (groupCohomology.cochainsFunctor (ULift.{u} ℤ) G) :=
    X.mapNatIso (nativeCochainsCommonNatIso G)
  let dX : groupCohomology X'.X₃ i ⟶ groupCohomology X'.X₁ j :=
    groupCohomology.δ hX' i j hij
  let dY : groupCohomology Y.X₃ i ⟶ groupCohomology Y.X₁ j :=
    groupCohomology.δ hY i j hij
  let c₁ : groupCohomology X'.X₁ j ⟶ groupCohomology Y.X₁ j :=
    HomologicalComplex.homologyMap E.hom.τ₁ j
  let c₃ : groupCohomology X'.X₃ i ⟶ groupCohomology Y.X₃ i :=
    HomologicalComplex.homologyMap E.hom.τ₃ i
  have hn : dX ≫ c₁ = c₃ ≫ dY :=
    HomologicalComplex.HomologySequence.δ_naturality E.hom
      (groupCohomology.map_cochainsFunctor_shortExact hX')
      (groupCohomology.map_cochainsFunctor_shortExact hY) i j hij
  exact (IntegralGroupCohomology.integerScalars.map_comp dX c₁).symm.trans
    ((congrArg (fun f : groupCohomology X'.X₃ i ⟶ groupCohomology Y.X₁ j =>
        IntegralGroupCohomology.integerScalars.map f) hn).trans
      (IntegralGroupCohomology.integerScalars.map_comp c₃ dY))

section Finite

variable [Fintype G]

/-- The same group/carrier lift is removed naturally on all actual Tate chains and cochains. -/
def nativeTateCommonNatIso :
    nativeFunctor.{u, u} G ⋙ tateComplexFunctor (ULift.{u} ℤ) (ULift.{u} G) ≅
      IntegralGroupCohomology.coefficientFunctor G ⋙ tateComplexFunctor (ULift.{u} ℤ) G :=
  NatIso.ofComponents (fun A => TateCohomology.groupEquivComplexIso
    (MulEquiv.ulift : ULift.{u} G ≃* G) (nativeCarrierEquiv A)
    (nativeCarrierEquiv_comm A)) (by
      intro A B f
      apply HomologicalComplex.hom_ext
      intro i
      cases i with
      | ofNat n =>
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          rfl
      | negSucc n =>
          apply ModuleCat.hom_ext
          apply LinearMap.toAddMonoidHom_injective
          apply Finsupp.addHom_ext
          intro g a
          let q : ULift.{u} G →* G := (MulEquiv.ulift : ULift.{u} G ≃* G).toMonoidHom
          let aA : (nativeFunctor G).obj A ⟶
              Rep.res q ((IntegralGroupCohomology.coefficientFunctor G).obj A) :=
            Rep.ofHom ⟨(nativeCarrierEquiv A).toLinearMap, nativeCarrierEquiv_comm A⟩
          let aB : (nativeFunctor G).obj B ⟶
              Rep.res q ((IntegralGroupCohomology.coefficientFunctor G).obj B) :=
            Rep.ofHom ⟨(nativeCarrierEquiv B).toLinearMap, nativeCarrierEquiv_comm B⟩
          change (groupHomology.chainsMap q aB).f n
              ((groupHomology.chainsMap (MonoidHom.id _) ((nativeFunctor G).map f)).f n
                (Finsupp.single g a)) =
            (groupHomology.chainsMap (MonoidHom.id G)
                ((IntegralGroupCohomology.coefficientFunctor G).map f)).f n
              ((groupHomology.chainsMap q aA).f n (Finsupp.single g a))
          rw [groupHomology.chainsMap_f_single, groupHomology.chainsMap_f_single,
            groupHomology.chainsMap_f_single, groupHomology.chainsMap_f_single]
          rfl)

/-- The existing common-universe Tate comparison preserves its actual connecting map. -/
theorem tateδ_tateIsoCommon {X : ShortComplex (Rep.{u} ℤ G)} (hX : X.ShortExact)
    (i : ℤ) :
    tateδ hX i ≫ (tateIsoCommon X.X₁ (i + 1)).hom =
      (tateIsoCommon X.X₃ i).hom ≫ IntegralGroupCohomology.tateδ hX i := by
  let X' := X.map (nativeFunctor G)
  let Y := X.map (IntegralGroupCohomology.coefficientFunctor G)
  have hX' : X'.ShortExact := by
    simpa only [X', nativeFunctor, ShortComplex.map_comp] using
      IntegralGroupCohomology.coefficient_shortExact
        (S := X.map (Rep.universeLiftFunctor ℤ G))
        (Rep.universeLiftFunctor_shortExact ℤ G hX)
  have hY : Y.ShortExact := IntegralGroupCohomology.coefficient_shortExact hX
  let E : X'.map (tateComplexFunctor (ULift.{u} ℤ) (ULift.{u} G)) ≅
      Y.map (tateComplexFunctor (ULift.{u} ℤ) G) :=
    X.mapNatIso (nativeTateCommonNatIso (G := G))
  let dX : tateCohomology X'.X₃ i ⟶ tateCohomology X'.X₁ (i + 1) :=
    TateCohomology.δ hX' i
  let dY : tateCohomology Y.X₃ i ⟶ tateCohomology Y.X₁ (i + 1) :=
    TateCohomology.δ hY i
  let c₁ : tateCohomology X'.X₁ (i + 1) ⟶ tateCohomology Y.X₁ (i + 1) :=
    HomologicalComplex.homologyMap E.hom.τ₁ (i + 1)
  let c₃ : tateCohomology X'.X₃ i ⟶ tateCohomology Y.X₃ i :=
    HomologicalComplex.homologyMap E.hom.τ₃ i
  have hn : dX ≫ c₁ = c₃ ≫ dY :=
    HomologicalComplex.HomologySequence.δ_naturality E.hom
      (TateCohomology.map_tateComplexFunctor_shortExact hX')
      (TateCohomology.map_tateComplexFunctor_shortExact hY) i (i + 1) rfl
  exact (IntegralGroupCohomology.integerScalars.map_comp dX c₁).symm.trans
    ((congrArg (fun f : tateCohomology X'.X₃ i ⟶ tateCohomology Y.X₁ (i + 1) =>
        IntegralGroupCohomology.integerScalars.map f) hn).trans
      (IntegralGroupCohomology.integerScalars.map_comp c₃ dY))

end Finite

section Original

variable {H : Type} [Group H]

/-- The specified independent-universe comparison recovers the literal integer connecting map. -/
theorem δ_cohomologyIsoOriginal {X : ShortComplex (Rep.{0} ℤ H)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ (cohomologyIsoOriginal X.X₁ j).hom =
      (cohomologyIsoOriginal X.X₃ i).hom ≫ groupCohomology.δ hX i j hij := by
  change δ hX i j hij ≫ ((cohomologyIsoCommon X.X₁ j).hom ≫
      (IntegralGroupCohomology.cohomologyIsoOriginal X.X₁ j).hom) =
    ((cohomologyIsoCommon X.X₃ i).hom ≫
      (IntegralGroupCohomology.cohomologyIsoOriginal X.X₃ i).hom) ≫
        groupCohomology.δ hX i j hij
  rw [← assoc, δ_cohomologyIsoCommon, assoc,
    IntegralGroupCohomology.δ_cohomologyIsoOriginal, ← assoc]

variable [Fintype H]

/-- The specified independent-universe comparison recovers the literal Tate connecting map. -/
theorem tateδ_tateIsoOriginal {X : ShortComplex (Rep.{0} ℤ H)} (hX : X.ShortExact)
    (i : ℤ) :
    tateδ hX i ≫ (tateIsoOriginal X.X₁ (i + 1)).hom =
      (tateIsoOriginal X.X₃ i).hom ≫ TateCohomology.δ hX i := by
  change tateδ hX i ≫ ((tateIsoCommon X.X₁ (i + 1)).hom ≫
      (IntegralGroupCohomology.tateIsoOriginal X.X₁ (i + 1)).hom) =
    ((tateIsoCommon X.X₃ i).hom ≫
      (IntegralGroupCohomology.tateIsoOriginal X.X₃ i).hom) ≫ TateCohomology.δ hX i
  rw [← assoc, tateδ_tateIsoCommon, assoc,
    IntegralGroupCohomology.tateδ_tateIsoOriginal, ← assoc]

end Original

end IntegralGroupCohomology.Universe
