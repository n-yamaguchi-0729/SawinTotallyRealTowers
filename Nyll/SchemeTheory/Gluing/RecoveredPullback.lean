/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Gluing.CoefficientCover
import Nyll.SchemeTheory.Gluing.RecoveredLocalModel
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! Actual recovered local charts and overlap maps after arbitrary base change. -/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Cover

variable {X Y : Scheme.{u}} (ψ : Y ⟶ X) (𝒰 : X.OpenCover)

/-- The pulled-back cover with charts in the order used by `Over.pullback`. -/
def swappedPullbackCover : Y.OpenCover :=
  Scheme.Cover.copy (𝒰.pullback₁ ψ) 𝒰.I₀
    (fun i => pullback (𝒰.f i) ψ) (fun i => pullback.snd (𝒰.f i) ψ)
    (Equiv.refl _) (fun i => pullbackSymmetry (𝒰.f i) ψ)
    (fun i => (pullbackSymmetry_hom_comp_fst (𝒰.f i) ψ).symm)

variable (M : ∀ i : 𝒰.I₀, Over (𝒰.X i))

/-- A local model viewed as a scheme over the original base. -/
def gluingLocalOver (i : 𝒰.I₀) : Over X := Over.mk ((M i).hom ≫ 𝒰.f i)
/-- An open chart viewed as a scheme over the original base. -/
def gluingChartOver (i : 𝒰.I₀) : Over X := Over.mk (𝒰.f i)
/-- The structure map from a local model to its open chart. -/
def gluingLocalStructure (i : 𝒰.I₀) : gluingLocalOver 𝒰 M i ⟶ gluingChartOver 𝒰 i :=
  Over.homMk (M i).hom rfl

/-- The overlap of a local model with a second open chart. -/
def gluingOverlapOver (ij : 𝒰.I₀ × 𝒰.I₀) : Over X :=
  Over.mk (pullback.fst ((M ij.1).hom ≫ 𝒰.f ij.1) (𝒰.f ij.2) ≫
    ((M ij.1).hom ≫ 𝒰.f ij.1))

/-- The first projection from a local overlap to its model. -/
def gluingOverlapFirst (i j : 𝒰.I₀) : gluingOverlapOver 𝒰 M (i, j) ⟶ gluingLocalOver 𝒰 M i :=
  Over.homMk (pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j)) rfl

/-- The second projection from a local overlap to its open chart. -/
def gluingOverlapSecond (i j : 𝒰.I₀) : gluingOverlapOver 𝒰 M (i, j) ⟶ gluingChartOver 𝒰 j :=
  Over.homMk (pullback.snd ((M i).hom ≫ 𝒰.f i) (𝒰.f j)) pullback.condition.symm

/-- The literal pullback of a relative product is the product over the new base. -/
theorem overPullback_product_isPullback {P A C : Over X}
    (d : P ⟶ A) (r : P ⟶ C) (h : IsPullback d.left r.left A.hom C.hom) :
    IsPullback ((Over.pullback ψ).map d).left ((Over.pullback ψ).map r).left
      ((Over.pullback ψ).obj A).hom ((Over.pullback ψ).obj C).hom := by
  let a : A ⟶ Over.mk (𝟙 X) := Over.homMk A.hom (Category.comp_id A.hom)
  let c : C ⟶ Over.mk (𝟙 X) := Over.homMk C.hom (Category.comp_id C.hom)
  have h' := overCoefficientPullback_map_isPullback ψ d r a c h
  let e0 : ((Over.pullback ψ).obj (Over.mk (𝟙 X))).left ≅ Y :=
    asIso (pullback.snd (𝟙 X) ψ)
  refine h'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e0 ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change ((Over.pullback ψ).map a).left ≫
      ((Over.pullback ψ).obj (Over.mk (𝟙 X))).hom =
        𝟙 _ ≫ ((Over.pullback ψ).obj A).hom
    rw [Category.id_comp]
    exact Over.w ((Over.pullback ψ).map a)
  · change ((Over.pullback ψ).map c).left ≫
      ((Over.pullback ψ).obj (Over.mk (𝟙 X))).hom =
        𝟙 _ ≫ ((Over.pullback ψ).obj C).hom
    rw [Category.id_comp]
    exact Over.w ((Over.pullback ψ).map c)

theorem recoveredPullbackOverlap_isPullback (i j : 𝒰.I₀) :
    IsPullback ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M i j)).left
      ((Over.pullback ψ).map (gluingOverlapSecond 𝒰 M i j)).left
      ((Over.pullback ψ).obj (gluingLocalOver 𝒰 M i)).hom
      ((Over.pullback ψ).obj (gluingChartOver 𝒰 j)).hom :=
  overPullback_product_isPullback ψ (gluingOverlapFirst 𝒰 M i j)
    (gluingOverlapSecond 𝒰 M i j) (IsPullback.of_hasPullback _ _)

/-- The pulled-back local model over its pulled-back chart. -/
def recoveredPullbackLocalModel (i : 𝒰.I₀) : Over ((swappedPullbackCover ψ 𝒰).X i) :=
  Over.mk (((Over.pullback ψ).map (gluingLocalStructure 𝒰 M i)).left)

/-- The canonical iterated-pullback comparison for the local model. -/
def recoveredPullbackLocalModelIso (i : 𝒰.I₀) :
    recoveredPullbackLocalModel ψ 𝒰 M i ≅
      (Over.pullback (pullback.fst (𝒰.f i) ψ)).obj (M i) := by
  refine Over.isoMk (pullbackRightPullbackFstIso (𝒰.f i) ψ (M i).hom).symm ?_
  change (pullbackRightPullbackFstIso (𝒰.f i) ψ (M i).hom).inv ≫
    pullback.snd (M i).hom (pullback.fst (𝒰.f i) ψ) =
      ((Over.pullback ψ).map (gluingLocalStructure 𝒰 M i)).left
  have hf : ((Over.pullback ψ).map (gluingLocalStructure 𝒰 M i)).left ≫
      pullback.fst (𝒰.f i) ψ = pullback.fst ((M i).hom ≫ 𝒰.f i) ψ ≫ (M i).hom :=
    pullback.lift_fst _ _ _
  have hs : ((Over.pullback ψ).map (gluingLocalStructure 𝒰 M i)).left ≫
      pullback.snd (𝒰.f i) ψ = pullback.snd ((M i).hom ≫ 𝒰.f i) ψ :=
    pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((pullbackRightPullbackFstIso_inv_snd_fst (𝒰.f i) ψ (M i).hom).trans hf.symm)
  · exact (Category.assoc _ _ _).trans
      ((pullbackRightPullbackFstIso_inv_snd_snd (𝒰.f i) ψ (M i).hom).trans hs.symm)

variable (Z : Over Y)
variable (e : ∀ i : 𝒰.I₀,
  (Over.pullback (pullback.fst (𝒰.f i) ψ)).obj (M i) ≅
    (Over.pullback (pullback.snd (𝒰.f i) ψ)).obj Z)

/-- The given local recovery transported to the standard pullback chart. -/
def recoveredPullbackLocalIso (i : 𝒰.I₀) :
    recoveredPullbackLocalModel ψ 𝒰 M i ≅
      (Over.pullback ((swappedPullbackCover ψ 𝒰).f i)).obj Z :=
  recoveredPullbackLocalModelIso ψ 𝒰 M i ≪≫ e i

/-- The recovered chart map into the original object after base change. -/
def recoveredPullbackChartMap (i : 𝒰.I₀) :
    ((Over.pullback ψ).obj (gluingLocalOver 𝒰 M i)).left ⟶ Z.left :=
  Scheme.Cover.recoveredLocalModelMap (swappedPullbackCover ψ 𝒰) Z
    (recoveredPullbackLocalModel ψ 𝒰 M) (recoveredPullbackLocalIso ψ 𝒰 M Z e) i

/-- The open cover supplied by the recovered local models. -/
def recoveredPullbackChartCover : Z.left.OpenCover :=
  Scheme.Cover.recoveredLocalModelCover (swappedPullbackCover ψ 𝒰) Z
    (recoveredPullbackLocalModel ψ 𝒰 M) (recoveredPullbackLocalIso ψ 𝒰 M Z e)

theorem recoveredPullbackChartMap_isOpenImmersion (i : 𝒰.I₀) :
    IsOpenImmersion (recoveredPullbackChartMap ψ 𝒰 M Z e i) :=
  (recoveredPullbackChartCover ψ 𝒰 M Z e).map_prop i

theorem recoveredPullbackChartMap_isPullback (i : 𝒰.I₀) :
    IsPullback ((Over.pullback ψ).map (gluingLocalStructure 𝒰 M i)).left
      (recoveredPullbackChartMap ψ 𝒰 M Z e i)
      (((Over.pullback ψ).obj (gluingChartOver 𝒰 i)).hom) Z.hom :=
  Scheme.Cover.recoveredLocalModelMap_isPullback (swappedPullbackCover ψ 𝒰) Z
    (recoveredPullbackLocalModel ψ 𝒰 M) (recoveredPullbackLocalIso ψ 𝒰 M Z e) i

theorem recoveredPullbackChartMap_structure (i : 𝒰.I₀) :
    recoveredPullbackChartMap ψ 𝒰 M Z e i ≫ Z.hom =
      ((Over.pullback ψ).obj (gluingLocalOver 𝒰 M i)).hom :=
  (recoveredPullbackChartMap_isPullback ψ 𝒰 M Z e i).w.symm.trans
    (Over.w ((Over.pullback ψ).map (gluingLocalStructure 𝒰 M i)))

/-- The map from a recovered overlap to its second local model. -/
def recoveredPullbackOverlapTransfer (i j : 𝒰.I₀) :
    ((Over.pullback ψ).obj (gluingOverlapOver 𝒰 M (i, j))).left ⟶
      ((Over.pullback ψ).obj (gluingLocalOver 𝒰 M j)).left :=
  (recoveredPullbackChartMap_isPullback ψ 𝒰 M Z e j).lift
    ((Over.pullback ψ).map (gluingOverlapSecond 𝒰 M i j)).left
    (((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M i j)).left ≫
      recoveredPullbackChartMap ψ 𝒰 M Z e i)
    (by
      rw [Category.assoc, recoveredPullbackChartMap_structure]
      exact (recoveredPullbackOverlap_isPullback ψ 𝒰 M i j).w.symm)

@[reassoc]
theorem recoveredPullbackOverlapTransfer_structure (i j : 𝒰.I₀) :
    recoveredPullbackOverlapTransfer ψ 𝒰 M Z e i j ≫
      ((Over.pullback ψ).map (gluingLocalStructure 𝒰 M j)).left =
        ((Over.pullback ψ).map (gluingOverlapSecond 𝒰 M i j)).left :=
  (recoveredPullbackChartMap_isPullback ψ 𝒰 M Z e j).lift_fst _ _ _

@[reassoc]
theorem recoveredPullbackOverlapTransfer_chartMap (i j : 𝒰.I₀) :
    recoveredPullbackOverlapTransfer ψ 𝒰 M Z e i j ≫ recoveredPullbackChartMap ψ 𝒰 M Z e j =
      ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M i j)).left ≫
        recoveredPullbackChartMap ψ 𝒰 M Z e i :=
  (recoveredPullbackChartMap_isPullback ψ 𝒰 M Z e j).lift_snd _ _ _

/-- The transition map between the two orders of a recovered overlap. -/
def recoveredPullbackTransition (i j : 𝒰.I₀) :
    (Over.pullback ψ).obj (gluingOverlapOver 𝒰 M (i, j)) ⟶
      (Over.pullback ψ).obj (gluingOverlapOver 𝒰 M (j, i)) := by
  let t := (recoveredPullbackOverlap_isPullback ψ 𝒰 M j i).lift
    (recoveredPullbackOverlapTransfer ψ 𝒰 M Z e i j)
    (((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M i j)).left ≫
      ((Over.pullback ψ).map (gluingLocalStructure 𝒰 M i)).left)
    (by
      rw [Category.assoc, Over.w]
      rw [← Over.w ((Over.pullback ψ).map (gluingLocalStructure 𝒰 M j)),
        recoveredPullbackOverlapTransfer_structure_assoc]
      exact (recoveredPullbackOverlap_isPullback ψ 𝒰 M i j).w.symm)
  refine Over.homMk t ?_
  rw [← Over.w ((Over.pullback ψ).map (gluingOverlapSecond 𝒰 M j i)), ← Category.assoc]
  dsimp only [t]
  rw [(recoveredPullbackOverlap_isPullback ψ 𝒰 M j i).lift_snd]
  simp only [Category.assoc, Over.w]

@[reassoc]
theorem recoveredPullbackTransition_first (i j : 𝒰.I₀) :
    (recoveredPullbackTransition ψ 𝒰 M Z e i j).left ≫
      ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M j i)).left =
      recoveredPullbackOverlapTransfer ψ 𝒰 M Z e i j :=
  (recoveredPullbackOverlap_isPullback ψ 𝒰 M j i).lift_fst _ _ _

theorem recoveredPullbackTransition_chartMap (i j : 𝒰.I₀) :
    (recoveredPullbackTransition ψ 𝒰 M Z e i j).left ≫
      ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M j i)).left ≫
        recoveredPullbackChartMap ψ 𝒰 M Z e j =
      ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M i j)).left ≫
        recoveredPullbackChartMap ψ 𝒰 M Z e i := by
  rw [recoveredPullbackTransition_first_assoc, recoveredPullbackOverlapTransfer_chartMap]

end AlgebraicGeometry.Scheme.Cover
