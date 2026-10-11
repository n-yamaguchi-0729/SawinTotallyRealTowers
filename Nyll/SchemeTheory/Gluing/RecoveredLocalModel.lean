/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Nyll.SchemeTheory.Gluing.CommonCover

/-!
# Recovering overlaps from cartesian local models
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Cover

variable {S : Scheme.{u}} (𝒰 : S.OpenCover) (Z : Over S)
variable (M : ∀ i : 𝒰.I₀, Over (𝒰.X i))
variable (e : ∀ i : 𝒰.I₀, M i ≅ (Over.pullback (𝒰.f i)).obj Z)

private def recoveredChartIso (i : 𝒰.I₀) :
    (M i).left ≅ Limits.pullback Z.hom (𝒰.f i) :=
  (Over.forget (𝒰.X i)).mapIso (e i)

@[reassoc]
private theorem recoveredChartIso_hom_structure (i : 𝒰.I₀) :
    (recoveredChartIso 𝒰 Z M e i).hom ≫ Limits.pullback.snd Z.hom (𝒰.f i) =
      (M i).hom :=
  (e i).hom.w

@[reassoc]
private theorem recoveredChartIso_inv_structure (i : 𝒰.I₀) :
    (recoveredChartIso 𝒰 Z M e i).inv ≫ (M i).hom =
      Limits.pullback.snd Z.hom (𝒰.f i) :=
  (e i).inv.w

/-- The map from a recovered local model to the original scheme. -/
def recoveredLocalModelMap (i : 𝒰.I₀) : (M i).left ⟶ Z.left :=
  (recoveredChartIso 𝒰 Z M e i).hom ≫ Limits.pullback.fst Z.hom (𝒰.f i)

local instance recoveredLocalModelMap_isOpenImmersion (i : 𝒰.I₀) :
    IsOpenImmersion (recoveredLocalModelMap 𝒰 Z M e i) := by
  dsimp only [recoveredLocalModelMap]
  infer_instance

@[reassoc]
theorem recoveredLocalModelMap_structure (i : 𝒰.I₀) :
    recoveredLocalModelMap 𝒰 Z M e i ≫ Z.hom = (M i).hom ≫ 𝒰.f i := by
  rw [recoveredLocalModelMap, Category.assoc, Limits.pullback.condition,
    recoveredChartIso_hom_structure_assoc]

/-- Each actual recovered chart is cartesian over its base chart. -/
theorem recoveredLocalModelMap_isPullback (i : 𝒰.I₀) :
    IsPullback (M i).hom (recoveredLocalModelMap 𝒰 Z M e i) (𝒰.f i) Z.hom := by
  refine (IsPullback.of_hasPullback Z.hom (𝒰.f i)).flip.of_iso'
    (recoveredChartIso 𝒰 Z M e i) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id]
    exact recoveredChartIso_hom_structure 𝒰 Z M e i
  · exact (Category.comp_id _).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

private abbrev recoveredOverlap (i j : 𝒰.I₀) : Scheme.{u} :=
  Limits.pullback ((M i).hom ≫ 𝒰.f i) (𝒰.f j)

private def recoveredOverlapTransfer (i j : 𝒰.I₀) :
    recoveredOverlap 𝒰 M i j ⟶ (M j).left :=
  Limits.pullback.lift
      (Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫
        recoveredLocalModelMap 𝒰 Z M e i)
      (Limits.pullback.snd ((M i).hom ≫ 𝒰.f i) (𝒰.f j))
      (by rw [Category.assoc, recoveredLocalModelMap_structure, Limits.pullback.condition]) ≫
    (recoveredChartIso 𝒰 Z M e j).inv

@[reassoc]
private theorem recoveredOverlapTransfer_structure (i j : 𝒰.I₀) :
    recoveredOverlapTransfer 𝒰 Z M e i j ≫ (M j).hom =
      Limits.pullback.snd ((M i).hom ≫ 𝒰.f i) (𝒰.f j) := by
  rw [recoveredOverlapTransfer, Category.assoc,
    recoveredChartIso_inv_structure, Limits.pullback.lift_snd]

@[reassoc]
private theorem recoveredOverlapTransfer_chartMap (i j : 𝒰.I₀) :
    recoveredOverlapTransfer 𝒰 Z M e i j ≫ recoveredLocalModelMap 𝒰 Z M e j =
      Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫
        recoveredLocalModelMap 𝒰 Z M e i := by
  simp only [recoveredOverlapTransfer, recoveredLocalModelMap, Category.assoc,
    Iso.inv_hom_id_assoc, Limits.pullback.lift_fst]

private def recoveredOverlapTransition (i j : 𝒰.I₀) :
    recoveredOverlap 𝒰 M i j ⟶ recoveredOverlap 𝒰 M j i :=
  Limits.pullback.lift
    (recoveredOverlapTransfer 𝒰 Z M e i j)
    (Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫ (M i).hom)
    (by
      rw [← Category.assoc, recoveredOverlapTransfer_structure,
        Category.assoc, Limits.pullback.condition])

@[reassoc]
private theorem recoveredOverlapTransition_fst (i j : 𝒰.I₀) :
    recoveredOverlapTransition 𝒰 Z M e i j ≫
      Limits.pullback.fst ((M j).hom ≫ 𝒰.f j) (𝒰.f i) =
        recoveredOverlapTransfer 𝒰 Z M e i j :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
private theorem recoveredOverlapTransition_snd (i j : 𝒰.I₀) :
    recoveredOverlapTransition 𝒰 Z M e i j ≫
      Limits.pullback.snd ((M j).hom ≫ 𝒰.f j) (𝒰.f i) =
        Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫ (M i).hom :=
  Limits.pullback.lift_snd _ _ _

@[reassoc]
private theorem recoveredOverlapTransition_chartMap (i j : 𝒰.I₀) :
    recoveredOverlapTransition 𝒰 Z M e i j ≫
      Limits.pullback.fst ((M j).hom ≫ 𝒰.f j) (𝒰.f i) ≫
        recoveredLocalModelMap 𝒰 Z M e j =
    Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫
      recoveredLocalModelMap 𝒰 Z M e i := by
  rw [recoveredOverlapTransition_fst_assoc, recoveredOverlapTransfer_chartMap]

private theorem recoveredOverlapTransition_id (i : 𝒰.I₀) :
    recoveredOverlapTransition 𝒰 Z M e i i = 𝟙 _ := by
  apply (cancel_mono (Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f i) ≫
    recoveredLocalModelMap 𝒰 Z M e i)).mp
  rw [recoveredOverlapTransition_chartMap, Category.id_comp]

private abbrev recoveredTriple (i j k : 𝒰.I₀) : Scheme.{u} :=
  Limits.pullback
    (Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j))
    (Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f k))

private def recoveredTripleToOverlap (i j k : 𝒰.I₀) :
    recoveredTriple 𝒰 M i j k ⟶ recoveredOverlap 𝒰 M j k :=
  Limits.pullback.lift
    (Limits.pullback.fst _ _ ≫ recoveredOverlapTransfer 𝒰 Z M e i j)
    (Limits.pullback.snd _ _ ≫
      Limits.pullback.snd ((M i).hom ≫ 𝒰.f i) (𝒰.f k))
    (by
      rw [Category.assoc, ← Category.assoc (recoveredOverlapTransfer 𝒰 Z M e i j),
        recoveredOverlapTransfer_structure, ← Limits.pullback.condition,
        ← Category.assoc, Limits.pullback.condition, Category.assoc,
        Limits.pullback.condition, Category.assoc])

private def recoveredTripleTransition (i j k : 𝒰.I₀) :
    recoveredTriple 𝒰 M i j k ⟶ recoveredTriple 𝒰 M j k i :=
  Limits.pullback.lift
    (recoveredTripleToOverlap 𝒰 Z M e i j k)
    (Limits.pullback.fst _ _ ≫ recoveredOverlapTransition 𝒰 Z M e i j)
    (by
      simp only [recoveredTripleToOverlap, Limits.pullback.lift_fst,
        Category.assoc, recoveredOverlapTransition_fst])

@[reassoc]
private theorem recoveredTripleTransition_chartMap (i j k : 𝒰.I₀) :
    recoveredTripleTransition 𝒰 Z M e i j k ≫
      Limits.pullback.fst _ _ ≫
        Limits.pullback.fst ((M j).hom ≫ 𝒰.f j) (𝒰.f k) ≫
          recoveredLocalModelMap 𝒰 Z M e j =
    Limits.pullback.fst _ _ ≫
      Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫
        recoveredLocalModelMap 𝒰 Z M e i := by
  simp only [recoveredTripleTransition, recoveredTripleToOverlap,
    Limits.pullback.lift_fst_assoc, Category.assoc, recoveredOverlapTransfer_chartMap]

private theorem recoveredTripleTransition_cocycle (i j k : 𝒰.I₀) :
    recoveredTripleTransition 𝒰 Z M e i j k ≫
      recoveredTripleTransition 𝒰 Z M e j k i ≫
        recoveredTripleTransition 𝒰 Z M e k i j = 𝟙 _ := by
  apply (cancel_mono
    (Limits.pullback.fst
      (Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j))
      (Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f k)) ≫
        Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫
          recoveredLocalModelMap 𝒰 Z M e i)).mp
  simp only [Category.assoc, recoveredTripleTransition_chartMap, Category.id_comp]

/-- Actual local models recovered from one scheme determine gluing data on
their literal pairwise overlaps, including the diagonal and triple cocycle laws. -/
def recoveredOverlapGlueData : Scheme.GlueData.{u} where
  J := 𝒰.I₀
  U i := (M i).left
  V ij := recoveredOverlap 𝒰 M ij.1 ij.2
  f i j := Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j)
  f_id i := inferInstance
  t i j := recoveredOverlapTransition 𝒰 Z M e i j
  t_id i := recoveredOverlapTransition_id 𝒰 Z M e i
  t' i j k := recoveredTripleTransition 𝒰 Z M e i j k
  t_fac i j k := Limits.pullback.lift_snd _ _ _
  cocycle i j k := recoveredTripleTransition_cocycle 𝒰 Z M e i j k
  f_open i j := inferInstance

/-- The recovered transition preserves the actual structure map to the other
base chart. -/
theorem recoveredOverlapGlueData_transition_structure (i j : 𝒰.I₀) :
    (recoveredOverlapGlueData 𝒰 Z M e).t i j ≫
      (recoveredOverlapGlueData 𝒰 Z M e).f j i ≫ (M j).hom =
        Limits.pullback.snd ((M i).hom ≫ 𝒰.f i) (𝒰.f j) := by
  change recoveredOverlapTransition 𝒰 Z M e i j ≫
    Limits.pullback.fst ((M j).hom ≫ 𝒰.f j) (𝒰.f i) ≫ (M j).hom = _
  rw [recoveredOverlapTransition_fst_assoc, recoveredOverlapTransfer_structure]

/-- The local maps to the original scheme agree on the recovered overlaps. -/
theorem recoveredOverlapGlueData_transition_map (i j : 𝒰.I₀) :
    (recoveredOverlapGlueData 𝒰 Z M e).t i j ≫
      (recoveredOverlapGlueData 𝒰 Z M e).f j i ≫ recoveredLocalModelMap 𝒰 Z M e j =
    (recoveredOverlapGlueData 𝒰 Z M e).f i j ≫ recoveredLocalModelMap 𝒰 Z M e i :=
  recoveredOverlapTransition_chartMap 𝒰 Z M e i j

/-- The recovered transition preserves the structure map to the covered base. -/
theorem recoveredOverlapGlueData_transition_base (i j : 𝒰.I₀) :
    (recoveredOverlapGlueData 𝒰 Z M e).t i j ≫
      (recoveredOverlapGlueData 𝒰 Z M e).f j i ≫ (M j).hom ≫ 𝒰.f j =
    (recoveredOverlapGlueData 𝒰 Z M e).f i j ≫ (M i).hom ≫ 𝒰.f i := by
  change recoveredOverlapTransition 𝒰 Z M e i j ≫
    Limits.pullback.fst ((M j).hom ≫ 𝒰.f j) (𝒰.f i) ≫ (M j).hom ≫ 𝒰.f j =
      Limits.pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫ (M i).hom ≫ 𝒰.f i
  rw [recoveredOverlapTransition_fst_assoc, recoveredOverlapTransfer_structure_assoc,
    ← Limits.pullback.condition]

/-- The recovered overlap is the actual intersection of the two recovered charts. -/
theorem recoveredOverlapGlueData_isPullback (i j : 𝒰.I₀) :
    IsPullback ((recoveredOverlapGlueData 𝒰 Z M e).f i j)
      ((recoveredOverlapGlueData 𝒰 Z M e).t i j ≫
        (recoveredOverlapGlueData 𝒰 Z M e).f j i)
      (recoveredLocalModelMap 𝒰 Z M e i) (recoveredLocalModelMap 𝒰 Z M e j) := by
  exact isPullback_of_cartesian_chart_overlap
    (recoveredLocalModelMap 𝒰 Z M e i) (recoveredLocalModelMap 𝒰 Z M e j) Z.hom
    (M i).hom (M j).hom (𝒰.f i) (𝒰.f j)
    ((recoveredOverlapGlueData 𝒰 Z M e).f i j)
    ((recoveredOverlapGlueData 𝒰 Z M e).t i j ≫ (recoveredOverlapGlueData 𝒰 Z M e).f j i)
    (Limits.pullback.snd ((M i).hom ≫ 𝒰.f i) (𝒰.f j))
    (recoveredLocalModelMap_structure 𝒰 Z M e i).symm
    (recoveredLocalModelMap_isPullback 𝒰 Z M e j)
    (IsPullback.of_hasPullback ((M i).hom ≫ 𝒰.f i) (𝒰.f j))
    ((Category.assoc _ _ _).trans (recoveredOverlapGlueData_transition_structure 𝒰 Z M e i j))
    (recoveredOverlapGlueData_transition_map 𝒰 Z M e i j).symm

/-- The recovered local models form an actual open cover of the original scheme. -/
def recoveredLocalModelCover : Z.left.OpenCover where
  I₀ := 𝒰.I₀
  X i := (M i).left
  f i := recoveredLocalModelMap 𝒰 Z M e i
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun i => inferInstance⟩
    intro z
    obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (Z.hom z)
    obtain ⟨v, hv, -⟩ := Scheme.Pullback.exists_preimage_pullback z x hx.symm
    refine ⟨i, (recoveredChartIso 𝒰 Z M e i).inv v, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    change ((recoveredChartIso 𝒰 Z M e i).inv ≫
      (recoveredChartIso 𝒰 Z M e i).hom ≫ Limits.pullback.fst Z.hom (𝒰.f i)) v = z
    rw [Iso.inv_hom_id_assoc]
    exact hv

end AlgebraicGeometry.Scheme.Cover
