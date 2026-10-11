/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayDoubleComplex
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Nyll.SchemeTheory.Cohomology.Cech.Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen
import Nyll.SchemeTheory.Cohomology.Cech.Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
import Nyll.SchemeTheory.Cohomology.Cech.Scheme_OrderedAffineCoverOf_aug_injective

/-!
Exactness of the Leray bicomplex rows for a quasicoherent module presheaf.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_Leray_rows_exact

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace Leray
open _root_.AlgebraicGeometry.OModulePresheaf.Leray
open _root_.AlgebraicGeometry.OModulePresheaf.Leray
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

section Aux

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

theorem res_self' {O : V.Opens} (h : O ≤ O) (x : Γ(V, O)) : (V.presheaf.map (homOfLE h).op).hom x
    = x := by
  rw [show (homOfLE h : O ⟶ O) = 𝟙 O from rfl, op_id, V.presheaf.map_id]; rfl

theorem unit_d_apply' (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover) (i : ℕ)
    (f : (OModulePresheaf.unit π).cochain K i) (s : K.Idx (i + 1)) :
    ((OModulePresheaf.unit π).d K i f s : Γ(V, K.inter s))
      = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (V.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom (f (K.face s j)) := by
  rw [← Scheme.OrderedAffineCover.d_toCoverOf]
  exact Scheme.OrderedAffineCoverOf.d_apply π K.toCoverOf i f s

end Aux

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

theorem pullOpen_d_apply' (W : V'.Opens) (a : ℕ) (f : (pullOpen p πZ W).cochain K a) (σ : K.Idx (a
    + 1)) :
    ((pullOpen p πZ W).d K a f σ : Γ(V', W ⊓ (Opens.map p.base).obj (K.inter σ)))
      = ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (V'.presheaf.map (homOfLE (inf_le_inf_left W
            ((Opens.map p.base).monotone (K.inter_le_inter_face σ j)))).op).hom (f (K.face σ j))
              := by
  let := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  simp only [OModulePresheaf.d, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

section Rows

variable [IsSeparated πZ] [IsSeparated (p ≫ πZ)]

/-- Identify a row of the Leray bicomplex with the cochains of its induced affine cover. -/
def rowC_equiv {b : ℕ} (τ : K'.Idx b) (a : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (pullOpen p πZ (K'.inter τ)).cochain K a ≃ₗ[R] (rowCoverOf p πZ K K' τ).cochain a :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  { toFun := fun f σ => (V'.presheaf.map (homOfLE (inter_rowCoverOf p πZ K K' τ σ).le).op).hom (f σ)
    invFun := fun g σ => (V'.presheaf.map (homOfLE (inter_rowCoverOf p πZ K K' τ σ).ge).op).hom (g
      σ)
    left_inv := fun f => funext fun σ => by
      change (V'.presheaf.map _).hom ((V'.presheaf.map _).hom (f σ)) = f σ
      erw [Scheme.TwoAffineOpenCover.res_res]; exact res_self' _ _
    right_inv := fun g => funext fun σ => by
      change (V'.presheaf.map _).hom ((V'.presheaf.map _).hom (g σ)) = g σ
      erw [Scheme.TwoAffineOpenCover.res_res]; exact res_self' _ _
    map_add' := fun _ _ => funext fun σ => map_add _ _ _
    map_smul' := fun r f => funext fun σ =>
      (Scheme.OrderedAffineCoverOf.res (p ≫ πZ) (inter_rowCoverOf p πZ K K' τ σ).le).map_smul r (f
        σ) }

theorem rowC_equiv_apply {b : ℕ} (τ : K'.Idx b) (a : ℕ) (f) (σ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    rowC_equiv p πZ K K' τ a f σ = (V'.presheaf.map (homOfLE (inter_rowCoverOf p πZ K K' τ
      σ).le).op).hom (f σ) :=
  rfl

theorem rowC_comm {b : ℕ} (τ : K'.Idx b) (a : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    ∀ f, rowC_equiv p πZ K K' τ (a + 1) ((pullOpen p πZ (K'.inter τ)).d K a f)
      = (rowCoverOf p πZ K K' τ).d (p ≫ πZ) a (rowC_equiv p πZ K K' τ a f) := by
  let := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  intro f; funext σ
  erw [rowC_equiv_apply, pullOpen_d_apply', Scheme.OrderedAffineCoverOf.d_apply]
  refine (map_sum ((V'.presheaf.map _).hom) _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  change (V'.presheaf.map _).hom (((-1 : ℤ) ^ (j : ℕ)) • (V'.presheaf.map _).hom (f (K.face σ j)))
    = ((-1 : ℤ) ^ (j : ℕ)) • (V'.presheaf.map _).hom ((V'.presheaf.map _).hom (f (K.face σ j)))
  erw [map_zsmul, Scheme.TwoAffineOpenCover.res_res]
  exact (congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) (Scheme.TwoAffineOpenCover.res_res _ _ _)).symm

theorem ker_dH_succ_le_range_dH (a b : ℕ) :
    LinearMap.ker ((LerayDblCpx p πZ K K').dH (a + 1) b) ≤ LinearMap.range ((LerayDblCpx p πZ K
      K').dH a b) := by
  let := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  intro c hc
  have hcτ : ∀ τ, rowC_equiv p πZ K K' τ (a + 1) (biC_uncurry' p πZ K K' (a + 1) b c τ)
      ∈ LinearMap.range ((rowCoverOf p πZ K K' τ).d (p ≫ πZ) a) := fun τ =>
    Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen (p ≫ πZ) _
      (Scheme.OrderedAffineCover.isAffineOpen_inter (p ≫ πZ) K' τ) a
      (LinearMap.mem_ker.mpr <|
        (rowC_comm p πZ K K' τ (a + 1) _).symm.trans <|
          (congrArg _ ((dH_uncurry p πZ K K' (a + 1) b c τ).symm.trans
            ((congrFun (congrArg _ (LinearMap.mem_ker.mp hc)) τ).trans
              (congrFun (map_zero _) τ)))).trans (map_zero _))
  choose g hg using hcτ
  refine ⟨(biC_uncurry' p πZ K K' a b).symm fun τ => (rowC_equiv p πZ K K' τ a).symm (g τ),
    (biC_uncurry' p πZ K K' (a + 1) b).injective (funext fun τ =>
      (dH_uncurry p πZ K K' a b _ τ).trans ((rowC_equiv p πZ K K' τ (a + 1)).injective ?_))⟩
  have hsimp : biC_uncurry' p πZ K K' a b
      ((biC_uncurry' p πZ K K' a b).symm fun τ' => (rowC_equiv p πZ K K' τ' a).symm (g τ')) τ
      = (rowC_equiv p πZ K K' τ a).symm (g τ) :=
    congrFun ((biC_uncurry' p πZ K K' a b).apply_symm_apply _) τ
  rw [rowC_comm, hsimp, LinearEquiv.apply_symm_apply]
  exact hg τ

theorem ker_dH_zero_eq_range_biAug (b : ℕ) :
    LinearMap.ker ((LerayDblCpx p πZ K K').dH 0 b) = LinearMap.range (biAug p πZ K K' b) := by
  let := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  have hbridge : ∀ (τ : K'.Idx b) (y : Γ(V', K'.inter τ)),
      rowC_equiv p πZ K K' τ 0 (fun σ =>
          (V'.presheaf.map (homOfLE (inf_le_left : biOpen p K K' 0 b σ τ ≤ K'.inter τ)).op).hom y)
        = (rowCoverOf p πZ K K' τ).aug (p ≫ πZ) y :=
    fun τ y => funext fun σ => by
      change (V'.presheaf.map _).hom ((V'.presheaf.map _).hom y) = (V'.presheaf.map _).hom y
      rw [Scheme.TwoAffineOpenCover.res_res]
  refine le_antisymm (fun c hc => ?_) (fun _ ⟨y, hy⟩ => hy ▸ LinearMap.mem_ker.mpr ?_)
  · choose y hy using fun τ => ((Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug (p ≫ πZ)
        (rowCoverOf p πZ K K' τ)).le
      (LinearMap.mem_ker.mpr <|
        (rowC_comm p πZ K K' τ 0 _).symm.trans <|
          (congrArg _ ((dH_uncurry p πZ K K' 0 b c τ).symm.trans
            ((congrFun (congrArg _ (LinearMap.mem_ker.mp hc)) τ).trans
              (congrFun (map_zero _) τ)))).trans (map_zero _)))
    refine ⟨y, funext fun ⟨σ, τ⟩ => ?_⟩
    have hkey := congrArg (V'.presheaf.map (homOfLE (inter_rowCoverOf p πZ K K' τ σ).ge).op).hom
      (congrFun (hy τ) σ)
    erw [Scheme.OrderedAffineCoverOf.aug_apply, rowC_equiv_apply, Scheme.TwoAffineOpenCover.res_res,
      Scheme.TwoAffineOpenCover.res_res] at hkey
    exact hkey.trans (res_self' _ _)
  · refine (biC_uncurry' p πZ K K' 1 b).injective (funext fun τ => ?_)
    refine (dH_uncurry p πZ K K' 0 b _ τ).trans
      (((rowC_equiv p πZ K K' τ 1).injective ?_).trans (congrFun (map_zero (biC_uncurry' p πZ K K'
        1 b)) τ).symm)
    refine (rowC_comm p πZ K K' τ 0 _).trans
      ((congrArg _ (hbridge τ (y τ))).trans ((LinearMap.mem_ker.mp
        ((Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug (p ≫ πZ) _).ge ⟨y τ, rfl⟩)).trans
        (map_zero (rowC_equiv p πZ K K' τ 1)).symm))

theorem biAug_injective (b : ℕ) : Function.Injective (biAug p πZ K K' b) := by
  let := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  intro y₁ y₂ hy
  refine funext fun τ => Scheme.OrderedAffineCoverOf.aug_injective (p ≫ πZ) (rowCoverOf p πZ K K'
    τ) (funext fun σ => ?_)
  have key := congrArg (V'.presheaf.map (homOfLE (inter_rowCoverOf p πZ K K' τ σ).le).op).hom
    (congrFun hy (σ, τ))
  erw [biAug_apply, biAug_apply, Scheme.TwoAffineOpenCover.res_res,
    Scheme.TwoAffineOpenCover.res_res] at key
  exact key

end Rows

end AlgebraicGeometry.OModulePresheaf.Leray

end

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open _root_.AlgebraicGeometry.OModulePresheaf.Leray
  OModulePresheaf_Leray_rows_exact.AlgebraicGeometry.OModulePresheaf.Leray in
theorem _root_.AlgebraicGeometry.OModulePresheaf.Leray.rows_exact
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    [IsSeparated πZ] [IsSeparated (p ≫ πZ)] (K : Z.OrderedAffineCover) (K' :
      V'.OrderedAffineCover) :
    (∀ a b : ℕ, LinearMap.ker ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH (a + 1) b)
        ≤ LinearMap.range ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH a b)) ∧
      (∀ b : ℕ, LinearMap.ker ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH 0 b)
        = LinearMap.range (OModulePresheaf.Leray.biAug p πZ K K' b)) ∧
      ∀ b : ℕ, Function.Injective (OModulePresheaf.Leray.biAug p πZ K K' b) :=
  ⟨ker_dH_succ_le_range_dH p πZ K K', ker_dH_zero_eq_range_biAug p πZ K K', biAug_injective p πZ K
    K'⟩
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_Leray_rows_exact
end ProofImplementation
