/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayDoubleComplex
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
The vertical differential vanishes on the bicomplex augmentation.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_Leray_dV_comp_biAug

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

theorem dV_comp_biAug' (b : ℕ) :
    (LerayDblCpx p πZ K K').dV 0 b ∘ₗ biAug p πZ K K' b
      = biAug p πZ K K' (b + 1) ∘ₗ (OModulePresheaf.unit (p ≫ πZ)).d K' b := by
  let := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine LinearMap.ext fun y => funext fun στ => ?_
  change dV p πZ K K' 0 b (biAug p πZ K K' b y) στ
    = (V'.presheaf.map (homOfLE (inf_le_left : biOpen p K K' 0 (b + 1) στ.1 στ.2 ≤ K'.inter
      στ.2)).op).hom
        ((OModulePresheaf.unit (p ≫ πZ)).d K' b y στ.2)
  rw [dV_apply', unit_d_apply', map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  erw [biAug_apply, map_zsmul, Scheme.TwoAffineOpenCover.res_res, Scheme.TwoAffineOpenCover.res_res]

end AlgebraicGeometry.OModulePresheaf.Leray

end

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open _root_.AlgebraicGeometry.OModulePresheaf.Leray
  OModulePresheaf_Leray_dV_comp_biAug.AlgebraicGeometry.OModulePresheaf.Leray in
theorem _root_.AlgebraicGeometry.OModulePresheaf.Leray.dV_comp_biAug
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) (b : ℕ) :
    (OModulePresheaf.Leray.LerayDblCpx p πZ K K').dV 0 b ∘ₗ OModulePresheaf.Leray.biAug p πZ K K' b
      = OModulePresheaf.Leray.biAug p πZ K K' (b + 1) ∘ₗ (OModulePresheaf.unit (p ≫ πZ)).d K' b :=
  dV_comp_biAug' p πZ K K' b
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_Leray_dV_comp_biAug
end ProofImplementation
