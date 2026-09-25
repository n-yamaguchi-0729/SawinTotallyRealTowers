/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.Cohomology.InvariantCharacterFiniteStage

set_option autoImplicit false
/-!
# Common finite-stage descent for finite families of invariant characters

A finite family of ambient-conjugation-invariant continuous mod-`p` characters on a closed normal
subgroup descends to one common finite `p`-group quotient.  The construction preserves all
pointwise `ZMod p`-linear relations, which is the finite-stage input needed for dimension arguments.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC

noncomputable section

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]

omit [IsTopologicalGroup F] [CompactSpace F] [T2Space F]
  [TotallyDisconnectedSpace F] in
/-- A finite family of invariant continuous characters descends to one common finite stage.

Each descended character pulls back to the original one and remains invariant under conjugation.
Moreover, a pointwise `ZMod p`-linear combination of the descended family vanishes identically if
and only if the corresponding combination of the original family vanishes identically. -/
theorem exists_finiteStage_invariant_character_family
    {ι : Type v} [Fintype ι]
    (hF : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) F)
    (R : ClosedSubgroup F) [R.Normal]
    (χ : ι → R →ₜ* Multiplicative (ZMod p))
    (hχinv : ∀ (i : ι) (f : F) (r : R),
      χ i (MulAut.conjNormal f r) = χ i r) :
    ∃ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F,
      ∃ χbar : ι → MonoidHom (finiteStageImage R U) (Multiplicative (ZMod p)),
        (∀ i, (χbar i).comp (finiteStageImageMap R U) = (χ i).toMonoidHom) ∧
          (∀ (i : ι) (g : F ⧸ (U.1 : Subgroup F)) (n : finiteStageImage R U),
            χbar i (MulAut.conjNormal g n) = χbar i n) ∧
          ∀ a : ι → ZMod p,
            (∀ n : finiteStageImage R U,
                ∑ i, a i * (χbar i n).toAdd = 0) ↔
              ∀ r : R, ∑ i, a i * (χ i r).toAdd = 0 := by
  classical
  let kerχ : ι → OpenSubgroup R := fun i ↦
    (OpenNormalSubgroup.ker (χ i)).toOpenSubgroup
  let commonKer : OpenSubgroup R := Finset.univ.inf kerχ
  obtain ⟨U, hUR⟩ :=
    exists_openNormalSubgroupInClass_inter_closedSubgroup_le hF R commonKer
  have hker (i : ι) :
      (finiteStageImageMap R U).ker ≤ (χ i).toMonoidHom.ker := by
    intro r hr
    have hrU : r.1 ∈ (U.1 : Subgroup F) := by
      exact (QuotientGroup.eq_one_iff (N := (U.1 : Subgroup F)) (x := r.1)).1
        (congrArg Subtype.val hr)
    have hrCommon : r ∈ commonKer := hUR hrU
    have hri : r ∈ kerχ i :=
      (Finset.inf_le (f := kerχ) (Finset.mem_univ i)) hrCommon
    exact hri
  let χbar : ι → MonoidHom (finiteStageImage R U) (Multiplicative (ZMod p)) :=
    fun i ↦ (finiteStageImageMap R U).liftOfSurjective
      (finiteStageImageMap_surjective R U) ⟨(χ i).toMonoidHom, hker i⟩
  have hpull (i : ι) :
      (χbar i).comp (finiteStageImageMap R U) = (χ i).toMonoidHom := by
    exact (finiteStageImageMap R U).liftOfRightInverse_comp
      (Function.surjInv (finiteStageImageMap_surjective R U))
      (Function.rightInverse_surjInv (finiteStageImageMap_surjective R U))
      ⟨(χ i).toMonoidHom, hker i⟩
  refine ⟨U, χbar, hpull, ?_, ?_⟩
  · intro i g n
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (U.1 : Subgroup F) g
    obtain ⟨r, rfl⟩ := finiteStageImageMap_surjective R U n
    have hconj :
        MulAut.conjNormal (OpenNormalSubgroup.quotientProj U.1 f)
            (finiteStageImageMap R U r) =
          finiteStageImageMap R U (MulAut.conjNormal f r) := by
      rfl
    change χbar i
        (MulAut.conjNormal (OpenNormalSubgroup.quotientProj U.1 f)
          (finiteStageImageMap R U r)) = χbar i (finiteStageImageMap R U r)
    rw [hconj]
    have hpullConj := DFunLike.congr_fun (hpull i) (MulAut.conjNormal f r)
    have hpullR := DFunLike.congr_fun (hpull i) r
    exact hpullConj.trans ((hχinv i f r).trans hpullR.symm)
  · intro a
    constructor
    · intro hstage r
      calc
        ∑ i, a i * (χ i r).toAdd =
            ∑ i, a i * (χbar i (finiteStageImageMap R U r)).toAdd := by
              apply Finset.sum_congr rfl
              intro i hi
              have hir := DFunLike.congr_fun (hpull i) r
              change χbar i (finiteStageImageMap R U r) = χ i r at hir
              rw [hir]
        _ = 0 := hstage (finiteStageImageMap R U r)
    · intro hsource n
      obtain ⟨r, rfl⟩ := finiteStageImageMap_surjective R U n
      calc
        ∑ i, a i * (χbar i (finiteStageImageMap R U r)).toAdd =
            ∑ i, a i * (χ i r).toAdd := by
              apply Finset.sum_congr rfl
              intro i hi
              have hir := DFunLike.congr_fun (hpull i) r
              change χbar i (finiteStageImageMap R U r) = χ i r at hir
              rw [hir]
        _ = 0 := hsource r

end

end ClassFieldTower.ProP
