import ProCGroups.Cohomology.FiniteInvariantCharacter
import Mathlib.Topology.Instances.ZMod
import ProCGroups.ProC.Quotients.ClosedSubgroupNeighborhoods

set_option autoImplicit false
/-!
# Finite-stage descent of invariant characters

Every ambient-conjugation-invariant continuous mod-`p` character on a closed normal subgroup of a
pro-`p` group descends to the subgroup's image in one finite `p`-group quotient.  This isolates the
finite-stage input needed to construct transgression without assuming that the closed subgroup is
open.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]

/-- The image of a closed subgroup in an ambient finite quotient. -/
def finiteStageImage (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    Subgroup (F ⧸ (U.1 : Subgroup F)) :=
  R.map (OpenNormalSubgroup.quotientProj U.1).toMonoidHom

instance finiteStageImage_normal (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    (finiteStageImage R U).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective (U.1 : Subgroup F))

/-- The canonical surjection from a closed subgroup to its image at a finite stage. -/
def finiteStageImageMap (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    MonoidHom R (finiteStageImage R U) where
  toFun r :=
    ⟨OpenNormalSubgroup.quotientProj U.1 r.1, ⟨r.1, r.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (OpenNormalSubgroup.quotientProj U.1))
  map_mul' a b := Subtype.ext (map_mul (OpenNormalSubgroup.quotientProj U.1) a.1 b.1)

omit [IsTopologicalGroup F] [CompactSpace F] [T2Space F]
  [TotallyDisconnectedSpace F] in
/-- The finite-stage image map is surjective. -/
theorem finiteStageImageMap_surjective (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    Function.Surjective (finiteStageImageMap R U) := by
  intro y
  obtain ⟨x, hxR, hxy⟩ := y.2
  exact ⟨⟨x, hxR⟩, Subtype.ext hxy⟩

omit [IsTopologicalGroup F] [CompactSpace F] [T2Space F]
  [TotallyDisconnectedSpace F] in
/-- An ambient-conjugation-invariant continuous mod-`p` character of a closed normal subgroup
descends to an invariant character on the subgroup's image in one finite `p`-group quotient. -/
theorem exists_finiteStage_invariant_character
    (hF : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) F)
    (R : ClosedSubgroup F) [R.Normal]
    (χ : R →ₜ* Multiplicative (ZMod p)) (hχne : χ ≠ 1)
    (hχinv : ∀ (f : F) (r : R), χ (MulAut.conjNormal f r) = χ r) :
    ∃ U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F,
      ∃ χbar : MonoidHom (finiteStageImage R U) (Multiplicative (ZMod p)),
        χbar.comp (finiteStageImageMap R U) = χ.toMonoidHom ∧
          χbar ≠ 1 ∧
          ∀ (g : F ⧸ (U.1 : Subgroup F)) (n : finiteStageImage R U),
            χbar (MulAut.conjNormal g n) = χbar n := by
  let kerχ : OpenSubgroup R := (OpenNormalSubgroup.ker χ).toOpenSubgroup
  obtain ⟨U, hUR⟩ :=
    exists_openNormalSubgroupInClass_inter_closedSubgroup_le hF R kerχ
  have hker : (finiteStageImageMap R U).ker ≤ χ.toMonoidHom.ker := by
    intro r hr
    have hrU : r.1 ∈ (U.1 : Subgroup F) := by
      exact (QuotientGroup.eq_one_iff (N := (U.1 : Subgroup F)) (x := r.1)).1
        (congrArg Subtype.val hr)
    exact hUR hrU
  let χbar : MonoidHom (finiteStageImage R U) (Multiplicative (ZMod p)) :=
    (finiteStageImageMap R U).liftOfSurjective
      (finiteStageImageMap_surjective R U) ⟨χ.toMonoidHom, hker⟩
  have hpull : χbar.comp (finiteStageImageMap R U) = χ.toMonoidHom := by
    exact (finiteStageImageMap R U).liftOfRightInverse_comp
      (Function.surjInv (finiteStageImageMap_surjective R U))
      (Function.rightInverse_surjInv (finiteStageImageMap_surjective R U))
      ⟨χ.toMonoidHom, hker⟩
  have hχbarne : χbar ≠ 1 := by
    intro hbar
    apply hχne
    apply ContinuousMonoidHom.ext
    intro r
    have hr := DFunLike.congr_fun hpull r
    rw [hbar] at hr
    exact hr.symm
  refine ⟨U, χbar, hpull, hχbarne, ?_⟩
  intro g n
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (U.1 : Subgroup F) g
  obtain ⟨r, rfl⟩ := finiteStageImageMap_surjective R U n
  have hconj :
      MulAut.conjNormal (OpenNormalSubgroup.quotientProj U.1 f)
          (finiteStageImageMap R U r) =
        finiteStageImageMap R U (MulAut.conjNormal f r) := by
    rfl
  change χbar
      (MulAut.conjNormal (OpenNormalSubgroup.quotientProj U.1 f)
        (finiteStageImageMap R U r)) = χbar (finiteStageImageMap R U r)
  rw [hconj]
  have hpullConj := DFunLike.congr_fun hpull (MulAut.conjNormal f r)
  have hpullR := DFunLike.congr_fun hpull r
  exact hpullConj.trans ((hχinv f r).trans hpullR.symm)

end


end ClassFieldTower.ProP
