/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageAbsoluteH2Vanishing
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2EmbeddingProblem
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteUnramifiedGaloisSequence
import GaloisCohomology.ProP.PresentationQuotientEquiv

set_option autoImplicit false
/-!
# Vanishing of absolute inflation from unramified pro-p degree two

The quotient/arithmetic-stage equivalence is checked on actual field
automorphisms against restriction from the absolute Galois group.  Thus
the proved arithmetic-stage vanishing applies to every finite quotient.
Finite-stage realization of continuous cohomology then gives vanishing
for every degree-two class of the maximal everywhere-unramified pro-p
group over a base containing the supplied primitive root.
No comparison assumption or new instance is introduced.
-/

open scoped Topology NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet ClassFieldTower.ProP ClassFieldTower.Cohomology
open ProCGroups ProCGroups.ProC

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))

include hpOdd

/-- Quotient restriction followed by the arithmetic-stage equivalence is
exactly actual absolute restriction to that field. -/
theorem openNormalArithmeticStageAbsoluteRestriction_factor :
    (ContinuousMonoidHom.toContinuousMonoidHom
      (openNormalQuotientContinuousEquivArithmeticStageGalois F (n : ℕ) hpOdd U)).comp
        ((OpenNormalSubgroup.quotientProj U).comp
          (absoluteToMaxEverywhereUnramifiedProP F (n : ℕ))) =
      openNormalArithmeticStageAbsoluteRestriction F n hpOdd U := by
  apply ContinuousMonoidHom.ext
  intro sigma
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change ((openNormalQuotientEquivArithmeticStageGalois F (n : ℕ) hpOdd U
      (QuotientGroup.mk (absoluteToMaxEverywhereUnramifiedProP F (n : ℕ) sigma))) x).1 =
    (AlgEquiv.restrictNormalHom
      (openNormalArithmeticStage F (n : ℕ) hpOdd U).field
        (absoluteGaloisGroupContinuousMulEquiv F sigma) x).1
  rw [AlgEquiv.restrictNormalHom_apply]
  let L := IntermediateField.fixedField
    (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))
  let _ : Normal F L :=
    (IsGalois.of_fixedField_normal_subgroup
      (U.toOpenSubgroup : Subgroup
        (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))
      (hn := U.isNormal')).to_normal
  change ((IntermediateField.liftAlgEquiv L)
      ((AlgEquiv.restrictNormalHom L
        (absoluteToMaxEverywhereUnramifiedProP F (n : ℕ) sigma))
          ((IntermediateField.liftAlgEquiv L).symm x))).1 =
    (absoluteGaloisGroupContinuousMulEquiv F sigma) x.1
  rw [IntermediateField.liftAlgEquiv_apply]
  let M := maximalEverywhereUnramifiedProP F (n : ℕ)
  have hL := AlgEquiv.restrictNormal_commutes
    (absoluteToMaxEverywhereUnramifiedProP F (n : ℕ) sigma) L
    ((IntermediateField.liftAlgEquiv L).symm x)
  have hM := AlgEquiv.restrictNormal_commutes
    (absoluteGaloisGroupContinuousMulEquiv F sigma) M
    (algebraMap L M ((IntermediateField.liftAlgEquiv L).symm x))
  exact (congrArg (algebraMap M (AlgebraicClosure F)) hL).trans hM

/-- Every finite unramified quotient class becomes zero on the absolute
Galois group. -/
theorem openNormalQuotient_absoluteH2Inflation_eq_zero
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (x : continuousCohomologyZModPLifted (n : ℕ)
      (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ) ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))) 2) :
    (continuousCohomologyZModPMapLifted (n : ℕ)
      (absoluteToMaxEverywhereUnramifiedProP F (n : ℕ)) 2).hom
        ((continuousCohomologyZModPMapLifted (n : ℕ)
          (OpenNormalSubgroup.quotientProj U) 2).hom x) = 0 := by
  let e := openNormalQuotientContinuousEquivArithmeticStageGalois F (n : ℕ) hpOdd U
  let eH := continuousCohomologyZModPLiftedLinearEquiv (p := (n : ℕ)) e 2
  let y := eH.symm x
  have hy : (continuousCohomologyZModPMapLifted (n : ℕ)
      (ContinuousMonoidHom.toContinuousMonoidHom e) 2).hom y = x :=
    eH.apply_symm_apply x
  have h := openNormalArithmeticStage_absoluteH2Map_eq_zero F n hpOdd U hmu y
  rw [← openNormalArithmeticStageAbsoluteRestriction_factor F n hpOdd U,
    continuousCohomologyZModPMapLifted_comp,
    continuousCohomologyZModPMapLifted_comp] at h
  change (continuousCohomologyZModPMapLifted (n : ℕ)
      (absoluteToMaxEverywhereUnramifiedProP F (n : ℕ)) 2).hom
        ((continuousCohomologyZModPMapLifted (n : ℕ)
          (OpenNormalSubgroup.quotientProj U) 2).hom
          ((continuousCohomologyZModPMapLifted (n : ℕ)
            (ContinuousMonoidHom.toContinuousMonoidHom e) 2).hom y)) = 0 at h
  rw [hy] at h
  exact h

omit U in
/-- Absolute inflation kills every continuous unramified pro-p degree-two
class when the base contains a primitive p-th root of unity. -/
theorem absoluteUnramifiedH2Inflation_eq_zero_of_primitiveRoots
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (x : continuousCohomologyZModPLifted (n : ℕ)
      (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)) 2) :
    (continuousCohomologyZModPMapLifted (n : ℕ)
      (absoluteToMaxEverywhereUnramifiedProP F (n : ℕ)) 2).hom x = 0 := by
  obtain ⟨V, xV, hxV⟩ := exists_openNormalSubgroupInClass_inflation_eq_degree_two
    (maxEverywhereUnramifiedProPGaloisGroup_hasPGroupOpenNormalBasis F (n : ℕ) hpOdd) x
  rw [← hxV]
  exact openNormalQuotient_absoluteH2Inflation_eq_zero F n hpOdd V.1 hmu xV

end ClassFieldTower.Martinet.Shafarevich
