/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.CyclotomicArithmeticStageRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteIntermediateAbsoluteClosure
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.FiniteUnramifiedAbsoluteH2Vanishing
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.FiniteExtensionAbsoluteH2Restriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteUnramifiedH2Vanishing

set_option autoImplicit false
/-!
# Absolute inflation vanishes over every number field

The actual cyclotomic base change of an unramified arithmetic stage is
mapped into the standard cyclotomic algebraic closure using exactly the
equivalence underlying finite-extension absolute restriction. Evaluation
on field elements proves the restriction square. The mapped stage has
zero absolute H², and prime-to-p cyclotomic restriction is injective.

Thus no primitive-root hypothesis remains. Finite-stage realization then
shows that every continuous degree-two class of the maximal everywhere-
unramified pro-p group vanishes on the absolute Galois group, for odd p.
Only two local proposition-valued instances name the finite cyclotomic
base and its number-field certificate; no comparison assumption is used.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet ClassFieldTower.ProP ClassFieldTower.Cohomology
open ProCGroups ProCGroups.ProC

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))

local notation "Cyclo" => IdealRadicalCyclotomicBase F (n : ℕ) (Fact.out : Nat.Prime (n : ℕ))
local notation "OriginalStage" => FiniteEverywhereUnramifiedProPExtension.field
  (openNormalArithmeticStage F (n : ℕ) hpOdd U)

local instance cyclotomicVanishingBaseFinite : FiniteDimensional F Cyclo :=
  finiteDimensional_idealRadicalCyclotomicBase F (n : ℕ) Fact.out

local instance cyclotomicVanishingBaseNumber : NumberField Cyclo :=
  NumberField.of_module_finite F Cyclo

local notation "closureEquiv" => finiteIntermediateAbsoluteClosureEquiv F Cyclo
local notation "MappedStage" => cyclotomicArithmeticStageMappedExtension F (n : ℕ) hpOdd U closureEquiv

/-- Actual finite restriction from the synchronized cyclotomic stage,
viewed as a continuous homomorphism between finite Galois groups. -/
def cyclotomicArithmeticStageRestrictionContinuous :
    Gal((MappedStage).field/Cyclo) →ₜ* Gal(OriginalStage/F) where
  toMonoidHom := cyclotomicArithmeticStageMappedRestriction F (n : ℕ) hpOdd U closureEquiv
  continuous_toFun := continuous_of_discreteTopology

/-- The finite restriction square commutes with the actual absolute
Galois inclusion, using the same closure equivalence on both sides. -/
theorem cyclotomicArithmeticStageAbsoluteRestriction_factor :
    (cyclotomicArithmeticStageRestrictionContinuous F n hpOdd U).comp
      (finiteUnramifiedExtensionAbsoluteRestriction Cyclo n MappedStage) =
    (openNormalArithmeticStageAbsoluteRestriction F n hpOdd U).comp
      (cyclotomicAbsoluteGaloisInclusion F (n : ℕ)) := by
  apply ContinuousMonoidHom.ext
  intro sigma
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  apply (closureEquiv).symm.injective
  change (closureEquiv).symm
    ((cyclotomicArithmeticStageMappedRestriction F (n : ℕ) hpOdd U closureEquiv
      (finiteUnramifiedExtensionAbsoluteRestriction Cyclo n MappedStage sigma) x).1) =
    (closureEquiv).symm
      ((AlgEquiv.restrictNormalHom OriginalStage
        (absoluteGaloisGroupContinuousMulEquiv F
          (cyclotomicAbsoluteGaloisInclusion F (n : ℕ) sigma)) x).1)
  refine (cyclotomicArithmeticStageMappedRestriction_apply F (n : ℕ) hpOdd U closureEquiv
    (show Gal(cyclotomicArithmeticStageMappedField F (n : ℕ) hpOdd U closureEquiv/Cyclo) from
      finiteUnramifiedExtensionAbsoluteRestriction Cyclo n MappedStage sigma) x).trans ?_
  refine (AlgEquiv.restrictNormalHom_apply (MappedStage).field
    (absoluteGaloisGroupContinuousMulEquiv Cyclo sigma)
    (show (MappedStage).field from
      cyclotomicArithmeticStageMappedOriginalAlgHom F (n : ℕ) hpOdd U closureEquiv x)).trans ?_
  refine (congrArg (absoluteGaloisGroupContinuousMulEquiv Cyclo sigma)
    (cyclotomicArithmeticStageMappedOriginalAlgHom_apply F (n : ℕ) hpOdd U closureEquiv x)).trans ?_
  symm
  refine (congrArg (closureEquiv).symm
    (AlgEquiv.restrictNormalHom_apply OriginalStage
      (absoluteGaloisGroupContinuousMulEquiv F
        (cyclotomicAbsoluteGaloisInclusion F (n : ℕ) sigma)) x)).trans ?_
  exact (congrArg (closureEquiv).symm
    (finiteIntermediateAbsoluteGaloisInclusion_apply F Cyclo sigma x.1)).trans
      (AlgEquiv.symm_apply_apply closureEquiv
        ((absoluteGaloisGroupContinuousMulEquiv Cyclo sigma) ((closureEquiv).symm x.1)))

/-- Every finite unramified arithmetic-stage H² class vanishes on the
absolute Galois group, without assuming that the base contains mu_p. -/
theorem openNormalArithmeticStage_absoluteH2Map_eq_zero_of_odd
    (x : continuousCohomologyZModPLifted (n : ℕ) Gal(OriginalStage/F) 2) :
    (continuousCohomologyZModPMapLifted (n : ℕ)
      (openNormalArithmeticStageAbsoluteRestriction F n hpOdd U) 2).hom x = 0 := by
  apply cyclotomicFieldAbsoluteH2Restriction_injective F (n : ℕ)
  rw [map_zero]
  have h := finiteUnramifiedExtension_absoluteH2Map_eq_zero Cyclo n MappedStage
    (idealRadicalCyclotomicBase_primitiveRoots_nonempty F (n : ℕ) Fact.out)
    ((continuousCohomologyZModPMapLifted (n : ℕ)
      (cyclotomicArithmeticStageRestrictionContinuous F n hpOdd U) 2).hom x)
  have hf := congrArg (fun f => (continuousCohomologyZModPMapLifted (n : ℕ) f 2).hom x)
    (cyclotomicArithmeticStageAbsoluteRestriction_factor F n hpOdd U)
  rw [continuousCohomologyZModPMapLifted_comp,
    continuousCohomologyZModPMapLifted_comp] at hf
  exact hf.symm.trans h

include hpOdd

/-- Absolute inflation kills a finite open-normal quotient H² class for
every number field and odd p. -/
theorem openNormalQuotient_absoluteH2Inflation_eq_zero_of_odd
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
  have h := openNormalArithmeticStage_absoluteH2Map_eq_zero_of_odd F n hpOdd U y
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
/-- Every unramified pro-p degree-two class has zero absolute inflation
over every number field, for odd p. -/
theorem absoluteUnramifiedH2Inflation_eq_zero
    (x : continuousCohomologyZModPLifted (n : ℕ)
      (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)) 2) :
    (continuousCohomologyZModPMapLifted (n : ℕ)
      (absoluteToMaxEverywhereUnramifiedProP F (n : ℕ)) 2).hom x = 0 := by
  obtain ⟨V, xV, hxV⟩ := exists_openNormalSubgroupInClass_inflation_eq_degree_two
    (maxEverywhereUnramifiedProPGaloisGroup_hasPGroupOpenNormalBasis F (n : ℕ) hpOdd) x
  rw [← hxV]
  exact openNormalQuotient_absoluteH2Inflation_eq_zero_of_odd F n hpOdd V.1 xV

end ClassFieldTower.Martinet.Shafarevich
