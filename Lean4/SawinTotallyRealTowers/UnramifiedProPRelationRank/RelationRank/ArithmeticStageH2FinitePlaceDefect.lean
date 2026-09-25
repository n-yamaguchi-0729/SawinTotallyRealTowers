/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2CocycleExtensionSplitting
import GaloisCohomology.ProP.QuotientRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2EmbeddingProblem
import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace

set_option autoImplicit false
/-!
# Finite-place splitting defects of arithmetic-stage H² embedding problems

At a finite place, restrict the arithmetic-stage quotient to its chosen
decomposition group.  The restricted degree-two class is the local splitting
defect: it vanishes exactly when the pulled-back central extension has a
continuous section.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.Martinet
open ProCGroups ProCGroups.ProC

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- The chosen finite-place decomposition group of an arithmetic stage. -/
abbrev ArithmeticStageFinitePlaceDecompositionGroup
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :=
  finitePlaceDecompositionGroup
    (K := F) (L := (openNormalArithmeticStage F p hpOdd U).field) v

/-- Inclusion of the chosen decomposition group into the arithmetic-stage
Galois group. -/
def arithmeticStageFinitePlaceDecompositionInclusion
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ArithmeticStageFinitePlaceDecompositionGroup F p hpOdd U v →ₜ*
      ((openNormalArithmeticStage F p hpOdd U).field ≃ₐ[F]
        (openNormalArithmeticStage F p hpOdd U).field) :=
  ClassFieldTower.Cohomology.subgroupInclusion _

/-- The decomposition-group inclusion transported back to the open-normal
quotient of the maximal everywhere-unramified pro-`p` group. -/
noncomputable def arithmeticStageFinitePlaceQuotientInclusion
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ArithmeticStageFinitePlaceDecompositionGroup F p hpOdd U v →ₜ*
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (openNormalQuotientContinuousEquivArithmeticStageGalois
      F p hpOdd U).symm).comp
    (arithmeticStageFinitePlaceDecompositionInclusion F p hpOdd U v)

/-- Restriction of stage `H²` to a chosen finite-place decomposition group. -/
noncomputable def arithmeticStageFinitePlaceH2Localization
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    continuousCohomologyZModPLifted p
        (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
          (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2 →ₗ[ZMod p]
      continuousCohomologyZModPLifted p
        (ArithmeticStageFinitePlaceDecompositionGroup F p hpOdd U v) 2 :=
  (continuousCohomologyZModPMapLifted p
    (arithmeticStageFinitePlaceQuotientInclusion F p hpOdd U v) 2).hom.toLinearMap

/-- The prime-wise splitting defect of a stage class. -/
abbrev ArithmeticStageFinitePlaceH2Defect
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :=
  arithmeticStageFinitePlaceH2Localization F p hpOdd U v xU

@[simp]
theorem arithmeticStageFinitePlaceH2Localization_apply
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :
    arithmeticStageFinitePlaceH2Localization F p hpOdd U v xU =
      continuousCohomologyZModPMapLifted p
        (arithmeticStageFinitePlaceQuotientInclusion F p hpOdd U v) 2 xU :=
  rfl

/-- The chosen stage cocycle restricted to the finite-place decomposition
group.  Its extension is the cocycle pullback of the arithmetic embedding
problem. -/
noncomputable def arithmeticStageFinitePlaceRestrictedCocycle
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    trivialZModPCocyclesLifted p
      (ArithmeticStageFinitePlaceDecompositionGroup F p hpOdd U v) 2 :=
  trivialZModPCocyclesMapLifted p
    (arithmeticStageFinitePlaceQuotientInclusion F p hpOdd U v) 2
      (ClassFieldTower.ProP.degreeTwoCocycleRepresentative xU)

/-- Local splitting means that the pulled-back cocycle extension over the
decomposition group has a continuous section. -/
def ArithmeticStageH2LocallySplitAt
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) : Prop :=
  ∃ s : ArithmeticStageFinitePlaceDecompositionGroup F p hpOdd U v →ₜ*
      ClassFieldTower.ProP.H2CocycleExtension
        (arithmeticStageFinitePlaceRestrictedCocycle F p hpOdd U xU v),
    (ClassFieldTower.ProP.H2CocycleExtension.projection
      (arithmeticStageFinitePlaceRestrictedCocycle F p hpOdd U xU v)).comp s =
        ContinuousMonoidHom.id _

/-- The cohomology class of the restricted stage cocycle is exactly the
finite-place splitting defect. -/
theorem arithmeticStageFinitePlaceRestrictedCocycle_π
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ContinuousCohomology.π
        (trivialZModPLifted p
          (ArithmeticStageFinitePlaceDecompositionGroup F p hpOdd U v)) 2
        (arithmeticStageFinitePlaceRestrictedCocycle F p hpOdd U xU v) =
      ArithmeticStageFinitePlaceH2Defect F p hpOdd U xU v := by
  let f := arithmeticStageFinitePlaceQuotientInclusion F p hpOdd U v
  let z := ClassFieldTower.ProP.degreeTwoCocycleRepresentative xU
  have hnat := ConcreteCategory.congr_hom
    (trivialZModPLifted_π_naturality p f 2) z
  change ContinuousCohomology.π
      (trivialZModPLifted p
        (ArithmeticStageFinitePlaceDecompositionGroup F p hpOdd U v)) 2
      (trivialZModPCocyclesMapLifted p f 2 z) =
    continuousCohomologyZModPMapLifted p f 2 xU
  calc
    _ = continuousCohomologyZModPMapLifted p f 2
        (ContinuousCohomology.π
          (trivialZModPLifted p
            (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
              (U : Subgroup
                (MaxEverywhereUnramifiedProPGaloisGroup F p)))) 2 z) := by
      simpa only [ConcreteCategory.comp_apply] using hnat.symm
    _ = _ := congrArg
      (fun y ↦ continuousCohomologyZModPMapLifted p f 2 y)
      (ClassFieldTower.ProP.degreeTwoCocycleRepresentative_π xU)

/-- The local defect vanishes exactly when the pulled-back central embedding
problem splits over the chosen decomposition group. -/
theorem arithmeticStageH2LocallySplitAt_iff_defect_eq_zero
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ArithmeticStageH2LocallySplitAt F p hpOdd U xU v ↔
      ArithmeticStageFinitePlaceH2Defect F p hpOdd U xU v = 0 := by
  change (∃ s : ArithmeticStageFinitePlaceDecompositionGroup F p hpOdd U v →ₜ*
      ClassFieldTower.ProP.H2CocycleExtension
        (arithmeticStageFinitePlaceRestrictedCocycle F p hpOdd U xU v),
    (ClassFieldTower.ProP.H2CocycleExtension.projection
      (arithmeticStageFinitePlaceRestrictedCocycle F p hpOdd U xU v)).comp s =
        ContinuousMonoidHom.id _) ↔ _
  rw [ClassFieldTower.ProP.H2CocycleExtension.exists_section_iff_π_eq_zero,
    arithmeticStageFinitePlaceRestrictedCocycle_π]

/-- The stage embedding problem is locally split at every finite place
exactly when every prime-wise defect vanishes. -/
theorem arithmeticStageH2LocallySplitAt_allFinitePlaces_iff
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2) :
    (∀ v, ArithmeticStageH2LocallySplitAt F p hpOdd U xU v) ↔
      ∀ v, ArithmeticStageFinitePlaceH2Defect F p hpOdd U xU v = 0 := by
  constructor <;> intro h v
  · exact (arithmeticStageH2LocallySplitAt_iff_defect_eq_zero
      F p hpOdd U xU v).mp (h v)
  · exact (arithmeticStageH2LocallySplitAt_iff_defect_eq_zero
      F p hpOdd U xU v).mpr (h v)

end ClassFieldTower.Martinet.Shafarevich
