/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2CocycleExtensionPullback
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2EmbeddingProblem
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.FinitePlaceUnramifiedH2LocalizationVanishing

set_option autoImplicit false
/-!
# Unramified local solutions of arithmetic-stage central embedding problems

The absolute decomposition group modulo inertia is procyclic and has zero
continuous `H²`.  Pulling a finite arithmetic-stage cocycle extension back to
this quotient therefore supplies a continuous lift to the original extension.
Composing with the inertia quotient gives a local solution that kills inertia.

No splitting of the extension over the finite decomposition group is required.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.Martinet
open ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- The local unramified quotient mapped to the finite stage quotient. -/
noncomputable def arithmeticStageFinitePlaceUnramifiedQuotientMap
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteDecompositionGroup F v ⧸
        finitePlaceAbsoluteInertiaSubgroup F v →ₜ*
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) :=
  (quotientProjection
    (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))).comp
      (finitePlaceUnramifiedToMaxEverywhereUnramifiedProP F p v)

/-- Absolute finite-place restriction followed by the finite stage quotient. -/
noncomputable def arithmeticStageFinitePlaceAbsoluteQuotientMap
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteDecompositionGroup F v →ₜ*
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) :=
  (quotientProjection
    (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))).comp
      ((absoluteToMaxEverywhereUnramifiedProP F p).comp
        (finitePlaceAbsoluteDecompositionInclusion F v))

/-- The stage map from the absolute decomposition group factors through inertia. -/
theorem arithmeticStageFinitePlaceUnramifiedQuotientMap_comp
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (arithmeticStageFinitePlaceUnramifiedQuotientMap F p U v).comp
        (quotientProjection (finitePlaceAbsoluteInertiaSubgroup F v)) =
      arithmeticStageFinitePlaceAbsoluteQuotientMap F p U v := by
  ext sigma
  rfl

/-- Vanishing of local unramified `H²` gives a lift of the unramified
quotient to every finite stage cocycle extension. -/
theorem arithmeticStageH2_exists_unramifiedLocalLift
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ∃ s : (finitePlaceAbsoluteDecompositionGroup F v ⧸
        finitePlaceAbsoluteInertiaSubgroup F v) →ₜ*
          ClassFieldTower.ProP.DegreeTwoCentralExtension xU,
      (ClassFieldTower.ProP.H2CocycleExtension.projection
        (ClassFieldTower.ProP.degreeTwoCocycleRepresentative xU)).comp s =
          arithmeticStageFinitePlaceUnramifiedQuotientMap F p U v := by
  let : CompactSpace (finitePlaceAbsoluteDecompositionGroup F v) :=
    isCompact_iff_compactSpace.mp
      (HilbertRamification.absoluteValueDecompositionGroup_isClosed
        F (finitePlaceAbsoluteValueExtension F v).1).isCompact
  apply ClassFieldTower.ProP.H2CocycleExtension.exists_lift_of_restriction_eq_zero
    (arithmeticStageFinitePlaceUnramifiedQuotientMap F p U v)
    (ClassFieldTower.ProP.degreeTwoCocycleRepresentative xU)
  exact @Subsingleton.elim
    (continuousCohomologyZModPLifted p
      (finitePlaceAbsoluteDecompositionGroup F v ⧸
        finitePlaceAbsoluteInertiaSubgroup F v) 2)
    (finitePlaceUnramifiedQuotientH2_subsingleton F p v) _ _

/-- A choice of the unramified local lift supplied by local `H² = 0`. -/
noncomputable def arithmeticStageH2UnramifiedLocalLift
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (finitePlaceAbsoluteDecompositionGroup F v ⧸
      finitePlaceAbsoluteInertiaSubgroup F v) →ₜ*
        ClassFieldTower.ProP.DegreeTwoCentralExtension xU :=
  Classical.choose (arithmeticStageH2_exists_unramifiedLocalLift F p U xU v)

/-- The chosen lift solves the embedding problem on the unramified quotient. -/
theorem arithmeticStageH2UnramifiedLocalLift_projection
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (ClassFieldTower.ProP.H2CocycleExtension.projection
        (ClassFieldTower.ProP.degreeTwoCocycleRepresentative xU)).comp
        (arithmeticStageH2UnramifiedLocalLift F p U xU v) =
      arithmeticStageFinitePlaceUnramifiedQuotientMap F p U v :=
  Classical.choose_spec (arithmeticStageH2_exists_unramifiedLocalLift F p U xU v)

/-- The resulting local solution on the absolute decomposition group. -/
noncomputable def arithmeticStageH2AbsoluteLocalLift
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteDecompositionGroup F v →ₜ*
      ClassFieldTower.ProP.DegreeTwoCentralExtension xU :=
  (arithmeticStageH2UnramifiedLocalLift F p U xU v).comp
    (quotientProjection (finitePlaceAbsoluteInertiaSubgroup F v))

/-- The local solution projects to the prescribed finite stage map. -/
theorem arithmeticStageH2AbsoluteLocalLift_projection
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (ClassFieldTower.ProP.H2CocycleExtension.projection
        (ClassFieldTower.ProP.degreeTwoCocycleRepresentative xU)).comp
        (arithmeticStageH2AbsoluteLocalLift F p U xU v) =
      arithmeticStageFinitePlaceAbsoluteQuotientMap F p U v := by
  ext sigma
  exact DFunLike.congr_fun
    (arithmeticStageH2UnramifiedLocalLift_projection F p U xU v)
    (quotientProjection (finitePlaceAbsoluteInertiaSubgroup F v) sigma)

/-- Every absolute inertia element is killed by the constructed local solution. -/
theorem arithmeticStageH2AbsoluteLocalLift_inertia
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteInertiaSubgroup F v) :
    arithmeticStageH2AbsoluteLocalLift F p U xU v sigma.1 = 1 := by
  change arithmeticStageH2UnramifiedLocalLift F p U xU v
    (quotientProjection (finitePlaceAbsoluteInertiaSubgroup F v) sigma.1) = 1
  have hq : quotientProjection (finitePlaceAbsoluteInertiaSubgroup F v) sigma.1 = 1 :=
    (QuotientGroup.eq_one_iff (N := finitePlaceAbsoluteInertiaSubgroup F v)
      sigma.1).mpr sigma.2
  rw [hq, map_one]

/-- The local solution is unramified: its kernel contains absolute inertia. -/
theorem arithmeticStageH2AbsoluteLocalLift_inertia_le_ker
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteInertiaSubgroup F v ≤
      (arithmeticStageH2AbsoluteLocalLift F p U xU v).toMonoidHom.ker := by
  intro sigma hsigma
  exact arithmeticStageH2AbsoluteLocalLift_inertia F p U xU v ⟨sigma, hsigma⟩

/-- The absolute finite-place stage map in arithmetic Galois coordinates. -/
noncomputable def arithmeticStageFinitePlaceAbsoluteRestriction
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteDecompositionGroup F v →ₜ*
      ((openNormalArithmeticStage F p hpOdd U).field ≃ₐ[F]
        (openNormalArithmeticStage F p hpOdd U).field) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (openNormalQuotientContinuousEquivArithmeticStageGalois F p hpOdd U)).comp
      (arithmeticStageFinitePlaceAbsoluteQuotientMap F p U v)

/-- The local solution also commutes with the arithmetic-stage projection. -/
theorem arithmeticStageH2AbsoluteLocalLift_arithmeticProjection
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (arithmeticStageH2Projection F p hpOdd U xU).comp
        (arithmeticStageH2AbsoluteLocalLift F p U xU v) =
      arithmeticStageFinitePlaceAbsoluteRestriction F p hpOdd U v := by
  apply ContinuousMonoidHom.ext
  intro sigma
  exact congrArg
    (openNormalQuotientContinuousEquivArithmeticStageGalois F p hpOdd U)
    (DFunLike.congr_fun (arithmeticStageH2AbsoluteLocalLift_projection F p U xU v) sigma)

/-- Every finite arithmetic-stage central embedding problem has an unramified
continuous solution at each finite place. -/
theorem arithmeticStageH2_exists_absoluteLocalLift_killsInertia
    (hpOdd : Odd p)
    (U : OpenNormalSubgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F p))
    (xU : continuousCohomologyZModPLifted p
      (MaxEverywhereUnramifiedProPGaloisGroup F p ⧸
        (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ∃ s : finitePlaceAbsoluteDecompositionGroup F v →ₜ*
        ClassFieldTower.ProP.DegreeTwoCentralExtension xU,
      (arithmeticStageH2Projection F p hpOdd U xU).comp s =
          arithmeticStageFinitePlaceAbsoluteRestriction F p hpOdd U v ∧
        finitePlaceAbsoluteInertiaSubgroup F v ≤ s.toMonoidHom.ker := by
  exact ⟨arithmeticStageH2AbsoluteLocalLift F p U xU v,
    arithmeticStageH2AbsoluteLocalLift_arithmeticProjection F p hpOdd U xU v,
    arithmeticStageH2AbsoluteLocalLift_inertia_le_ker F p U xU v⟩

end ClassFieldTower.Martinet.Shafarevich
