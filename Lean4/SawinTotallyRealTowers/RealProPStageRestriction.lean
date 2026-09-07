import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.Topology.Algebra.Group.Quotient
import SawinTotallyRealTowers.MaximalRealProPOutside
import SawinTotallyRealTowers.RealProPOpenNormalStage
import SawinTotallyRealTowers.AbsoluteRealProPRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerAbsoluteLift
import GaloisCohomology.ProP.QuotientRestriction
import ProCGroups.Topologies.QuotientMaps
import ProCGroups.Profinite.OpenSubgroups
import Mathlib.FieldTheory.Galois.Profinite

set_option autoImplicit false

/-!
# Absolute restriction and finite arithmetic stages

The actual finite quotient is continuously identified with the Galois group
of its lifted fixed field. Its restriction map agrees with restriction from
the fixed algebraic closure, by the actions of both maps on every field element.
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich ClassFieldTower.Cohomology ProCGroups

private def quotientToDiscreteMap
    {G H : Type} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] [Group H] [TopologicalSpace H]
    (U : OpenNormalSubgroup G) (f : (G ⧸ (U : Subgroup G)) →* H) : G →ₜ* H := by
  let : DiscreteTopology (G ⧸ (U : Subgroup G)) :=
    QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
  exact
    { toMonoidHom := f.comp (QuotientGroup.mk' (U : Subgroup G))
      continuous_toFun := (show Continuous f from continuous_of_discreteTopology).comp
        (show Continuous (QuotientGroup.mk' (U : Subgroup G)) from QuotientGroup.continuous_mk) }

private def quotientDiscreteEquiv
    {G H : Type} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (U : OpenNormalSubgroup G) (e : (G ⧸ (U : Subgroup G)) ≃* H) :
    (G ⧸ (U : Subgroup G)) ≃ₜ* H := by
  let : DiscreteTopology (G ⧸ (U : Subgroup G)) :=
    QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
  exact
    { toMulEquiv := e
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The finite open normal quotient and its actual arithmetic Galois group
are continuously isomorphic. -/
def realProPOpenNormalQuotientContinuousEquivStage
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)) :
    ((maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) ⧸
      (U : Subgroup _)) ≃ₜ* ((realProPOpenNormalStage p T U).val ≃ₐ[ℚ]
        (realProPOpenNormalStage p T U).val) :=
  quotientDiscreteEquiv U (realProPOpenNormalQuotientEquivStage p T U)

/-- Restriction to the actual finite arithmetic layer of an open normal subgroup. -/
def realProPOpenNormalStageRestriction
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)) :
    (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) →ₜ*
      ((realProPOpenNormalStage p T U).val ≃ₐ[ℚ]
        (realProPOpenNormalStage p T U).val) :=
  quotientToDiscreteMap U (realProPOpenNormalQuotientEquivStage p T U).toMonoidHom

/-- Restriction through the actual maximal field agrees with absolute restriction
on its finite arithmetic layer. -/
theorem realProPOpenNormalStageRestriction_comp_absolute
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)) :
    (realProPOpenNormalStageRestriction p T U).comp
      (absoluteToMaximalRealProPOutside p T) =
    absoluteFiniteGaloisRestriction ℚ (realProPOpenNormalStage p T U).val := by
  apply ContinuousMonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have h := realProPOpenNormalQuotientEquivStage_apply p T U
    (absoluteToMaximalRealProPOutside p T σ) x
  have hA := absoluteToMaximalRealProPOutside_apply p T σ
    ⟨(x : AlgebraicClosure ℚ),
      le_maximalRealProPOutside (realProPOpenNormalStage p T U) x.property⟩
  have hR := AlgEquiv.restrictNormalHom_apply
    (realProPOpenNormalStage p T U).val.toIntermediateField
    (absoluteGaloisGroupContinuousMulEquiv ℚ σ) x
  exact (h.trans hA).trans hR.symm

end ClassFieldTower.Sawin
