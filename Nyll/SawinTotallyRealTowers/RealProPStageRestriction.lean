/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Nyll.SawinTotallyRealTowers.MaximalRealProPOutside
public import Nyll.SawinTotallyRealTowers.RealProPOpenNormalStage
public import Nyll.SawinTotallyRealTowers.AbsoluteRealProPRestriction
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerAbsoluteLift
public import Nyll.GaloisCohomology.ProP.QuotientRestriction
public import Nyll.ProCGroups.Topologies.QuotientMaps
public import Nyll.ProCGroups.Profinite.OpenSubgroups
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Absolute restriction and finite arithmetic stages

The actual finite quotient is continuously identified with the Galois group
of its lifted fixed field. Its restriction map agrees with restriction from
the fixed algebraic closure, by the actions of both maps on every field element.
-/

@[expose] public section

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich ClassFieldTower.Cohomology ProCGroups

/-- The finite open normal quotient and its actual arithmetic Galois group
are continuously isomorphic. -/
def realProPOpenNormalQuotientContinuousEquivStage
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)) :
    ((maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) ⧸
      (U : Subgroup _)) ≃ₜ* ((realProPOpenNormalStage p T U).val ≃ₐ[ℚ]
        (realProPOpenNormalStage p T U).val) :=
  ProCGroups.QuotientGroup.quotientDiscreteEquiv U (realProPOpenNormalQuotientEquivStage p T U)

/-- Restriction to the actual finite arithmetic layer of an open normal subgroup. -/
def realProPOpenNormalStageRestriction
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)) :
    (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) →ₜ*
      ((realProPOpenNormalStage p T U).val ≃ₐ[ℚ]
        (realProPOpenNormalStage p T U).val) :=
  ProCGroups.QuotientGroup.quotientToDiscreteMap U
    (realProPOpenNormalQuotientEquivStage p T U).toMonoidHom

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
