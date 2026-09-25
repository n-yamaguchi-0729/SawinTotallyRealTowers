/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.RealProPFrobenius
import SawinTotallyRealTowers.FinitePlaceFrobenius
import SawinTotallyRealTowers.FinitePlaceDecompositionSplit
import SawinTotallyRealTowers.RealProPDepthStage
import SawinTotallyRealTowers.RealProPStageRestriction
import SawinTotallyRealTowers.RealProPOpenNormalStage
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerAbsoluteLift
import ProCGroups.ProP.Zassenhaus.Depth
import ProCGroups.FiniteGeneration.Basic

set_option autoImplicit false

/-!
# Split finite stages and deep arithmetic Frobenius lifts

The actual arithmetic Frobenius is represented by an absolute decomposition
element. Complete splitting makes its finite-stage restriction trivial,
so the constructed depth-detecting stage supplies a deep source lift.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich ClassFieldTower.ProP
open ProCGroups.FiniteGeneration

universe u

private local instance depthStageIsGalois
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T)) :
    IsGalois ℚ (realProPOpenNormalStage p T U).val.toIntermediateField :=
  (realProPOpenNormalStage p T U).val.isGalois

/-- Arithmetic Frobenius acts trivially on an actual finite arithmetic
stage at every place which splits completely in that stage. -/
theorem maximalRealProPArithmeticFrobenius_stageRestriction_eq_one
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T))
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hsplit : FinitePlaceSplitsCompletely
      (K := ℚ) (L := (realProPOpenNormalStage p T U).val) v) :
    realProPOpenNormalStageRestriction p T U
      (maximalRealProPArithmeticFrobenius p T v) = 1 := by
  let σ := finitePlaceArithmeticFrobeniusLift ℚ v
  have hcomm := congrArg
    (fun f : Field.absoluteGaloisGroup ℚ →ₜ*
      ((realProPOpenNormalStage p T U).val ≃ₐ[ℚ]
        (realProPOpenNormalStage p T U).val) ↦ f σ.1)
    (realProPOpenNormalStageRestriction_comp_absolute p T U)
  change realProPOpenNormalStageRestriction p T U
      (maximalRealProPArithmeticFrobenius p T v) =
    absoluteFiniteGaloisRestriction ℚ (realProPOpenNormalStage p T U).val σ.1 at hcomm
  exact hcomm.trans
    (finitePlaceAbsoluteDecomposition_restrictNormal_eq_one_of_splitsCompletely
      ℚ (realProPOpenNormalStage p T U).val v hsplit σ)

/-- For every requested source depth, an actual finite arithmetic stage
ensures that its completely split places have Frobenius lifts of that depth. -/
theorem exists_realProPOpenNormalStage_with_deep_frobenius_lifts
    (p : ℕ) [Fact p.Prime] (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (hfg : TopologicallyFinitelyGenerated F)
    (q : F →ₜ* (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T))
    (hq : Function.Surjective q) (n : ℕ) :
    ∃ U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T),
      ∀ v : HeightOneSpectrum (𝓞 ℚ),
        FinitePlaceSplitsCompletely (K := ℚ) (L := (realProPOpenNormalStage p T U).val) v →
          ∃ f : F, q f = maximalRealProPArithmeticFrobenius p T v ∧
            ZassenhausDepthAtLeast p n f := by
  obtain ⟨U, hU⟩ := exists_realProPOpenNormalStage_with_zassenhaus_lifts p T hfg q hq n
  exact ⟨U, fun v hv ↦ hU (maximalRealProPArithmeticFrobenius p T v)
    (maximalRealProPArithmeticFrobenius_stageRestriction_eq_one p T U v hv)⟩

end ClassFieldTower.Sawin
