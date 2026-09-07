import SawinTotallyRealTowers.RealProPStageRestriction
import SawinTotallyRealTowers.RealProPOpenNormalStage
import SawinTotallyRealTowers.MaximalRealProPOutside
import Mathlib.FieldTheory.Galois.Profinite
import ProCGroups.ProP.Zassenhaus.OpenNormal
import Mathlib.GroupTheory.QuotientGroup.Defs

set_option autoImplicit false

/-!
# Finite arithmetic stages detecting source depth

An actual quotient of a finitely generated profinite group admits finite
arithmetic stages such that every element trivial on that stage has a lift
of any prescribed augmentation depth in the source.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

open ClassFieldTower.ProP ProCGroups.FiniteGeneration

universe u

/-- Restriction to the arithmetic stage detects precisely the selected open
normal subgroup of the actual maximal real Galois group. -/
theorem realProPOpenNormalStageRestriction_eq_one_iff
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T))
    (g : maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) :
    realProPOpenNormalStageRestriction p T U g = 1 ↔ g ∈ U := by
  let e := realProPOpenNormalQuotientEquivStage p T U
  change e (QuotientGroup.mk' (U : Subgroup _) g) = 1 ↔ g ∈ U
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff g

/-- A finite arithmetic layer is constructed so that every element trivial
on that layer has a source lift of the requested depth. -/
theorem exists_realProPOpenNormalStage_with_zassenhaus_lifts
    (p : ℕ) [Fact p.Prime] (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (hfg : TopologicallyFinitelyGenerated F)
    (q : F →ₜ* (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T))
    (hq : Function.Surjective q) (n : ℕ) :
    ∃ U : OpenNormalSubgroup
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T),
      ∀ g : maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T,
        realProPOpenNormalStageRestriction p T U g = 1 →
          ∃ f : F, q f = g ∧ ZassenhausDepthAtLeast p n f := by
  let : IsGalois ℚ (maximalRealProPOutside p T) :=
    maximalRealProPOutside_isGalois p T
  obtain ⟨U, hU⟩ := exists_openNormal_with_zassenhaus_lifts p hfg q hq n
  exact ⟨U, fun g hg ↦ hU g
    ((realProPOpenNormalStageRestriction_eq_one_iff p T U g).mp hg)⟩

end ClassFieldTower.Sawin
