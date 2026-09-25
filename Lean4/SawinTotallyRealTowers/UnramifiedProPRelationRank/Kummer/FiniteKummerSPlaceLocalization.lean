/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.SupportedSPlaceFactorsH2Localization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteRootIdeleSupport
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.FiniteFieldUnitsIdelePrimitive
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.FiniteIdeleH2Injection
import ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.SPlaces
import GaloisCohomology.Kummer.FiniteKummerCoefficientH2
import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

set_option autoImplicit false

/-!
# Finite Kummer coefficients in an arbitrary finite idele support

Roots of unity are integral at every finite place. The empty-support
coefficient map therefore factors through each prescribed finite support,
without changing the principal idele in the full idele representation.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open RelativeIdeleGroup.Cohomology CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

local instance finiteKummerSPlaceSupportedAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := L) S

local instance finiteKummerSPlaceIdeleAction :
    MulDistribMulAction Gal(L / K) (RelativeIdeleGroup K L) :=
  relativeIdeleMulDistribMulAction K L

/-- Roots of unity mapped into any prescribed finite idele support. -/
def finiteKummerSSupportedIdeleRepHom
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Rep.trivial ℤ Gal(L / K) (ULift (ZMod (n : ℕ))) ⟶
      Rep.ofMulDistribMulAction Gal(L / K)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) := by
  apply Rep.ofHom
  let i := Subgroup.inclusion (relativeIdeleLocalTensorDecompositionSupportedSubgroup_mono
    (K := K) (L := L) (Finset.empty_subset S))
  refine ⟨((MonoidHom.toAdditive i).comp
    (finiteKummerSupportedIdeleAddHom K L n hmu)).toIntLinearMap, ?_⟩
  intro g
  apply LinearMap.ext
  intro z
  apply Additive.toMul.injective
  apply Subtype.ext
  change RelativeIdeleGroup.principalIdele K L
      (finiteKummerCoefficientAddHom K L n hmu z).toMul =
    g • RelativeIdeleGroup.principalIdele K L
      (finiteKummerCoefficientAddHom K L n hmu z).toMul
  rw [RelativeIdeleGroup.smul_principalIdele]
  exact congrArg (fun x : Additive Lˣ => RelativeIdeleGroup.principalIdele K L x.toMul)
    (finiteKummerCoefficientAddHom_fixed K L n hmu g z).symm

/-- The actual inclusion of finite-support ideles in all relative ideles. -/
def finiteSSupportedIdeleInclusionRepHom
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Rep.ofMulDistribMulAction Gal(L / K)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) ⟶
      (finiteIdeleShortComplex K L).X₂ :=
  equivariantRepHom
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S).subtype
    (fun _ _ => rfl)

/-- Passing a Kummer coefficient through the supported subgroup or through
field units gives the same actual principal idele. -/
theorem finiteKummerSSupportedIdeleRepHom_factor
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    finiteKummerSSupportedIdeleRepHom K L S n hmu ≫
        finiteSSupportedIdeleInclusionRepHom K L S =
      finiteKummerCoefficientRepHom K L n hmu ≫ finiteFieldUnitsIdeleRepHom K L := by
  ext z
  rfl


variable [IsGalois K L]

local instance finiteKummerSPlaceTensorAction (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L / K) (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.adicCompletion K)

/-- The actual finite Kummer class localized at the finite tensor blocks
in the chosen exceptional support. -/
def finiteKummerSPlaceH2Localization
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    groupCohomology (Rep.trivial ℤ Gal(L / K) (ULift (ZMod (n : ℕ)))) 2 →+
      ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        groupCohomology
          (Rep.ofMulDistribMulAction Gal(L / K) (v.1.adicCompletion K ⊗[K] L)ˣ) 2 :=
  (supportedSPlaceH2Localization K L S).comp
    (((groupCohomology.functor ℤ Gal(L / K) 2).map
      (finiteKummerSSupportedIdeleRepHom K L S n hmu)).hom.toAddMonoidHom)

/-- A Kummer class vanishing at all exceptional finite coordinates dies
in field-unit cohomology when the other local blocks are unramified.
This is a kernel containment, not injectivity of the Kummer coefficient map. -/
theorem finiteKummerSPlaceH2Localization_ker_le
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+) [Fact (n : ℕ).Prime]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hP : IsPGroup (n : ℕ) Gal(L / K))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K) :
    (finiteKummerSPlaceH2Localization K L S n hmu).ker ≤
      (finiteKummerCoefficientH2Map K L n hmu).hom.toAddMonoidHom.ker := by
  intro x hx
  change finiteKummerSPlaceH2Localization K L S n hmu x = 0 at hx
  change (finiteKummerCoefficientH2Map K L n hmu).hom x = 0
  let C := groupCohomology.functor ℤ Gal(L / K) 2
  have hz : (C.map (finiteKummerSSupportedIdeleRepHom K L S n hmu)).hom x = 0 := by
    apply supportedSPlaceH2Localization_injective K L S hfin hinf
    change finiteKummerSPlaceH2Localization K L S n hmu x =
      supportedSPlaceH2Localization K L S 0
    exact hx.trans (map_zero _).symm
  have hf := congrArg (fun f ↦ (C.map f).hom x)
    (finiteKummerSSupportedIdeleRepHom_factor K L S n hmu)
  have hleft :
      (C.map (finiteKummerSSupportedIdeleRepHom K L S n hmu ≫
        finiteSSupportedIdeleInclusionRepHom K L S)).hom x =
        (C.map (finiteSSupportedIdeleInclusionRepHom K L S)).hom
          ((C.map (finiteKummerSSupportedIdeleRepHom K L S n hmu)).hom x) := by
    have hmap := ConcreteCategory.congr_hom
      (C.map_comp
        (finiteKummerSSupportedIdeleRepHom K L S n hmu)
        (finiteSSupportedIdeleInclusionRepHom K L S)) x
    erw [ConcreteCategory.comp_apply] at hmap
    exact hmap
  have hright :
      (C.map (finiteKummerCoefficientRepHom K L n hmu ≫
        finiteFieldUnitsIdeleRepHom K L)).hom x =
        (C.map (finiteFieldUnitsIdeleRepHom K L)).hom
          ((C.map (finiteKummerCoefficientRepHom K L n hmu)).hom x) := by
    have hmap := ConcreteCategory.congr_hom
      (C.map_comp
        (finiteKummerCoefficientRepHom K L n hmu)
        (finiteFieldUnitsIdeleRepHom K L)) x
    erw [ConcreteCategory.comp_apply] at hmap
    exact hmap
  have hfExpanded :
      (C.map (finiteSSupportedIdeleInclusionRepHom K L S)).hom
          ((C.map (finiteKummerSSupportedIdeleRepHom K L S n hmu)).hom x) =
        (C.map (finiteFieldUnitsIdeleRepHom K L)).hom
          ((C.map (finiteKummerCoefficientRepHom K L n hmu)).hom x) :=
    hleft.symm.trans (hf.trans hright)
  have hzero :
      (C.map (finiteFieldUnitsIdeleRepHom K L)).hom
          ((C.map (finiteKummerCoefficientRepHom K L n hmu)).hom x) = 0 := by
    rw [← hfExpanded, hz, map_zero]
  apply finiteFieldUnitsIdeleH2Map_injective_of_isPGroup K L hP
  change (C.map (finiteFieldUnitsIdeleRepHom K L)).hom
      ((C.map (finiteKummerCoefficientRepHom K L n hmu)).hom x) =
    (C.map (finiteFieldUnitsIdeleRepHom K L)).hom 0
  simpa only [map_zero] using hzero

end ClassFieldTower.Martinet.Shafarevich
end
