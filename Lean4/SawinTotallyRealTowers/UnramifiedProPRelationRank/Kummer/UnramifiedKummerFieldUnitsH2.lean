/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.EverywhereUnramifiedSupportedIdeleH2
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteRootIdeleSupport
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.FiniteFieldUnitsIdelePrimitive

set_option autoImplicit false
/-!
# Kummer H² dies in field units at an unramified p-extension

The two coefficient paths into actual relative ideles coincide: Kummer
coefficients through everywhere-integral ideles, or through field units.
The first has zero H² by the proved local block and restricted-product
construction. Injectivity of field-unit H² into idele H² then supplies an
actual field-unit primitive. Neither an idele primitive nor a comparison
of coefficient maps is an additional hypothesis.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open RelativeIdeleGroup.Cohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

local instance kummerFieldUnitsH2SupportedAction : MulDistribMulAction Gal(L / K)
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) ∅) :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := L) ∅

local instance kummerFieldUnitsH2IdeleAction : MulDistribMulAction Gal(L / K) (RelativeIdeleGroup K L) :=
  relativeIdeleMulDistribMulAction K L

/-- Actual inclusion of everywhere-integral ideles into relative ideles,
as a morphism of the canonical Galois representations. -/
def finiteSupportedIdeleInclusionRepHom :
    Rep.ofMulDistribMulAction Gal(L / K)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) ∅) ⟶
      (finiteIdeleShortComplex K L).X₂ :=
  equivariantRepHom
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) ∅).subtype
    (fun _ _ ↦ rfl)

variable (n : ℕ+) [Fact (n : ℕ).Prime]

omit [IsGalois K L] [Fact (n : ℕ).Prime] in
/-- The two actual Kummer-to-idele coefficient paths agree pointwise. -/
theorem finiteKummerSupportedIdeleRepHom_factor
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    finiteKummerSupportedIdeleRepHom K L n hmu ≫ finiteSupportedIdeleInclusionRepHom K L =
      finiteKummerCoefficientRepHom K L n hmu ≫ finiteFieldUnitsIdeleRepHom K L := by
  ext z
  rfl

/-- Kummer classes in degree two vanish after passage to field units in
an everywhere-unramified finite Galois p-extension. -/
theorem unramifiedFiniteKummerCoefficientH2Map_eq_zero
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hP : IsPGroup (n : ℕ) Gal(L / K))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K)
    (x : groupCohomology (Rep.trivial ℤ Gal(L / K) (ULift (ZMod (n : ℕ)))) 2) :
    (finiteKummerCoefficientH2Map K L n hmu).hom x = 0 := by
  let _ := everywhereUnramifiedSupportedIdeleH2_subsingleton K L hfin hinf
  let C := groupCohomology.functor ℤ Gal(L / K) 2
  have hz : (C.map (finiteKummerSupportedIdeleRepHom K L n hmu)).hom x = 0 := by
    change (groupCohomology.map (MonoidHom.id Gal(L / K))
      (finiteKummerSupportedIdeleRepHom K L n hmu) 2).hom x = 0
    exact Subsingleton.elim _ _
  have hf := congrArg (fun f ↦ (C.map f).hom x)
    (finiteKummerSupportedIdeleRepHom_factor K L n hmu)
  have hleft :
      (C.map (finiteKummerSupportedIdeleRepHom K L n hmu ≫
        finiteSupportedIdeleInclusionRepHom K L)).hom x =
        (C.map (finiteSupportedIdeleInclusionRepHom K L)).hom
          ((C.map (finiteKummerSupportedIdeleRepHom K L n hmu)).hom x) := by
    have hmap := ConcreteCategory.congr_hom
      (C.map_comp
        (finiteKummerSupportedIdeleRepHom K L n hmu)
        (finiteSupportedIdeleInclusionRepHom K L)) x
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
    (C.map (finiteSupportedIdeleInclusionRepHom K L)).hom
        ((C.map (finiteKummerSupportedIdeleRepHom K L n hmu)).hom x) =
      (C.map (finiteFieldUnitsIdeleRepHom K L)).hom
        ((C.map (finiteKummerCoefficientRepHom K L n hmu)).hom x) := by
    exact hleft.symm.trans (hf.trans hright)
  have hzero :
      (C.map (finiteFieldUnitsIdeleRepHom K L)).hom
          ((C.map (finiteKummerCoefficientRepHom K L n hmu)).hom x) = 0 := by
    rw [← hfExpanded, hz, map_zero]
  apply finiteFieldUnitsIdeleH2Map_injective_of_isPGroup K L hP
  change
    (C.map (finiteFieldUnitsIdeleRepHom K L)).hom
        ((C.map (finiteKummerCoefficientRepHom K L n hmu)).hom x) =
      (C.map (finiteFieldUnitsIdeleRepHom K L)).hom 0
  simpa only [map_zero] using hzero

/-- Every finite Kummer two-cocycle admits an actual field-unit primitive
in an everywhere-unramified finite Galois p-extension. -/
theorem unramifiedFiniteKummerTwoCocycle_isFieldUnitsCoboundary
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hP : IsPGroup (n : ℕ) Gal(L / K))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K)
    (c : groupCohomology.cocycles₂ (Rep.trivial ℤ Gal(L / K) (ULift (ZMod (n : ℕ))))) :
    ∃ b : Gal(L / K) → Additive Lˣ,
      (groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K L)).hom b =
        (groupCohomology.mapCocycles₂ (MonoidHom.id Gal(L / K))
          (finiteKummerCoefficientRepHom K L n hmu) c).1 := by
  let d := groupCohomology.mapCocycles₂ (MonoidHom.id Gal(L / K))
    (finiteKummerCoefficientRepHom K L n hmu) c
  apply (groupCohomology.H2π_eq_zero_iff d).1
  have hn := congrArg (fun f ↦ f c)
    (groupCohomology.H2π_comp_map (MonoidHom.id Gal(L / K))
      (finiteKummerCoefficientRepHom K L n hmu))
  exact hn.symm.trans (unramifiedFiniteKummerCoefficientH2Map_eq_zero K L n hmu hP
    hfin hinf (groupCohomology.H2π _ c))

end ClassFieldTower.Martinet.Shafarevich
