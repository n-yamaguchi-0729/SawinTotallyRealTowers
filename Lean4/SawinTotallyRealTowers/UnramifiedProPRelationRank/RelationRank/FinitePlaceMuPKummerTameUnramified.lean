/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.ContinuousH1Bridge
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.FinitePlaceAbsoluteInertiaKernel
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FinitePlaceMuPH1RamificationLocalization
import ClassFieldTheory.KummerTheory.Concrete.SUnitKummerUnramified

set_option autoImplicit false
/-!
# Tame unramifiedness of finite-place natural `mu_p` Kummer classes

Away from a prescribed finite set and from the residue characteristics
dividing `p`, an `S`-unit Kummer extension is unramified.  This file applies
that arithmetic statement to the chosen algebraic-closure root defining the
natural-`mu_p` Kummer cocycle.  Absolute inertia therefore fixes the root, so
the inertia-restricted cocycle, and hence its continuous `H¹` class, vanish.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open AlgebraicNumberTheory.Valuations
open ClassFieldTower.Cohomology KummerTheory TopRep

variable (K : Type) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime]

/-- At a tame place outside `S`, absolute inertia fixes the chosen root used
to define the natural-`mu_p` Kummer cocycle of an `S`-unit. -/
theorem finitePlaceAbsoluteInertia_fixes_absoluteKummerChosenRoot_of_sUnit
    (hmu : (primitiveRoots p K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : SUnitGroup (K := K) S)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S)
    (hp : v.valuation K (p : K) = 1)
    (sigma : finitePlaceAbsoluteInertiaSubgroup K v) :
    sigma.1.1 • absoluteKummerChosenRoot K p a.1 =
      absoluteKummerChosenRoot K p a.1 := by
  let n : ℕ+ := (p.toPNat (Fact.out : p.Prime).pos)
  have hpn : ((n : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr n.ne_zero
  let E := fullSUnitKummerExtension
    (K := K) (Omega := AlgebraicClosure K) n S
  let _ : FiniteDimensional K E :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := AlgebraicClosure K) n hpn hmu S
  let _ : IsGalois K E :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := AlgebraicClosure K) n S
  let _ : NumberField E :=
    NumberField.of_module_finite K E
  have hunramified :
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v := by
    simpa only [E, n] using
      fullSUnitKummerExtension_chosenFinitePlaceIsUnramified_of_not_mem
        (K := K) (Omega := AlgebraicClosure K)
        n hpn hmu S v hv hp
  let beta : (AlgebraicClosure K)ˣ :=
    absoluteKummerChosenRoot K p a.1
  have hbetaRoot : (beta : AlgebraicClosure K) ∈
      kummerRootSet (K := K) (Omega := AlgebraicClosure K) n
        (fullSUnitKummerSubgroup (K := K) n S).1 := by
    refine ⟨sUnitToFullSUnitKummerSubgroup (K := K) n S a, ?_⟩
    change
      ((absoluteKummerChosenRoot K p a.1 : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K) ^ p =
        algebraMap K (AlgebraicClosure K) (a.1 : K)
    exact congrArg Units.val (absoluteKummerChosenRoot_pow K p a.1)
  have hbetaE : (beta : AlgebraicClosure K) ∈ E := by
    exact IntermediateField.subset_adjoin K _ hbetaRoot
  let betaE : E := ⟨(beta : AlgebraicClosure K), hbetaE⟩
  let wE := restrictAbsoluteValueExtensionToIntermediate
    (HeightOneSpectrum.adicAbv K v)
    (finitePlaceAbsoluteValueExtension K v) E
  let P := finitePlaceExtensionCentre (K := K) (L := E) v wE
  have hPunramified :
      Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal :=
    isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
      (K := K) (L := E) v P
        (finitePlaceBelow_finitePlaceExtensionCentre v wE) hunramified
  have hmem :
      ((sigma.1.1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K).restrictNormal E) ∈
        HilbertRamification.Dedekind.inertiaGroup
          P.asIdeal (E ≃ₐ[K] E) := by
    simpa only [P, wE] using
      finitePlaceAbsoluteInertia_restrictNormal_mem_finiteInertia K E v sigma
  have hbot :
      HilbertRamification.Dedekind.inertiaGroup
          P.asIdeal (E ≃ₐ[K] E) = ⊥ :=
    HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_isUnramifiedAt
      P.asIdeal hPunramified
  have hrestrict :
      (sigma.1.1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K).restrictNormal E = 1 := by
    simpa only [hbot, Subgroup.mem_bot] using hmem
  have hcomm := AlgEquiv.restrictNormal_commutes
    (sigma.1.1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) E betaE
  have hfixVal :
      sigma.1.1 (beta : AlgebraicClosure K) = beta := by
    rw [hrestrict] at hcomm
    simpa only [betaE, AlgEquiv.one_apply, IntermediateField.algebraMap_apply]
      using hcomm.symm
  apply Units.ext
  exact hfixVal

/-- The natural-`mu_p` Kummer root cocycle of an `S`-unit vanishes on
absolute inertia at a tame place outside `S`. -/
theorem absoluteKummerMuPRootCocycle_eq_zero_on_inertia_of_sUnit
    (hmu : (primitiveRoots p K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : SUnitGroup (K := K) S)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S)
    (hp : v.valuation K (p : K) = 1)
    (sigma : finitePlaceAbsoluteInertiaSubgroup K v) :
    absoluteKummerMuPRootCocycle K p a.1
        (finitePlaceAbsoluteDecompositionInclusion K v
          (finitePlaceAbsoluteInertiaInclusion K v sigma)) = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [absoluteKummerMuPRootCocycle_apply_coe]
  apply div_eq_one.mpr
  exact finitePlaceAbsoluteInertia_fixes_absoluteKummerChosenRoot_of_sUnit
    K p hmu S a v hv hp sigma

/-- The inertia-restricted homogeneous natural-`mu_p` Kummer cocycle of an
`S`-unit is zero at a tame place outside `S`. -/
theorem finitePlaceAbsoluteKummerMuPInertiaHomogeneousOneCocycle_eq_zero_of_sUnit
    (hmu : (primitiveRoots p K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : SUnitGroup (K := K) S)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S)
    (hp : v.valuation K (p : K) = 1) :
    finitePlaceAbsoluteKummerMuPInertiaHomogeneousOneCocycle K p v a.1 = 0 := by
  apply topModule_mono_injective
    ((TopRep.homogeneousCochains
      (finitePlaceAbsoluteInertiaMuPTopRep K p v)).iCycles 1)
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
    ConcreteCategory.comp_apply]
  rw [map_zero]
  change
    ((ContinuousCohomology.cochainsMap
      (finitePlaceAbsoluteInertiaInclusion K v)
      (finitePlaceAbsoluteMuPInertiaRestrictionHom K p v)).f 1).hom
        (((TopRep.homogeneousCochains
          (finitePlaceAbsoluteMuPTopRep K p v)).iCycles 1)
            (finitePlaceAbsoluteMuPCocyclesMap K p v
              (absoluteKummerMuPHomogeneousOneCocycle K p a.1))) = 0
  have hdecomposition := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (ContinuousCohomology.cochainsMap
        (finitePlaceAbsoluteDecompositionInclusion K v)
        (finitePlaceAbsoluteMuPRestrictionHom K p v)) 1)
      (absoluteKummerMuPHomogeneousOneCocycle K p a.1)
  simp only [ConcreteCategory.comp_apply] at hdecomposition
  rw [hdecomposition]
  rw [iCycles_absoluteKummerMuPHomogeneousOneCocycle]
  apply Subtype.ext
  ext g h
  change
    absoluteKummerMuPRootCocycle K p a.1
          (finitePlaceAbsoluteDecompositionInclusion K v
            (finitePlaceAbsoluteInertiaInclusion K v h)) -
        absoluteKummerMuPRootCocycle K p a.1
          (finitePlaceAbsoluteDecompositionInclusion K v
            (finitePlaceAbsoluteInertiaInclusion K v g)) = 0
  rw [absoluteKummerMuPRootCocycle_eq_zero_on_inertia_of_sUnit
      K p hmu S a v hv hp h,
    absoluteKummerMuPRootCocycle_eq_zero_on_inertia_of_sUnit
      K p hmu S a v hv hp g,
    sub_self]

/-- At a tame place outside `S`, the inertia-localized natural-`mu_p`
Kummer `H¹` class of an `S`-unit vanishes. -/
theorem finitePlaceAbsoluteKummerMuPInertiaH1Class_eq_zero_of_sUnit
    (hmu : (primitiveRoots p K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : SUnitGroup (K := K) S)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S)
    (hp : v.valuation K (p : K) = 1) :
    finitePlaceAbsoluteKummerMuPInertiaH1Class K p v a.1 = 0 := by
  rw [finitePlaceAbsoluteKummerMuPInertiaH1Class,
    finitePlaceAbsoluteKummerMuPInertiaHomogeneousOneCocycle_eq_zero_of_sUnit
      K p hmu S a v hv hp]
  exact map_zero
    (ContinuousCohomology.π
      (finitePlaceAbsoluteInertiaMuPTopRep K p v) 1).hom

end ClassFieldTower.Martinet.Shafarevich
