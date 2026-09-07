import SawinTotallyRealTowers.RealProPFrobeniusFixedField
import SawinTotallyRealTowers.RealProPFrobeniusCut
import SawinTotallyRealTowers.RealProPFrobenius
import SawinTotallyRealTowers.RealProTwoFrobeniusSequence
import SawinTotallyRealTowers.AbsoluteRealProPRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeSubextension
import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs

set_option autoImplicit false

/-!
# Complete splitting in every finite layer of the actual cut field

The actual quotient kills the absolute decomposition groups at selected
unramified primes. Thus those groups fix the cut field elementwise. The
proved restriction-image theorem for decomposition groups then gives complete
splitting in every finite Galois layer inside that field.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich AlgebraicNumberTheory.Valuations

private local instance finiteCutLayerIsGalois
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsGalois ℚ E.toIntermediateField := E.isGalois

/-- Trivial absolute decomposition action on an actual finite Galois layer
implies complete splitting there. -/
private theorem finitePlaceSplitsCompletely_of_absoluteDecomposition_trivial
    (F : Type) [Field F] [NumberField F]
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (w : HeightOneSpectrum (𝓞 F))
    (h : ∀ σ : finitePlaceAbsoluteDecompositionGroup F w,
      AlgEquiv.restrictNormalHom E σ.1 = 1) :
    FinitePlaceSplitsCompletely (K := F) (L := E) w := by
  let a := finitePlaceAbsoluteValueExtension F w
  let aE := restrictAbsoluteValueExtensionToIntermediate
    (HeightOneSpectrum.adicAbv F w) a E.toIntermediateField
  have hmap : (finitePlaceAbsoluteDecompositionGroup F w).map
      (AlgEquiv.restrictNormalHom E) =
        HilbertRamification.absoluteValueDecompositionGroup F aE.1 :=
    absoluteValueDecompositionGroup_map_restrictNormalHom
      (M := E) (HeightOneSpectrum.adicAbv F w) (RayClass.adicAbv_isNontrivial w) a
  have hbot : HilbertRamification.absoluteValueDecompositionGroup F aE.1 = ⊥ := by
    rw [← hmap]
    apply le_antisymm _ bot_le
    rintro _ ⟨σ, hσ, rfl⟩
    exact Subgroup.mem_bot.mpr (h ⟨σ, hσ⟩)
  exact absoluteValueDecompositionGroup_eq_bot_independent_extension
    (HeightOneSpectrum.adicAbv F w) (RayClass.adicAbv_isNontrivial w)
    aE (chosenFinitePlaceExtension (L := E) w) hbot

/-- At a selected place outside the original support, the actual absolute
decomposition group fixes every element of the cut field. -/
theorem realProPFrobeniusFixedField_absoluteDecomposition_fixes
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (v : ℕ → HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hv : v n ∉ T)
    (σ : finitePlaceAbsoluteDecompositionGroup ℚ (v n))
    (x : AlgebraicClosure ℚ) (hx : x ∈ realProPFrobeniusFixedField p T v) :
    σ.1 x = x := by
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := maximalRealProPOutside p T
  let g : M ≃ₐ[ℚ] M := maximalRealProPDecompositionMap p T (v n) σ
  have hg : g ∈ realProPFrobeniusCutKernel p T v :=
    (QuotientGroup.eq_one_iff g).mp
      (realProPFrobeniusCutProjection_decomposition p T v n hv σ)
  obtain ⟨y, hy, rfl⟩ := hx
  have hfix : g y = y :=
    (IntermediateField.mem_fixedField_iff (realProPFrobeniusCutKernel p T v) y).mp hy g hg
  have hvalue := congrArg (fun z : M ↦ (z : AlgebraicClosure ℚ)) hfix
  exact (absoluteToMaximalRealProPOutside_apply p T σ.1 y).symm.trans hvalue

/-- Every finite Galois layer in the actual cut field splits at every
selected place outside the original ramification support. -/
theorem realProPFrobeniusFixedField_finiteLayer_splits
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (v : ℕ → HeightOneSpectrum (𝓞 ℚ))
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : E.toIntermediateField ≤ realProPFrobeniusFixedField p T v)
    (n : ℕ) (hv : v n ∉ T) :
    FinitePlaceSplitsCompletely (K := ℚ) (L := E) (v n) := by
  apply finitePlaceSplitsCompletely_of_absoluteDecomposition_trivial ℚ E (v n)
  intro σ
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E (AlgebraicClosure ℚ)).injective
  exact (AlgEquiv.restrictNormal_commutes σ.1 E x).trans
    (realProPFrobeniusFixedField_absoluteDecomposition_fixes p T v n hv σ
      (x : AlgebraicClosure ℚ) (hE x.property))

/-- The unconditional S3 quotient gives an actual infinite Galois, totally
real field and infinitely many completely split primes in all its finite
Galois layers. -/
theorem exists_sawinInfinite_totallyReal_split_field :
    ∃ primes : ℕ → Nat.Primes, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      IsGalois ℚ L ∧ IsTotallyReal L ∧ Infinite (L ≃ₐ[ℚ] L) ∧
      L ≤ maximalRealProPOutside 2 sawinRationalPrimeSupport ∧
      (∀ n : ℕ, n < (primes n).val ∧
        (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (primes n) ∉
          sawinRationalPrimeSupport ∧ (primes n).val % 4 = 1) ∧
      (Set.range primes).Infinite ∧
      ∀ E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ),
        E.toIntermediateField ≤ L → ∀ n : ℕ,
          FinitePlaceSplitsCompletely (K := ℚ) (L := E)
            ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (primes n)) := by
  obtain ⟨primes, hprimes, hrange, hInfinite, _⟩ :=
    exists_sawinInfinite_decomposition_split_quotient
  let v : ℕ → HeightOneSpectrum (𝓞 ℚ) := fun n ↦
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (primes n)
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    realProPFrobeniusFixedField 2 sawinRationalPrimeSupport v
  let : Infinite (RealProPFrobeniusCut 2 sawinRationalPrimeSupport v) := hInfinite
  have hGal : Infinite (L ≃ₐ[ℚ] L) :=
    Infinite.of_surjective
      (realProPFrobeniusCutEquivFixedField 2 sawinRationalPrimeSupport v).symm
      (realProPFrobeniusCutEquivFixedField 2 sawinRationalPrimeSupport v).symm.surjective
  refine ⟨primes, L, realProPFrobeniusFixedField_isGalois 2 sawinRationalPrimeSupport v,
    realProPFrobeniusFixedField_isTotallyReal 2 sawinRationalPrimeSupport v,
    hGal, realProPFrobeniusFixedField_le 2 sawinRationalPrimeSupport v,
    hprimes, hrange, ?_⟩
  intro E hE n
  exact realProPFrobeniusFixedField_finiteLayer_splits
    2 sawinRationalPrimeSupport v E hE n (hprimes n).2.1

end ClassFieldTower.Sawin
