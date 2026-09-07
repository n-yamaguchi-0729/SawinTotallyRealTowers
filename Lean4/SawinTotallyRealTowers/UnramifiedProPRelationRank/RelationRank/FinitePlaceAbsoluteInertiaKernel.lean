import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteUnramifiedGaloisSequence
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.CompositumUnramified

set_option autoImplicit false
/-!
# Absolute finite-place inertia and the unramified kernel

This file compares the chosen absolute inertia subgroup at a finite place with
finite Galois subextensions of the algebraic closure.  The finite-level
restriction statement is the arithmetic input for showing that absolute
inertia fixes the maximal everywhere-unramified pro-`p` extension.
-/

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open AlgebraicNumberTheory.Valuations

variable (F : Type) [Field F] [NumberField F]

/-- Restricting an element of the chosen absolute inertia group to a finite
Galois subextension puts it in the inertia group at the induced finite place. -/
theorem finitePlaceAbsoluteInertia_restrictNormal_mem_finiteInertia
    (M : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F M] [IsGalois F M] [NumberField M]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteInertiaSubgroup F v) :
    (sigma.1.1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).restrictNormal M ∈
      HilbertRamification.Dedekind.inertiaGroup
        (finitePlaceExtensionCentre
          (K := F) (L := M) v
          (restrictAbsoluteValueExtensionToIntermediate
            (HeightOneSpectrum.adicAbv F v)
            (finitePlaceAbsoluteValueExtension F v) M)).asIdeal
        (M ≃ₐ[F] M) := by
  let w := finitePlaceAbsoluteValueExtension F v
  let wM := restrictAbsoluteValueExtensionToIntermediate
    (HeightOneSpectrum.adicAbv F v) w M
  let A := finitePlaceAbsoluteValuationSubring F v
  let tau := finitePlaceAbsoluteDecompositionValuationEquiv F v sigma.1
  have htau : tau ∈
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup F A :=
    sigma.property
  rw [HilbertRamification.Dedekind.mem_inertiaGroup_iff]
  intro x
  rw [finitePlaceExtensionCentre_asIdeal,
    mem_finitePlaceExtensionCentreIdeal_iff]
  let xA : A :=
    ⟨(x : M), by
      change wM.1 (x : M) ≤ 1
      have hx := ringOfIntegers_mem_finitePlaceExtensionValuationSubring
        (K := F) (L := M) v wM x
      simpa [finitePlaceExtensionValuationSubring,
        mem_absoluteValueValuationSubring_iff] using hx⟩
  have hnonunit :=
    (HilbertRamification.ValuationSubring.mem_inertiaGroup_iff_sub_mem_nonunits
      A tau).mp htau xA
  have hlt :=
    (HilbertRamification.algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one
      w.1 (finitePlaceAbsoluteValueExtension_nonarchimedean F v) _).mp hnonunit
  let sigmaAbs : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := sigma.1.1
  have hcompat :
      algebraMap M (AlgebraicClosure F)
          (((sigmaAbs.restrictNormal M) • x : NumberField.RingOfIntegers M) : M) =
        sigmaAbs (algebraMap M (AlgebraicClosure F) (x : M)) := by
    change algebraMap M (AlgebraicClosure F)
        (sigmaAbs.restrictNormal M x.1) =
      sigmaAbs (algebraMap M (AlgebraicClosure F) x.1)
    exact AlgEquiv.restrictNormal_commutes sigmaAbs M x.1
  change wM.1
    ((((sigmaAbs.restrictNormal M) • x - x : NumberField.RingOfIntegers M) : M)) < 1
  calc
    wM.1
        ((((sigmaAbs.restrictNormal M) • x - x : NumberField.RingOfIntegers M) : M)) =
        w.1
          (sigmaAbs (algebraMap M (AlgebraicClosure F) (x : M)) -
            algebraMap M (AlgebraicClosure F) (x : M)) := by
      change w.1
          (algebraMap M (AlgebraicClosure F)
            ((((sigmaAbs.restrictNormal M) • x - x :
              NumberField.RingOfIntegers M) : M))) = _
      congr 1
      change algebraMap M (AlgebraicClosure F)
          (((((sigmaAbs.restrictNormal M) • x :
            NumberField.RingOfIntegers M) : M)) - (x : M)) = _
      rw [map_sub, hcompat]
    _ < 1 := by
      change w.1
        (sigmaAbs (algebraMap M (AlgebraicClosure F) (x : M)) -
          algebraMap M (AlgebraicClosure F) (x : M)) < 1 at hlt
      exact hlt

/-- Every element of the chosen absolute inertia group at a finite place fixes
the maximal everywhere-unramified pro-`p` extension. -/
theorem finitePlaceAbsoluteInertia_mem_absoluteUnramifiedKernel
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteInertiaSubgroup F v) :
    (sigma.1.1 : Field.absoluteGaloisGroup F) ∈
      (absoluteUnramifiedKernel F p).toSubgroup := by
  let sigmaAbs : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := sigma.1.1
  have hmax :
      maximalEverywhereUnramifiedProP F p ≤
        IntermediateField.fixedField (Subgroup.zpowers sigmaAbs) := by
    apply maximalEverywhereUnramifiedProP_le_of_forall_le
    intro M _ _ _ _ hM
    rw [IntermediateField.le_iff_le, Subgroup.zpowers_le]
    let wM := restrictAbsoluteValueExtensionToIntermediate
      (HeightOneSpectrum.adicAbv F v)
      (finitePlaceAbsoluteValueExtension F v) M
    let P := finitePlaceExtensionCentre (K := F) (L := M) v wM
    have hmem :
        sigmaAbs.restrictNormal M ∈
          HilbertRamification.Dedekind.inertiaGroup P.asIdeal
            (M ≃ₐ[F] M) := by
      simpa [sigmaAbs, P, wM] using
        finitePlaceAbsoluteInertia_restrictNormal_mem_finiteInertia F M v sigma
    have hbot :
        HilbertRamification.Dedekind.inertiaGroup P.asIdeal
            (M ≃ₐ[F] M) = ⊥ :=
      HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_isUnramifiedAt
        P.asIdeal (hM.finitePlaces P)
    have hrestrict : sigmaAbs.restrictNormal M = 1 := by
      simpa [hbot] using hmem
    rw [← IntermediateField.restrictNormalHom_ker M, MonoidHom.mem_ker]
    exact hrestrict
  change sigmaAbs ∈
    (maximalEverywhereUnramifiedProP F p).fixingSubgroup
  have hzpow :
      Subgroup.zpowers sigmaAbs ≤
        (maximalEverywhereUnramifiedProP F p).fixingSubgroup := by
    rw [← IntermediateField.le_iff_le]
    exact hmax
  exact hzpow (Subgroup.mem_zpowers sigmaAbs)

end ClassFieldTower.Martinet.Shafarevich
