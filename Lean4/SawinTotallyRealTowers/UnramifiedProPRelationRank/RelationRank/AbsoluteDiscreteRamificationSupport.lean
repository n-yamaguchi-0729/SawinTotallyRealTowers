import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.FinitePlaceAbsoluteInertiaKernel
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
import ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes
import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence

set_option autoImplicit false
/-!
# Finite ramification support of a continuous discrete representation

A continuous map from the absolute Galois group to a discrete group has
open kernel. Its finite Galois fixed field is ramified at only finitely
many finite places. Actual absolute inertia restricts into finite ideal
inertia, so the original map kills inertia outside that finite set.
No finiteness hypothesis on the target group is needed. The two added
local instances are the fixed field's Galois and number-field proofs.
-/

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open RamificationTheory.Field.absoluteGaloisGroup
open AlgebraicNumberTheory.Valuations

variable (F : Type) [Field F] [NumberField F]
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- A continuous discrete representation of the absolute Galois group
is ramified at only finitely many of the chosen finite places. -/
theorem absoluteDiscreteHom_inertia_support_finite
    (s : Field.absoluteGaloisGroup F →ₜ* Q) :
    {v : HeightOneSpectrum (𝓞 F) |
      ∃ sigma : finitePlaceAbsoluteInertiaSubgroup F v,
        s (finitePlaceAbsoluteDecompositionInclusion F v
          (finitePlaceAbsoluteInertiaInclusion F v sigma)) ≠ 1}.Finite := by
  let a : Gal(AlgebraicClosure F/F) →ₜ* Q :=
    s.comp (absoluteGaloisGroupContinuousMulEquiv F).symm
  let H : OpenSubgroup Gal(AlgebraicClosure F/F) :=
    ⟨a.toMonoidHom.ker, (isOpen_discrete ({1} : Set Q)).preimage a.continuous⟩
  let M := fixedFieldOfOpenSubgroup F H
  have hfix : M.fixingSubgroup = a.toMonoidHom.ker :=
    fixingSubgroup_fixedFieldOfOpenSubgroup F H
  let _ : IsGalois F M := (InfiniteGalois.normal_iff_isGalois M).1 (by
    rw [hfix]
    infer_instance)
  let _ : NumberField M := NumberField.of_module_finite F M
  apply (AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes
    (𝓞 F) (𝓞 M)).subset
  rintro v ⟨sigma, hsigma⟩
  by_contra hv
  apply hsigma
  let wM := restrictAbsoluteValueExtensionToIntermediate
    (HeightOneSpectrum.adicAbv F v) (finitePlaceAbsoluteValueExtension F v) M
  let P := finitePlaceExtensionCentre (K := F) (L := M) v wM
  have hP : Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := by
    by_contra hram
    exact hv ⟨P, finitePlaceExtensionCentre_liesOver v wM, hram⟩
  have hmem := finitePlaceAbsoluteInertia_restrictNormal_mem_finiteInertia F M v sigma
  change (sigma.1.1 : Gal(AlgebraicClosure F/F)).restrictNormal M ∈
    HilbertRamification.Dedekind.inertiaGroup P.asIdeal Gal(M/F) at hmem
  have hbot : HilbertRamification.Dedekind.inertiaGroup P.asIdeal Gal(M/F) = ⊥ :=
    HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_isUnramifiedAt P.asIdeal hP
  have hrestrict : (sigma.1.1 : Gal(AlgebraicClosure F/F)).restrictNormal M = 1 := by
    simpa only [hbot, Subgroup.mem_bot] using hmem
  have hker : (sigma.1.1 : Gal(AlgebraicClosure F/F)) ∈ M.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker M, MonoidHom.mem_ker]
    exact hrestrict
  rw [hfix] at hker
  exact hker

end ClassFieldTower.Martinet.Shafarevich
