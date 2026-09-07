import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.UnramifiedLocalIntegerUnitsH2
import GaloisCohomology.ProP.MultiplicativeInducedShapiro
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlace
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceAction
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlock
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquiv
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquivApply
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInclusion
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInducedSmul
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockTensorSmul
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.CompletionTransport
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Spine
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Action
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Equiv
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Inclusion

set_option autoImplicit false
/-!
# H² of the actual unramified finite-place integral block

At an unramified finite place, integer-unit `H²` vanishes on the chosen
localized extension.  The actual decomposition-group action, the proved
multiplicative Shapiro isomorphism, and the equivariant integral tensor
decomposition transport this vanishing to the full global Galois group.
No cyclicity of the global Galois group is assumed.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField ValuativeRel NNReal

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology CyclicCohomology
open AlgebraicNumberTheory.Valuations HilbertRamification
open LocalClassFieldTheory LocalFieldTheory

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

-- Each of the three canonical representations is fixed once; their
-- coefficient types are distinct, so no competing action is introduced.
local instance (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup (K := K) (L := L) v)
      (ChosenFinitePlaceLocalizedIntegerUnits (K := K) (L := L) v) :=
  chosenFinitePlaceDecompositionGroupIntegerUnitsAction (K := K) (L := L) v

local instance (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L / K)
      (ChosenFinitePlaceInducedIntegerUnits (K := K) (L := L) v) :=
  chosenFinitePlaceInducedIntegerUnitsAction (K := K) (L := L) v

local instance (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L / K)
      (relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v) :=
  relativeLocalTensorDecompositionIntegralUnitSubgroupAction (K := K) (L := L) v

omit [NumberField L] in
/-- The actual chosen decomposition-group representation on integer units
has zero `H²` at an unramified finite place. -/
theorem chosenFinitePlaceIntegerUnitsH2_subsingleton
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    Subsingleton (groupCohomology
      (Rep.ofMulDistribMulAction
        (ChosenFinitePlaceDecompositionGroup (K := K) (L := L) v)
        (ChosenFinitePlaceLocalizedIntegerUnits (K := K) (L := L) v)) 2) := by
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let _ : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension C E := hunram
  let _ := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure C E
  let _ : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(E / C) 𝒪[E]ˣ) 2) :=
    unramifiedLocalIntegerUnitsH2_subsingleton C E
  let e := decompositionGroupEquivAlgebraicLocalizationAut
    (HeightOneSpectrum.adicAbv K v) (RayClass.adicAbv_isNontrivial v)
    (chosenFinitePlaceExtension (L := L) v)
  let i := groupCohomology.mapIso
    (A := Rep.ofMulDistribMulAction Gal(E / C) 𝒪[E]ˣ)
    (B := Rep.ofMulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup (K := K) (L := L) v)
      (ChosenFinitePlaceLocalizedIntegerUnits (K := K) (L := L) v))
    e (LinearEquiv.refl ℤ (Additive 𝒪[E]ˣ)) (by
      intro g
      apply LinearMap.ext
      intro x
      exact congrArg Additive.ofMul
        (chosenFinitePlaceDecompositionGroupIntegerUnitsAction_smul_eq_pullback
          (K := K) (L := L) v g x.toMul)) 2
  exact Function.Injective.subsingleton i.toLinearEquiv.injective

omit [NumberField L] in
/-- Shapiro transfers the actual unramified integer-unit vanishing to
the full global Galois action on its induced local block. -/
theorem chosenFinitePlaceInducedIntegerUnitsH2_subsingleton
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    Subsingleton (groupCohomology
      (Rep.ofMulDistribMulAction Gal(L / K)
        (ChosenFinitePlaceInducedIntegerUnits (K := K) (L := L) v)) 2) := by
  let _ := chosenFinitePlaceIntegerUnitsH2_subsingleton K L v hunram
  exact multiplicativeInducedCohomology_subsingleton
    (ChosenFinitePlaceDecompositionGroup (K := K) (L := L) v)
    (ChosenFinitePlaceLocalizedIntegerUnits (K := K) (L := L) v) 2

omit [NumberField L] in
/-- The actual integral tensor block at an unramified finite place has
zero `H²` for the full, not necessarily cyclic, global Galois group. -/
theorem unramifiedFinitePlaceIntegralBlockH2_subsingleton
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    Subsingleton (groupCohomology
      (Rep.ofMulDistribMulAction Gal(L / K)
        (relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v)) 2) := by
  let _ := chosenFinitePlaceInducedIntegerUnitsH2_subsingleton K L v hunram
  let e := relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
    (K := K) (L := L) v
  let i :
      Rep.ofMulDistribMulAction Gal(L / K)
          (relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v) ≅
        Rep.ofMulDistribMulAction Gal(L / K)
          (ChosenFinitePlaceInducedIntegerUnits (K := K) (L := L) v) :=
    Rep.mkIso (Representation.Equiv.mk e.toAdditive.toIntLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro x
      exact congrArg Additive.ofMul
        (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits_smul
          (K := K) (L := L) v g x.toMul)))
  let hi :
      groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
        (relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v)) 2 ≅
      groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
        (ChosenFinitePlaceInducedIntegerUnits (K := K) (L := L) v)) 2 :=
    (groupCohomology.functor ℤ Gal(L / K) 2).mapIso i
  exact Function.Injective.subsingleton hi.toLinearEquiv.injective

omit [NumberField L] in
/-- Every two-cocycle in the actual integral finite-place tensor block
admits a primitive which stays inside that integral block. -/
theorem unramifiedFinitePlaceIntegralBlockTwoCocycle_isCoboundary
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    ∀ c : groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction Gal(L / K)
      (relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v)),
      ∃ b : Gal(L / K) → Additive
          (relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v),
        (groupCohomology.d₁₂ (Rep.ofMulDistribMulAction Gal(L / K)
          (relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v))).hom b = c.1 := by
  let _ := unramifiedFinitePlaceIntegralBlockH2_subsingleton K L v hunram
  intro c
  exact (groupCohomology.H2π_eq_zero_iff c).1 (Subsingleton.elim _ _)

end ClassFieldTower.Martinet.Shafarevich
