import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceH1AdicRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1Transport
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceCompletionValuationCompatibility
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalUnramifiedArtinKummerRange
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ValuationSemilinear
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldLocalData

set_option autoImplicit false
/-!
# Inertia in the actual adic completion model

The canonical comparison of the two completions preserves their valuation
relations. Uniqueness of the separable-closure valuation and naturality of
residue degree therefore identify their inertia groups. This gives the exact
unramified-H¹ criterion for the actual decomposition-to-adic transport.
-/

open NumberField IsDedekindDomain LocalClassFieldTheory
open scoped NumberField Topology
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open ClassFieldTower.ProP

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

local notation "C" => AbsoluteValue.Completion (HeightOneSpectrum.adicAbv F v)
local notation "C'" => v.adicCompletion F
local instance finitePlaceAdicInertiaSourceCharZero : CharZero C :=
  charZero_of_injective_algebraMap (algebraMap F C).injective
local instance finitePlaceAdicInertiaSourceValuativeRel : ValuativeRel C :=
  GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
local instance finitePlaceAdicInertiaSourceLocalField : IsNonarchimedeanLocalField C :=
  GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
local instance finitePlaceAdicInertiaTargetValuativeRel : ValuativeRel C' :=
  finitePlaceAdicCompletionValuativeRel F v
local instance finitePlaceAdicInertiaTargetLocalField : IsNonarchimedeanLocalField C' :=
  finitePlaceAdicCompletionIsNonarchimedeanLocalField F v

/-- The completion comparison on separable closures, induced by the actual
algebraic-closure comparison. -/
def finitePlaceCompletionSeparableClosureRingEquiv :
    SeparableClosure C ≃+* SeparableClosure C' :=
  (algebraicClosureAlgEquivSeparableClosure C).symm.toRingEquiv.trans
    ((finitePlaceCompletionAlgebraicClosureRingEquiv F v).trans
      (algebraicClosureAlgEquivSeparableClosure C').toRingEquiv)

/-- The comparison extends the canonical comparison of completed base fields. -/
theorem finitePlaceCompletionSeparableClosureRingEquiv_algebraMap (x : C) :
    finitePlaceCompletionSeparableClosureRingEquiv F v (algebraMap C (SeparableClosure C) x) =
      algebraMap C' (SeparableClosure C') (relativeFinitePlaceCompletionAlgEquiv v x) := by
  change algebraicClosureAlgEquivSeparableClosure C'
    (finitePlaceCompletionAlgebraicClosureRingEquiv F v
      ((algebraicClosureAlgEquivSeparableClosure C).symm
        (algebraMap C (SeparableClosure C) x))) = _
  rw [AlgEquiv.commutes, finitePlaceCompletionAlgebraicClosureRingEquiv_algebraMap,
    AlgEquiv.commutes]

/-- Restricting semilinear conjugation to the separable parts commutes with
the standard absolute-Galois comparison. -/
theorem finitePlaceCompletionSeparableGalois_conjugation
    (sigma : Field.absoluteGaloisGroup C) :
    LocalClassFieldTheory.semilinearGaloisGroupCongr C C'
      (SeparableClosure C) (SeparableClosure C')
      (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
      (finitePlaceCompletionSeparableClosureRingEquiv F v)
      (finitePlaceCompletionSeparableClosureRingEquiv_algebraMap F v)
      (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv C sigma) =
    RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv C'
      (finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv F v sigma) := by
  ext x
  rfl

/-- The actual comparison of completion models preserves residue degree. -/
theorem finitePlaceCompletionResidueDegree_conjugation
    (sigma : Field.absoluteGaloisGroup C) :
    localResidueDegree C'
      (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv C'
        (finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv F v sigma)) =
    localResidueDegree C
      (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv C sigma) := by
  rw [← finitePlaceCompletionSeparableGalois_conjugation]
  exact localResidueDegree_semilinear_conjugation C C'
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
    (finitePlaceCompletionSeparableClosureRingEquiv F v)
    (finitePlaceCompletionSeparableClosureRingEquiv_algebraMap F v)
    (localSeparableValuationSubring_comap_semilinear C C'
      (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
      (finitePlaceCompletionSeparableClosureRingEquiv F v)
      (finitePlaceCompletionSeparableClosureRingEquiv_algebraMap F v)
      (finitePlaceCompletion_semilinearValuationCompatible F v)) _

/-- Actual finite-place inertia is precisely intrinsic adic inertia. -/
theorem finitePlaceDecompositionAdic_mem_inertia_iff
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv C'
        (finitePlaceDecompositionAdicContinuousMulEquiv F v sigma) ∈
      localIntrinsicInertiaSubgroup C' ↔
    sigma ∈ finitePlaceAbsoluteInertiaSubgroup F v := by
  change localResidueDegree C'
    (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv C'
      (finitePlaceCompletionAbsoluteGaloisContinuousMulEquiv F v
        (finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v sigma))) = 1 ↔ _
  rw [finitePlaceCompletionResidueDegree_conjugation]
  change finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup F v sigma ∈
    MonoidHom.ker (localResidueDegree C).toMonoidHom ↔ _
  rw [localResidueDegree_ker_eq_valuationInertiaGroupInAut]
  exact finitePlaceDecompositionTransport_mem_inertia_iff F v sigma

variable (n : ℕ+) [Fact (n : ℕ).Prime]
local instance finitePlaceAdicInertiaCoefficientTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance finitePlaceAdicInertiaCoefficientDiscrete : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _
local instance finitePlaceAdicInertiaH1Module
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (n : ℕ)) (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) := continuousH1ZModModule

/-- The actual adic H¹ transport preserves and reflects unramified characters. -/
theorem finitePlaceDecompositionH1ToAdic_mem_unramified_iff
    (chi : ContinuousH1ZMod (p := (n : ℕ)) (G := finitePlaceAbsoluteDecompositionGroup F v)) :
    finitePlaceDecompositionH1ToAdic F (n : ℕ) v chi ∈ localStandardUnramifiedH1 C' n ↔
      chi ∈ finitePlaceUnramifiedH1 F (n : ℕ) v := by
  let e := (finitePlaceDecompositionAdicContinuousMulEquiv F v).trans
    (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv C')
  have hm (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
      e sigma ∈ localIntrinsicInertiaSubgroup C' ↔
        sigma ∈ finitePlaceAbsoluteInertiaSubgroup F v :=
    finitePlaceDecompositionAdic_mem_inertia_iff F v sigma
  change localIntrinsicH1InertiaRestriction C' (n : ℕ)
    (localStandardH1LinearEquivSeparable (n : ℕ) C'
      (finitePlaceDecompositionH1ToAdic F (n : ℕ) v chi)) = 0 ↔
    finitePlaceH1InertiaRestriction F (n : ℕ) v chi = 0
  constructor
  · intro h
    ext sigma
    have hv := DFunLike.congr_fun h (Additive.ofMul
      (⟨e sigma.toMul.val, (hm sigma.toMul.val).2 sigma.toMul.property⟩ :
        localIntrinsicInertiaSubgroup C'))
    change chi (Additive.ofMul (e.symm (e sigma.toMul.val))) = 0 at hv
    change chi (Additive.ofMul sigma.toMul.val) = 0
    simpa only [ContinuousMulEquiv.symm_apply_apply] using hv
  · intro h
    ext tau
    have hv := DFunLike.congr_fun h (Additive.ofMul
      (⟨e.symm tau.toMul.val, (hm (e.symm tau.toMul.val)).1 (by
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact tau.toMul.property)⟩ : finitePlaceAbsoluteInertiaSubgroup F v))
    exact hv

end ClassFieldTower.Martinet.Shafarevich
