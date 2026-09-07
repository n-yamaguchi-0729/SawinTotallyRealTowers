import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceInertiaTransport

set_option autoImplicit false
/-!
# The actual global-to-local separable-closure embedding

The chosen algebraic localization embeds the global algebraic closure into
the local separable closure. Its pointwise equivariance identifies the
actual action used by the decomposition-group comparison. Two canonical
scalar towers are each installed once; no valuation preservation is assumed.
-/

open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open AlgebraicNumberTheory.Valuations HilbertRamification

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => AbsoluteValue.Completion (HeightOneSpectrum.adicAbv F v)
local notation "w" => finitePlaceAbsoluteValueExtension F v

local instance finitePlaceSeparableEmbeddingBaseAlgebra : Algebra F (SeparableClosure Kv) :=
  Algebra.compHom (SeparableClosure Kv) (algebraMap F Kv)
local instance finitePlaceSeparableEmbeddingBaseTower : IsScalarTower F Kv (SeparableClosure Kv) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance finitePlaceSeparableEmbeddingAbsoluteAlgebra : Algebra F w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := F) w.1
local instance finitePlaceSeparableEmbeddingCompletionAlgebra : Algebra Kv w.1.Completion :=
  AbsoluteValue.completionAlgebra (HeightOneSpectrum.adicAbv F v) w.1 w.2

/-- The selected global algebraic closure inside the local separable closure. -/
def finitePlaceSeparableEmbedding : AlgebraicClosure F →ₐ[F] SeparableClosure Kv where
  toRingHom := (finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure F v).toRingHom.comp
    (AbsoluteValue.toAlgebraicLocalization (HeightOneSpectrum.adicAbv F v) w.1 w.2)
  commutes' x := by
    change (finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure F v)
      (AbsoluteValue.toAlgebraicLocalization (HeightOneSpectrum.adicAbv F v) w.1 w.2
        (algebraMap F (AlgebraicClosure F) x)) = _
    rw [AbsoluteValue.toAlgebraicLocalization_algebraMap]
    exact (finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure F v).commutes
      (algebraMap F Kv x)

/-- Pointwise compatibility with the actual decomposition-group comparison. -/
theorem finitePlaceSeparableEmbedding_equivariant
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) (x : AlgebraicClosure F) :
    finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup F v sigma
        (finitePlaceSeparableEmbedding F v x) =
      finitePlaceSeparableEmbedding F v (sigma.1 x) := by
  rw [finitePlaceDecompositionTransport_apply]
  change (AlgEquiv.autCongr (finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure F v)
    (decompositionGroupEquivAlgebraicLocalizationAut
      (HeightOneSpectrum.adicAbv F v) (RayClass.adicAbv_isNontrivial v) w sigma))
      ((finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure F v)
        (AbsoluteValue.toAlgebraicLocalization (HeightOneSpectrum.adicAbv F v) w.1 w.2 x)) = _
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  change (finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure F v)
    ((decompositionGroupToLocalization (HeightOneSpectrum.adicAbv F v)
      (RayClass.adicAbv_isNontrivial v) w sigma)
        (AbsoluteValue.toAlgebraicLocalization (HeightOneSpectrum.adicAbv F v) w.1 w.2 x)) = _
  rw [decompositionGroupToLocalization_toLocalization]
  rfl

end ClassFieldTower.Martinet.Shafarevich
