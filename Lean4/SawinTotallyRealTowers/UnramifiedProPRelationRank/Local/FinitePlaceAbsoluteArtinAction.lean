import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.LocalAbsoluteArtinEmbedding
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Conjugation

set_option autoImplicit false
/-!
# Absolute Artin action on a global finite abelian extension

Pulling the valuation back through the actual embedding and extending that
embedding to its localization relates the two Artin actions.  Independence of
the place above the base removes the auxiliary pullback place.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations
open GlobalClassFieldTheory.Reciprocity LocalClassFieldTheory HilbertRamification

variable (F L : Type) [Field F] [NumberField F]
  [Field L] [Algebra F L] [FiniteDimensional F L] [IsAbelianGalois F L]

/-- The local Artin action intertwines with the global action on localization. -/
theorem finitePlaceLocalArtin_toAlgebraicLocalization
    (v : HeightOneSpectrum (RingOfIntegers F))
    (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv F v) L)
    (a : (v.adicCompletion F)ˣ) (z : L) :
    finitePlaceLocalArtinMonoidHom (K := F) (L := L) v w a
        (AbsoluteValue.toAlgebraicLocalization
          (NumberField.HeightOneSpectrum.adicAbv F v) w.1 w.2 z) =
      AbsoluteValue.toAlgebraicLocalization
        (NumberField.HeightOneSpectrum.adicAbv F v) w.1 w.2
        (finitePlaceArtinMonoidHomOfExtension (K := F) (L := L) v w a z) := by
  let C := (NumberField.HeightOneSpectrum.adicAbv F v).Completion
  let E := LocalizedCompletion (NumberField.HeightOneSpectrum.adicAbv F v) w
  let _ : Algebra C E := finitePlaceLocalArtinLocalizedAlgebra v w
  let eD : absoluteValueDecompositionGroup F w.1 ≃* Gal(E/C) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      (NumberField.HeightOneSpectrum.adicAbv F v) (RayClass.adicAbv_isNontrivial v) w
  let sigma := finitePlaceLocalArtinMonoidHom (K := F) (L := L) v w a
  have h := localizationRamificationGroups_decompositionGroupEquiv_toLocalization
    (NumberField.HeightOneSpectrum.adicAbv F v) (RayClass.adicAbv_isNontrivial v)
    w (eD.symm sigma) z
  change eD (eD.symm sigma) _ = _ at h
  rw [eD.apply_symm_apply] at h
  exact h

variable (v : HeightOneSpectrum (RingOfIntegers F))

local instance finitePlaceAbsoluteArtinActionValuativeRel :
    ValuativeRel (NumberField.HeightOneSpectrum.adicAbv F v).Completion :=
  finitePlaceLocalArtinCompletionValuativeRel v

local instance finitePlaceAbsoluteArtinActionLocalField :
    IsNonarchimedeanLocalField (NumberField.HeightOneSpectrum.adicAbv F v).Completion :=
  finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v

/-- Every absolute Artin representative acts through the actual global
finite-place Artin map on an embedded finite abelian extension. -/
theorem finitePlaceAbsoluteArtin_lift_action
    (i : L →ₐ[F] AlgebraicClosure
      (NumberField.HeightOneSpectrum.adicAbv F v).Completion)
    (a : (v.adicCompletion F)ˣ)
    (sigma : Gal(AlgebraicClosure
      (NumberField.HeightOneSpectrum.adicAbv F v).Completion /
      (NumberField.HeightOneSpectrum.adicAbv F v).Completion))
    (hsigma : (QuotientGroup.mk
        (show Field.absoluteGaloisGroup
          (NumberField.HeightOneSpectrum.adicAbv F v).Completion from sigma) :
        Field.absoluteGaloisGroupAbelianization
          (NumberField.HeightOneSpectrum.adicAbv F v).Completion) =
      absoluteLocalArtinMap (NumberField.HeightOneSpectrum.adicAbv F v).Completion
        (finitePlaceLocalArtinInput v a)) (z : L) :
    sigma (i z) = i (chosenFinitePlaceArtinMonoidHom (K := F) (L := L) v a z) := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hv := RayClass.adicAbv_isNontrivial v
  let w : AbsoluteValueExtension vF L :=
    ⟨absoluteValueExtension_pullback vF hv i,
      absoluteValueExtension_pullback_extends vF hv i⟩
  let C := vF.Completion
  let E := LocalizedCompletion vF w
  let _ : Algebra C E := finitePlaceLocalArtinLocalizedAlgebra v w
  let _ : FiniteDimensional C E := finitePlaceLocalArtinFiniteDimensional v w
  let _ : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois v w (inferInstance : FiniteDimensional F L)
  let j : E →ₐ[C] AlgebraicClosure C :=
    absoluteValueExtension_localizationEmbeddingOfPullback vF hv w i rfl
  have hj (x : L) :
      j (AbsoluteValue.toAlgebraicLocalization vF w.1 w.2 x) = i x :=
    absoluteValueExtension_localizationEmbeddingOfPullback_toLocalization
      vF hv w i rfl x
  have h := absoluteLocalArtinMap_lift_action C E j (finitePlaceLocalArtinInput v a)
    sigma hsigma (AbsoluteValue.toAlgebraicLocalization vF w.1 w.2 z)
  have haction := (congrArg sigma (hj z)).symm.trans h
  have hlocal := finitePlaceLocalArtinMonoidHom_apply_normalized_at
    (K := F) (L := L) v w a
    (AbsoluteValue.toAlgebraicLocalization vF w.1 w.2 z)
  have hplace : finitePlaceArtinMonoidHomOfExtension (K := F) (L := L) v w a z =
      chosenFinitePlaceArtinMonoidHom (K := F) (L := L) v a z :=
    congrArg (fun f : (v.adicCompletion F)ˣ →* Gal(L/F) => f a z)
      (finitePlaceArtinMonoidHomOfExtension_eq v w
        (chosenFinitePlaceExtension (L := L) v))
  have hlocalization := hlocal.symm.trans
    (finitePlaceLocalArtin_toAlgebraicLocalization F L v w a z)
  have hglobal := (congrArg j hlocalization).trans
    (hj (finitePlaceArtinMonoidHomOfExtension (K := F) (L := L) v w a z))
  exact haction.trans (hglobal.trans (congrArg i hplace))

end ClassFieldTower.Martinet.Shafarevich
