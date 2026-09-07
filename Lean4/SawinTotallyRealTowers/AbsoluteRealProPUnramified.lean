import SawinTotallyRealTowers.AbsoluteRealProPRestriction
import SawinTotallyRealTowers.AbsoluteRealKernelField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.FinitePlaceAbsoluteInertiaKernel
import ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.CompositumUnramified
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

set_option autoImplicit false

/-!
# Ramification killed by the maximal real pro-p restriction

Absolute inertia outside the allowed support fixes every admissible finite
layer, hence their compositum. Real Artin conjugation fixes that compositum
because every complex embedding of it is real.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich AlgebraicNumberTheory.Valuations
open GlobalClassFieldTheory.Reciprocity

private theorem finiteInertia_fixes_layer
    (F : Type) [Field F] [NumberField F]
    (M : FiniteGaloisIntermediateField F (AlgebraicClosure F)) [NumberField M]
    (T : Set (HeightOneSpectrum (𝓞 F)))
    (hM : IsUnramifiedAtFinitePlacesOutside F M T)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T)
    (σ : finitePlaceAbsoluteInertiaSubgroup F v) :
    (σ.1.1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ∈
      M.toIntermediateField.fixingSubgroup := by
  have : IsGalois F M.toIntermediateField := M.isGalois
  let s : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := σ.1.1
  let wM := restrictAbsoluteValueExtensionToIntermediate
    (HeightOneSpectrum.adicAbv F v) (finitePlaceAbsoluteValueExtension F v) M.toIntermediateField
  let P := finitePlaceExtensionCentre (K := F) (L := M) v wM
  have hmem : s.restrictNormal M ∈
      HilbertRamification.Dedekind.inertiaGroup P.asIdeal (M ≃ₐ[F] M) :=
    finitePlaceAbsoluteInertia_restrictNormal_mem_finiteInertia F M.toIntermediateField v σ
  have hBelow : finitePlaceBelow (K := F) P = v :=
    finitePlaceBelow_finitePlaceExtensionCentre (K := F) (L := M) v wM
  have hUnramified : Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := hM P (hBelow ▸ hv)
  have hbot : HilbertRamification.Dedekind.inertiaGroup P.asIdeal (M ≃ₐ[F] M) = ⊥ :=
    HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_isUnramifiedAt
      (K := F) (M := M) P.asIdeal hUnramified
  rw [← IntermediateField.restrictNormalHom_ker M.toIntermediateField, MonoidHom.mem_ker]
  exact Subgroup.mem_bot.mp (hbot ▸ hmem)

/-- The actual maximal real restriction kills finite inertia outside the support. -/
theorem absoluteToMaximalRealProPOutside_inertia (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v ∉ T) (σ : finitePlaceAbsoluteInertiaSubgroup ℚ v) :
    absoluteToMaximalRealProPOutside p T
      (finitePlaceAbsoluteDecompositionInclusion ℚ v σ.1) = 1 := by
  let s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := σ.1.1
  have hmax : maximalRealProPOutside p T ≤ IntermediateField.fixedField (Subgroup.zpowers s) := by
    apply iSup_le
    intro E
    have : NumberField E.val := NumberField.of_module_finite ℚ E.val
    rw [IntermediateField.le_iff_le, Subgroup.zpowers_le]
    exact finiteInertia_fixes_layer ℚ E.val T E.property.2.1 v hv σ
  have hfix : Subgroup.zpowers s ≤ (maximalRealProPOutside p T).fixingSubgroup :=
    (IntermediateField.le_iff_le _ _).mp hmax
  change s ∈ (absoluteToMaximalRealProPOutside p T).toMonoidHom.ker
  rw [absoluteToMaximalRealProPOutside_ker]
  exact hfix (Subgroup.mem_zpowers s)

private theorem infiniteArtin_fixes_totallyReal
    (F : Type) [Field F] [CharZero F] (M : IntermediateField F (AlgebraicClosure F))
    [IsTotallyReal M] (v : InfinitePlace F) (x : M) :
    (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from absoluteInfinitePlaceArtinNegOne F v)
      (x : AlgebraicClosure F) = (x : AlgebraicClosure F) := by
  let w : InfinitePlace (AlgebraicClosure F) :=
    chosenInfinitePlaceAbove (L := AlgebraicClosure F) v
  let c : Gal(AlgebraicClosure F/F) :=
    chosenInfinitePlaceArtinMonoidHom (K := F) (L := AlgebraicClosure F) v (-1 : v.Completionˣ)
  change c (x : AlgebraicClosure F) = (x : AlgebraicClosure F)
  by_cases hw : w.IsUnramified F
  · have hc : c = 1 := by
      change (infinitePlaceArtinMonoidHomOfPlace (K := F) (L := AlgebraicClosure F)
        v w (chosenInfinitePlaceAbove_comap (L := AlgebraicClosure F) v)) (-1) = 1
      simp only [infinitePlaceArtinMonoidHomOfPlace, dif_pos hw, MonoidHom.one_apply]
    rw [hc]
    rfl
  · have hConj : ComplexEmbedding.IsConj w.embedding c :=
      chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
        (K := F) (L := AlgebraicClosure F) v hw
    have hReal : ComplexEmbedding.IsReal (w.embedding.comp (algebraMap M (AlgebraicClosure F))) :=
      IsTotallyReal.complexEmbedding_isReal _
    apply w.embedding.injective
    exact (hConj.eq (x : AlgebraicClosure F)).trans
      (RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hReal) x)

/-- Real Artin negative-one elements act trivially on the actual totally real compositum. -/
theorem absoluteToMaximalRealProPOutside_infiniteArtin (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) (v : InfinitePlace ℚ) :
    absoluteToMaximalRealProPOutside p T (absoluteInfinitePlaceArtinNegOne ℚ v) = 1 := by
  have : IsTotallyReal (maximalRealProPOutside p T) := maximalRealProPOutside_isTotallyReal p T
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [absoluteToMaximalRealProPOutside_apply]
  exact infiniteArtin_fixes_totallyReal ℚ (maximalRealProPOutside p T) v x

end ClassFieldTower.Sawin
