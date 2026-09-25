/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceSeparableEmbedding
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.LocalFiniteInertiaUnramified
import ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal

set_option autoImplicit false
/-!
# Finite Galois fields fixed by absolute inertia are unramified

Normality makes the image of the finite global field in the local separable
closure independent of its embedding. The actual decomposition comparison
therefore makes inertia fix every generator of its chosen finite localization.
The finite local inertia criterion and completion-to-ideal theorem then give
unramifiedness at every global finite prime.

Only the two canonical base-to-separable-closure instances from the embedding
leaf are reactivated. The three local proof instances (characteristic zero and
two field-algebra torsion-freeness proofs) resolve otherwise ambiguous synthesis
at `IsAlgClosed.lift`; no new data instance or alternative scalar tower is used.
-/

open NumberField IsDedekindDomain
open scoped NumberField ValuativeRel
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open AlgebraicNumberTheory.Valuations LocalClassFieldTheory LocalFieldTheory

private theorem fieldAlgebraTorsionFree
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Module.IsTorsionFree K L :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with hr | hx
    · exact Or.inl ((algebraMap K L).injective (by simpa using hr))
    · exact Or.inr hx

private def finiteFieldSeparableEmbedding
    (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : L →ₐ[K] SeparableClosure K := by
  letI : Module.IsTorsionFree K L := fieldAlgebraTorsionFree K L
  letI : Module.IsTorsionFree K (SeparableClosure K) :=
    fieldAlgebraTorsionFree K (SeparableClosure K)
  exact IsAlgClosed.lift

private theorem normal_algHom_range_eq
    {K E A : Type*} [Field K] [Field E] [Field A] [Algebra K E] [Algebra K A]
    [FiniteDimensional K E] [Normal K E] (f g : E →ₐ[K] A) : f.range = g.range := by
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField K E
  let _ := hp
  rw [← Polynomial.IsSplittingField.adjoin_rootSet_eq_range E p f,
    ← Polynomial.IsSplittingField.adjoin_rootSet_eq_range E p g]

private theorem normal_algHom_fixed_image
    {K E A : Type*} [Field K] [Field E] [Field A] [Algebra K E] [Algebra K A]
    [FiniteDimensional K E] [Normal K E] (f g : E →ₐ[K] A)
    (u : A → A) (hu : ∀ x : E, u (g x) = g x) (x : E) : u (f x) = f x := by
  have hx : f x ∈ g.range := (normal_algHom_range_eq f g) ▸ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  rw [← hy]
  exact hu y

attribute [local instance] finitePlaceSeparableEmbeddingBaseAlgebra
  finitePlaceSeparableEmbeddingBaseTower

variable (F : Type) [Field F] [NumberField F]
variable (M : IntermediateField F (AlgebraicClosure F))
  [FiniteDimensional F M] [IsGalois F M]
variable (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => AbsoluteValue.Completion (HeightOneSpectrum.adicAbv F v)
local notation "Loc" => ChosenFinitePlaceLocalizedCompletion (K := F) (L := M) v
local notation "wM" => chosenFinitePlaceExtension (L := M) v

/-- Absolute inertia fixing a finite normal global field forces its actual
chosen local extension to be unramified. -/
theorem chosenFinitePlaceIsUnramified_of_absoluteInertiaFixes
    (hM : ∀ tau : finitePlaceAbsoluteInertiaSubgroup F v,
      ∀ x : M, (tau.1.1 : Gal(AlgebraicClosure F/F)) (x : AlgebraicClosure F) = x) :
    ChosenFinitePlaceIsUnramified (K := F) (L := M) v := by
  let _ : CharZero Kv := charZero_of_injective_algebraMap (algebraMap F Kv).injective
  let : Algebra F (SeparableClosure Kv) := finitePlaceSeparableEmbeddingBaseAlgebra F v
  let : IsScalarTower F Kv (SeparableClosure Kv) := finitePlaceSeparableEmbeddingBaseTower F v
  let f : Loc →ₐ[Kv] SeparableClosure Kv := finiteFieldSeparableEmbedding Kv Loc
  let fM : M →ₐ[F] SeparableClosure Kv :=
    { toRingHom := f.toRingHom.comp
        (AbsoluteValue.toAlgebraicLocalization (HeightOneSpectrum.adicAbv F v) wM.1 wM.2)
      commutes' x := by
        change f (AbsoluteValue.toAlgebraicLocalization
          (HeightOneSpectrum.adicAbv F v) wM.1 wM.2 (algebraMap F M x)) = _
        rw [AbsoluteValue.toAlgebraicLocalization_algebraMap]
        exact f.commutes (algebraMap F Kv x) }
  let jM := (finitePlaceSeparableEmbedding F v).comp M.val
  apply localFiniteExtension_isUnramified_of_inertiaFixes Kv Loc f
  intro sigma hsigma x
  have hσM (y : M) : sigma (fM y) = fM y := by
    apply normal_algHom_fixed_image fM jM sigma _ y
    intro z
    have hsigma' : sigma ∈ Subgroup.map
        (finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
          F v).toMonoidHom (finitePlaceAbsoluteInertiaSubgroup F v) := by
      rw [finitePlaceAbsoluteInertia_map_eq_localResidueDegree_ker]
      exact hsigma
    obtain ⟨tau, htau, rfl⟩ := hsigma'
    change finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup F v tau
      (finitePlaceSeparableEmbedding F v z) = finitePlaceSeparableEmbedding F v z
    rw [finitePlaceSeparableEmbedding_equivariant, hM ⟨tau, htau⟩ z]
  have heq : sigma.toAlgHom.comp f = f := by
    apply IntermediateField.adjoin_algHom_ext
    intro z hz
    obtain ⟨y, rfl⟩ := hz
    exact hσM y
  exact DFunLike.congr_fun heq x

local instance finitePlaceInertiaFixedNumberField : NumberField M :=
  NumberField.of_module_finite F M

/-- If every selected absolute inertia fixes the finite Galois field, every
finite prime of that field is unramified over the base. -/
theorem finitePlacesUnramified_of_absoluteInertiaFixes
    (hM : ∀ v : HeightOneSpectrum (𝓞 F),
      ∀ tau : finitePlaceAbsoluteInertiaSubgroup F v,
      ∀ x : M, (tau.1.1 : Gal(AlgebraicClosure F/F)) (x : AlgebraicClosure F) = x)
    (P : HeightOneSpectrum (𝓞 M)) : Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal :=
  isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
    (finitePlaceBelow (K := F) P) P rfl
    (chosenFinitePlaceIsUnramified_of_absoluteInertiaFixes F M _ (hM _))

end ClassFieldTower.Martinet.Shafarevich
