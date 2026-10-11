/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianDecomposition
import Nyll.ValuedFieldTheory.Valuation.ResidueAlgebraicClosedness
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Full residue Galois action over a Henselian valued field

Reduction acts on the actual residue-field algebra. Fixed integers descend to
the base field, identifying the scalars needed for residue surjectivity.
Finite residue bases lift to finitely many algebraic field elements, proving
Krull continuity. Reduction is an open quotient with the actual inertia kernel.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.ValuationSubring

open IsLocalRing

variable {K L Γ Δ : Type*} [Field K] [Field L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
  (v : _root_.Valuation K Γ) (w : _root_.Valuation L Δ) [v.HasExtension w]
  [IsGalois K L]
  [HenselianRing v.valuationSubring (maximalIdeal v.valuationSubring)]

omit [IsGalois K L] [HenselianRing v.valuationSubring (maximalIdeal v.valuationSubring)] in
private theorem canonical_hasExtension :
    v.valuationSubring.valuation.HasExtension w.valuationSubring.valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext a
  change w.valuationSubring.valuation (algebraMap K L a) ≤ 1 ↔
    v.valuationSubring.valuation a ≤ 1
  rw [_root_.ValuationSubring.valuation_le_one_iff,
    _root_.ValuationSubring.valuation_le_one_iff]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff v w a

/-- Over a Henselian base the full Galois group acts on the chosen valuation. -/
def henselianGalToDecomposition : Gal(L/K) →* decompositionGroup K w.valuationSubring where
  toFun σ := ⟨σ, by
    have := canonical_hasExtension v w
    rw [decompositionGroup_eq_top_of_henselianRing v.valuationSubring w.valuationSubring]
    exact Subgroup.mem_top σ⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The actual full residue action over the canonical residue-field algebra. -/
def henselianResidueAction : Gal(L/K) →*
    Gal(ResidueField w.valuationSubring / ResidueField v.valuationSubring) where
  toFun σ :=
    { residueAction K w.valuationSubring (henselianGalToDecomposition v w σ) with
      commutes' := by
        intro z
        obtain ⟨a, rfl⟩ := residue_surjective z
        rw [_root_.Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap]
        change residue w.valuationSubring
          ((henselianGalToDecomposition v w σ) •
            algebraMap v.valuationSubring w.valuationSubring a) =
          residue w.valuationSubring (algebraMap v.valuationSubring w.valuationSubring a)
        apply congrArg (residue w.valuationSubring)
        apply Subtype.ext
        exact σ.commutes (a : K) }
  map_one' := by
    apply AlgEquiv.ext
    intro z
    exact congrArg
      (fun f : ResidueField w.valuationSubring ≃+* ResidueField w.valuationSubring => f z)
      ((residueAction K w.valuationSubring).map_one)
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro z
    exact congrArg
      (fun f : ResidueField w.valuationSubring ≃+* ResidueField w.valuationSubring => f z)
      ((residueAction K w.valuationSubring).map_mul
        (henselianGalToDecomposition v w σ) (henselianGalToDecomposition v w τ))

@[simp] theorem henselianResidueAction_residue (σ : Gal(L/K)) (x : w.valuationSubring) :
    henselianResidueAction v w σ (residue w.valuationSubring x) =
      residue w.valuationSubring ((henselianGalToDecomposition v w σ) • x) := rfl

private theorem decompositionResidue_scalar_range_subset_base :
    Set.range (algebraMap (decompositionResidueField K w.valuationSubring)
      (ResidueField w.valuationSubring)) ⊆
      Set.range
        (algebraMap (ResidueField v.valuationSubring) (ResidueField w.valuationSubring)) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hfixed : ∀ σ : Gal(L/K), σ ((a : w.valuationSubring) : L) =
      ((a : w.valuationSubring) : L) := by
    intro σ
    exact congrArg (fun b : w.valuationSubring => (b : L))
      (a.property (henselianGalToDecomposition v w σ))
  obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    (k := K) ((a : w.valuationSubring) : L)).mpr hfixed
  have hbinteger : b ∈ v.valuationSubring := by
    apply (_root_.Valuation.HasExtension.val_map_le_one_iff v w b).mp
    rw [hb]
    exact (a : w.valuationSubring).property
  refine ⟨residue v.valuationSubring ⟨b, hbinteger⟩, ?_⟩
  rw [_root_.Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap]
  change residue w.valuationSubring (algebraMap v.valuationSubring w.valuationSubring
    ⟨b, hbinteger⟩) = residue w.valuationSubring (a : w.valuationSubring)
  apply congrArg (residue w.valuationSubring)
  exact Subtype.ext hb

/-- Every automorphism of the actual residue extension lifts to a field
Galois automorphism over a Henselian base. -/
theorem henselianResidueAction_surjective : Function.Surjective (henselianResidueAction v w) := by
  intro τ
  let e : Gal(ResidueField w.valuationSubring / decompositionResidueField K w.valuationSubring) :=
    { τ.toRingEquiv with
      commutes' := by
        intro z
        obtain ⟨x, hx⟩ := decompositionResidue_scalar_range_subset_base v w
          (Set.mem_range_self z)
        rw [← hx]
        exact τ.commutes x }
  obtain ⟨σ, hσ⟩ := decompositionGroupResidueAction_surjective (K := K) w.valuationSubring e
  refine ⟨σ.val, ?_⟩
  apply AlgEquiv.ext
  intro z
  exact congrArg (fun f : Gal(ResidueField w.valuationSubring /
    decompositionResidueField K w.valuationSubring) => f z) hσ

/-- The actual residue extension of an algebraic Galois extension of a
Henselian valued field is algebraic. -/
theorem henselianResidueExtension_isIntegral :
    Algebra.IsIntegral (ResidueField v.valuationSubring) (ResidueField w.valuationSubring) := by
  have := canonical_hasExtension v w
  have hring : w.valuationSubring.toSubring =
      (integralClosure v.valuationSubring L).toSubring := by
    simpa only [_root_.ValuationSubring.valuationSubring_valuation] using
      ValuationTheory.Henselian.valuationSubring_eq_integralClosure_of_henselianRing
        v.valuationSubring w.valuationSubring.valuation
  have : IsScalarTower v.valuationSubring (ResidueField v.valuationSubring)
      (ResidueField w.valuationSubring) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  constructor
  intro z
  obtain ⟨a, rfl⟩ := residue_surjective z
  have ha : IsIntegral v.valuationSubring (a : L) := by
    apply (mem_integralClosure_iff v.valuationSubring L).mp
    change (a : L) ∈ (integralClosure v.valuationSubring L).toSubring
    rw [← hring]
    exact a.property
  have ha' : IsIntegral v.valuationSubring a :=
    IsIntegral.tower_bot (show Function.Injective
      (algebraMap w.valuationSubring L) from Subtype.val_injective) ha
  have hr : IsIntegral v.valuationSubring (residue w.valuationSubring a) :=
    ha'.map (IsScalarTower.toAlgHom v.valuationSubring w.valuationSubring
      (ResidueField w.valuationSubring))
  exact hr.tower_top

/-- The chosen residue of an algebraic closure is an algebraic closure of the
actual base residue field. -/
theorem henselianResidueExtension_isAlgClosure [IsAlgClosed L] :
    IsAlgClosure (ResidueField v.valuationSubring) (ResidueField w.valuationSubring) := by
  have := henselianResidueExtension_isIntegral v w
  exact ⟨_root_.ValuationSubring.isAlgClosed_residueField w.valuationSubring, inferInstance⟩

/-- The actual residue action is continuous for the Krull topologies. -/
theorem henselianResidueAction_continuous : Continuous (henselianResidueAction v w) := by
  classical
  apply continuous_of_tendsto_nhds_one (henselianResidueAction v w)
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff
    (ResidueField v.valuationSubring) (ResidueField w.valuationSubring) U).mp hU
  have : FiniteDimensional (ResidueField v.valuationSubring) E := hE
  let b := Module.finBasis (ResidueField v.valuationSubring) E
  choose a ha using fun i => residue_surjective (R := w.valuationSubring)
    ((b i : E) : ResidueField w.valuationSubring)
  let S : Set L := Set.range (fun i => (a i : L))
  have : Finite S := (Set.finite_range (fun i => (a i : L))).to_subtype
  let B : IntermediateField K L := IntermediateField.adjoin K S
  have : FiniteDimensional K B := IntermediateField.finiteDimensional_adjoin
    (fun x _hx => Algebra.IsIntegral.isIntegral x)
  apply (krullTopology_mem_nhds_one_iff K L ((henselianResidueAction v w) ⁻¹' U)).mpr
  refine ⟨B, inferInstance, ?_⟩
  intro σ hσ
  apply hEU
  apply (IntermediateField.mem_fixingSubgroup_iff E (henselianResidueAction v w σ)).mpr
  intro z hz
  have hlin : (henselianResidueAction v w σ).toLinearMap.comp E.val.toLinearMap =
      E.val.toLinearMap := by
    apply b.ext
    intro i
    change henselianResidueAction v w σ ((b i : E) : ResidueField w.valuationSubring) =
      ((b i : E) : ResidueField w.valuationSubring)
    rw [← ha i, henselianResidueAction_residue]
    apply congrArg (residue w.valuationSubring)
    apply Subtype.ext
    exact (IntermediateField.mem_fixingSubgroup_iff B σ).mp hσ (a i : L)
      (IntermediateField.subset_adjoin K S (Set.mem_range_self i))
  exact LinearMap.congr_fun hlin ⟨z, hz⟩

/-- Full reduction, bundled as a continuous homomorphism. -/
def henselianResidueContinuousHom : Gal(L/K) →ₜ*
    Gal(ResidueField w.valuationSubring / ResidueField v.valuationSubring) :=
  ⟨henselianResidueAction v w, henselianResidueAction_continuous v w⟩

/-- The kernel of full reduction consists exactly of the actual inertia elements. -/
theorem henselianResidueAction_ker :
    (henselianResidueAction v w).ker =
      (inertiaGroup K w.valuationSubring).comap (henselianGalToDecomposition v w) := by
  ext σ
  change henselianResidueAction v w σ = 1 ↔
    residueAction K w.valuationSubring (henselianGalToDecomposition v w σ) = 1
  constructor
  · intro h
    exact congrArg AlgEquiv.toRingEquiv h
  · intro h
    apply AlgEquiv.ext
    intro z
    exact congrArg (fun f : ResidueField w.valuationSubring ≃+*
      ResidueField w.valuationSubring => f z) h

/-- The full residue action is an open quotient map. -/
theorem henselianResidueAction_isOpenQuotientMap :
    IsOpenQuotientMap (henselianResidueAction v w) := by
  have := henselianResidueExtension_isIntegral v w
  have : T2Space Gal(ResidueField w.valuationSubring / ResidueField v.valuationSubring) :=
    krullTopology_t2
  exact MonoidHom.isOpenQuotientMap_of_isQuotientMap
    (Topology.IsQuotientMap.of_surjective_continuous
      (henselianResidueAction_surjective v w) (henselianResidueAction_continuous v w))

end RamificationTheory.HilbertRamification.ValuationSubring
