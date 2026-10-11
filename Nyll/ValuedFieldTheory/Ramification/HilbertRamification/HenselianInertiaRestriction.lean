/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.BaseChange
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianDecomposition
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianResidueScalars
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence
import Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction
import Nyll.ValuedFieldTheory.Valuation.UniqueRing
import Mathlib.FieldTheory.Normal.Basic

/-!
# Surjectivity of inertia restriction over a Henselian valuation ring

A lift of an inertial automorphism fixes the actual residue scalars from the
intermediate field. The scalar-image comparison turns its residue action into
an automorphism over the base of the decomposition residue exact sequence.
Lifting that residue action over the intermediate field supplies a correction
which makes the original lift inertial without changing its restriction.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Restriction of the actual inertia groups is surjective over a Henselian
base. The intermediate extension need only be normal; in particular this
applies to every finite Galois intermediate field. -/
theorem galoisPullback_inertiaGroupMap_surjective_of_henselianRing
    [IsGalois K L]
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation]
    (E : IntermediateField K L) [Normal K E] :
    Function.Surjective
      (_root_.HilbertRamification.ValuationSubring.galoisPullback_inertiaGroupMap
        (RingHom.id K) E.val.toRingHom
        (by
          apply RingHom.ext
          intro a
          exact E.val.commutes a) A) := by
  intro τ
  let B : _root_.ValuationSubring E := A.comap E.val.toRingHom
  have hE : B.valuation.HasExtension A.valuation :=
    intermediateFieldComap_hasExtension A E
  let τ₀ : E ≃ₐ[K] E := inertiaGroupToAut (K := K) B τ
  let σ₀ : L ≃ₐ[K] L := τ₀.liftNormal L
  have hσ₀ : σ₀ ∈ decompositionGroup K A := by
    rw [decompositionGroup_eq_top_of_henselianRing V A]
    exact Subgroup.mem_top σ₀
  let σ : decompositionGroup K A := ⟨σ₀, hσ₀⟩
  let s : selectedResidueField A ≃+* selectedResidueField A := residueAction K A σ
  let f : B →+* A :=
    ValuationTheory.Valuations.valuationSubringMapOfHasExtension B A hE
  let r : IsLocalRing.ResidueField B →+* selectedResidueField A :=
    ValuationTheory.Valuations.residueFieldMapOfHasExtension B A hE
  have hr (b : B) : r (IsLocalRing.residue B b) = IsLocalRing.residue A (f b) :=
    AlgebraicNumberTheory.Valuations.residueFieldMapOfHasExtension_residue B A hE b
  have hfixed (y : IsLocalRing.ResidueField B) :
      s (r y) = r y := by
    obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective y
    rw [← hb, hr]
    let σA : A ≃+* A := MulSemiringAction.toRingAut (decompositionGroup K A) A σ
    let τB : B ≃+* B :=
      MulSemiringAction.toRingAut (decompositionGroup K B) B τ.val
    change IsLocalRing.residue A (σA (f b)) = IsLocalRing.residue A (f b)
    have hi : σA (f b) = f (τB b) := by
      apply Subtype.ext
      change σ₀ (algebraMap E L (b : E)) = algebraMap E L (τ₀ (b : E))
      exact τ₀.liftNormal_commutes L (b : E)
    have hbres := congrArg
      (fun φ : IsLocalRing.ResidueField B ≃+* IsLocalRing.ResidueField B =>
        φ (IsLocalRing.residue B b)) τ.property
    change IsLocalRing.residue B (τB b) = IsLocalRing.residue B b at hbres
    exact (congrArg (IsLocalRing.residue A) hi).trans
      ((hr (τB b)).symm.trans ((congrArg r hbres).trans (hr b)))
  let i : decompositionResidueField E A →+* selectedResidueField A :=
    algebraMap (decompositionResidueField E A) (selectedResidueField A)
  have hscalar (x : decompositionResidueField E A) : s (i x) = i x := by
    obtain ⟨y, hy⟩ :=
      (decompositionResidue_scalar_range_eq_comap_residueMap_of_henselianRing V A E).le
        (Set.mem_range_self x)
    exact (congrArg s hy.symm).trans ((hfixed y).trans hy)
  let e : selectedResidueField A ≃ₐ[decompositionResidueField E A] selectedResidueField A :=
    { s with commutes' := hscalar }
  obtain ⟨ρ, hρ⟩ := decompositionGroupResidueAction_surjective (K := E) A e
  let ρK : decompositionGroup K A :=
    decompositionGroupRestrictScalars (K := K) (M := E) A ρ
  have hρKres : residueAction K A ρK = s := by
    apply RingEquiv.ext
    intro y
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective y
    rw [← ha]
    exact congrArg
      (fun φ : selectedResidueField A ≃ₐ[decompositionResidueField E A]
        selectedResidueField A => φ (IsLocalRing.residue A a)) hρ
  have hδ : σ * ρK⁻¹ ∈ inertiaGroup K A := by
    change residueAction K A (σ * ρK⁻¹) = 1
    rw [(residueAction K A).map_mul σ ρK⁻¹,
      map_inv (residueAction K A) ρK, hρKres, mul_inv_cancel]
  let δ : inertiaGroup K A := ⟨σ * ρK⁻¹, hδ⟩
  refine ⟨δ, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply E.val.injective
  have hsquare : E.val.toRingHom.comp (algebraMap K E) =
      (algebraMap K L).comp (RingHom.id K) := by
    apply RingHom.ext
    intro a
    exact E.val.commutes a
  change E.val.toRingHom
      ((_root_.HilbertRamification.galoisPullback_galoisPullback
        (RingHom.id K) E.val.toRingHom hsquare (inertiaGroupToAut (K := K) A δ)) x) =
    E.val.toRingHom (τ₀ x)
  rw [_root_.HilbertRamification.galoisPullback_galoisPullback_commutes]
  change σ₀ (ρ.val.symm (algebraMap E L x)) = algebraMap E L (τ₀ x)
  rw [ρ.val.symm.commutes x]
  exact τ₀.liftNormal_commutes L x

end RamificationTheory.HilbertRamification.ValuationSubring
