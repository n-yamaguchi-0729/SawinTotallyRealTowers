/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.EtaleFieldPointBound
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Compactness.Compact


/-!
# A global uniform bound for field-valued points of an étale algebra

Compactness of the actual prime spectrum gives a finite family of the
previously constructed bounded principal charts. A map to a field has a
prime kernel, so one chart element maps to a unit and the map extends by
the existing localization lift. Restriction from the disjoint union of
chart hom sets is therefore surjective. Their finite cardinalities add,
giving one finite bound chosen before the target field and base map.

No nontriviality assumption on either algebra is required. Comparison with
scheme-theoretic geometric fibers remains a separate step toward 09Z0.
-/

noncomputable section

universe u v w

namespace Algebra.Etale

/-- An étale algebra has a single finite bound on its field-valued points,
uniform over all fields in the target universe and all base-ring maps. -/
theorem exists_uniform_fieldHom_bound
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Etale R S] :
    ∃ N : ℕ, ∀ (K : Type w) [Field K] [Algebra R K],
      Finite (S →ₐ[R] K) ∧ Nat.card (S →ₐ[R] K) ≤ N := by
  classical
  choose s hs N hN using fun p : PrimeSpectrum S =>
    exists_local_uniform_fieldHom_bound.{u, v, w} (R := R) p.asIdeal
  have hcover : (Set.univ : Set (PrimeSpectrum S)) ⊆
      ⋃ p : PrimeSpectrum S, (PrimeSpectrum.basicOpen (s p) : Set (PrimeSpectrum S)) := by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p, (PrimeSpectrum.mem_basicOpen (s p) p).mpr (hs p)⟩
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (PrimeSpectrum S))).elim_finite_subcover
      (fun p : PrimeSpectrum S => (PrimeSpectrum.basicOpen (s p) : Set (PrimeSpectrum S)))
      (fun p => (PrimeSpectrum.basicOpen (s p)).isOpen) hcover
  refine ⟨∑ p : t, N p, ?_⟩
  intro K _ _
  have : ∀ p : t, Finite (Localization.Away (s p) →ₐ[R] K) := fun p => (hN p K).1
  let ρ : (Σ p : t, Localization.Away (s p) →ₐ[R] K) → (S →ₐ[R] K) := fun a =>
    a.2.comp (IsScalarTower.toAlgHom R S (Localization.Away (s a.1)))
  have hρ : Function.Surjective ρ := by
    intro φ
    let p : PrimeSpectrum S := ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime φ.toRingHom⟩
    obtain ⟨j, hjt, hj⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
    have hunit : IsUnit (φ (s j)) :=
      isUnit_iff_ne_zero.mpr ((PrimeSpectrum.mem_basicOpen (s j) p).mp hj)
    let ψ : Localization.Away (s j) →ₐ[R] K :=
      IsLocalization.Away.liftAlgHom (s j) (f := φ) hunit
    refine ⟨⟨⟨j, hjt⟩, ψ⟩, ?_⟩
    apply AlgHom.ext
    intro x
    change IsLocalization.Away.lift (s j) (g := φ.toRingHom) hunit
      (algebraMap S (Localization.Away (s j)) x) = φ x
    exact IsLocalization.Away.lift_eq (s j) hunit x
  refine ⟨Finite.of_surjective ρ hρ, ?_⟩
  calc
    Nat.card (S →ₐ[R] K) ≤ Nat.card (Σ p : t, Localization.Away (s p) →ₐ[R] K) :=
      Nat.card_le_card_of_surjective ρ hρ
    _ = ∑ p : t, Nat.card (Localization.Away (s p) →ₐ[R] K) := Nat.card_sigma
    _ ≤ ∑ p : t, N p := Finset.sum_le_sum (fun p _ => (hN p K).2)

end Algebra.Etale
