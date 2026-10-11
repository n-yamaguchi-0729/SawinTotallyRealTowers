/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.KummerFiniteInertia
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicInertiaCentrality
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Absolute Galois centers over Henselian discrete valuations

For a Henselian discrete valuation field of residue characteristic zero
containing all p-power roots, a Kummer extension supplies nontrivial inertia
and hence a nonidentity element of the absolute Galois center.
-/

namespace ValuationTheory.DiscreteValuationField

open RamificationTheory.HilbertRamification.ValuationSubring

universe u v

/-- Over a residue-zero Henselian DVF containing all p-power roots, a cyclic
Kummer extension supplies finite nontrivial inertia; compactness then gives
a nonidentity element of the actual absolute Galois center. -/
theorem HenselianDVF.exists_ne_one_mem_absoluteGalois_center_of_all_primePowerRoots
    {K : Type u} [Field K] (D : HenselianDVF.{u, v} K)
    [CharZero D.residueField]
    (p : ℕ) [Fact p.Prime]
    (hroots : ∀ n : ℕ, ∃ ζ : K, IsPrimitiveRoot ζ (p ^ n)) :
    ∃ σ : Gal(AlgebraicClosure K/K),
      σ ∈ Subgroup.center Gal(AlgebraicClosure K/K) ∧ σ ≠ 1 := by
  have : CharZero K := by
    refine ⟨fun m n h => ?_⟩
    apply Nat.cast_injective (R := D.residueField)
    have hv : (m : D.valuation.valuationSubring) = n := Subtype.ext h
    have hr := congrArg (IsLocalRing.residue D.valuation.valuationSubring) hv
    simpa only [map_natCast] using hr
  obtain ⟨ζ, hζ⟩ := hroots 1
  rw [pow_one] at hζ
  obtain ⟨L, hL, hKL, hfd, T, hDT, hdeg, hGal, _hcyclic, hres⟩ :=
    D.exists_cyclic_kummer_extension_residueMap_surjective p ζ hζ
  let : Field L := hL
  let : Algebra K L := hKL
  let : FiniteDimensional K L := hfd
  let : IsGalois K L := hGal
  let : D.valuation.HasExtension T.valuation := hDT
  let Ω := AlgebraicClosure L
  have : IsAlgClosure K Ω :=
    ⟨inferInstance, Algebra.IsAlgebraic.trans K L Ω⟩
  obtain ⟨Γ, hΓ, z, hz⟩ := Valuation.chevalley_hasSomeExtensionTo (L := Ω) T.valuation
  let : LinearOrderedCommGroupWithZero Γ := hΓ
  let : T.valuation.HasExtension z := hz
  have : D.valuation.HasExtension z := Valuation.hasExtension_trans D.valuation T.valuation z
  have : CharZero (IsLocalRing.ResidueField z.valuationSubring) :=
    charZero_of_injective_algebraMap
      (algebraMap D.residueField (IsLocalRing.ResidueField z.valuationSubring)).injective
  have : D.valuation.valuationSubring.valuation.HasExtension z.valuationSubring.valuation := by
    apply _root_.Valuation.HasExtension.ofComapInteger
    ext a
    change z.valuationSubring.valuation (algebraMap K Ω a) ≤ 1 ↔
      D.valuation.valuationSubring.valuation a ≤ 1
    rw [_root_.ValuationSubring.valuation_le_one_iff,
      _root_.ValuationSubring.valuation_le_one_iff]
    exact _root_.Valuation.HasExtension.val_map_le_one_iff D.valuation z a
  obtain ⟨E, hEp, τ, hτ⟩ :=
    exists_finite_inertia_pGroup_of_prime_residue_trivial_extension D T z p hdeg hres
  obtain ⟨σ, hσc, hσ⟩ :=
    exists_ne_one_mem_center_of_finite_inertia_pGroup
      D.valuation.valuationSubring z.valuationSubring p hroots E hEp τ hτ
  let e : Gal(Ω/K) ≃* Gal(AlgebraicClosure K/K) :=
    AlgEquiv.autCongr (IsAlgClosure.equiv K Ω (AlgebraicClosure K))
  refine ⟨e σ, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff] at hσc ⊢
    intro g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hσc g]
  · intro h
    apply hσ
    apply e.injective
    exact h.trans e.map_one.symm

end ValuationTheory.DiscreteValuationField
