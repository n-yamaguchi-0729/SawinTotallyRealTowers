/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianResidueAction
import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionHenselian
import Nyll.ValuedFieldTheory.Valuation.Henselian.RootsOfUnity
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Lifting residue roots of unity in one finite field extension

Over a Henselian valued field of residue characteristic zero, a fixed finite
residue extension determines one finite intermediate field in which its primitive
roots of unity lift for every positive order. The field is constructed from the
residue Galois stabilizer.
-/

namespace ValuationTheory.Henselian

open IsLocalRing
open RamificationTheory.HilbertRamification.ValuationSubring

universe u v t w x

/-- Every root of unity in a fixed finite residue extension lifts into one finite
field extension. The field is the fixed field of the inverse image of its
residue Galois stabilizer; it works simultaneously for all positive orders. -/
theorem exists_finiteIntermediateField_lifting_residue_roots
    {K : Type u} {Ω : Type v} [Field K] [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω]
    {Γ : Type w} {Δ : Type x}
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    (v : Valuation K Γ) (w : Valuation Ω Δ) [v.HasExtension w]
    [HenselianRing v.valuationSubring (maximalIdeal v.valuationSubring)]
    [CharZero (ResidueField v.valuationSubring)]
    (E : Type t) [Field E] [Algebra (ResidueField v.valuationSubring) E]
    [FiniteDimensional (ResidueField v.valuationSubring) E] :
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
      ∀ (n : ℕ), 0 < n → (∃ ζ : E, IsPrimitiveRoot ζ n) →
        ∃ ζ : F, IsPrimitiveRoot ζ n := by
  classical
  have : CharZero K := by
    refine ⟨fun m n h => ?_⟩
    apply Nat.cast_injective (R := ResidueField v.valuationSubring)
    have hv : (m : v.valuationSubring) = n := Subtype.ext h
    have hr := congrArg (residue v.valuationSubring) hv
    simpa only [map_natCast] using hr
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : IsAlgClosure (ResidueField v.valuationSubring)
      (ResidueField w.valuationSubring) := henselianResidueExtension_isAlgClosure v w
  have : IsAlgClosed (ResidueField w.valuationSubring) :=
    IsAlgClosure.isAlgClosed (ResidueField v.valuationSubring)
  have : CharZero (ResidueField w.valuationSubring) :=
    charZero_of_injective_algebraMap
      (algebraMap (ResidueField v.valuationSubring) (ResidueField w.valuationSubring)).injective
  have hcanonical :
      v.valuationSubring.valuation.HasExtension w.valuationSubring.valuation := by
    apply Valuation.HasExtension.ofComapInteger
    ext a
    change w.valuationSubring.valuation (algebraMap K Ω a) ≤ 1 ↔
      v.valuationSubring.valuation a ≤ 1
    rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
    exact Valuation.HasExtension.val_map_le_one_iff v w a
  have : HenselianRing w.valuationSubring (maximalIdeal w.valuationSubring) :=
    henselianRing_of_algebraic_extension v.valuationSubring w.valuationSubring
  let j : E →ₐ[ResidueField v.valuationSubring] ResidueField w.valuationSubring :=
    IsAlgClosed.lift
  have : FiniteDimensional (ResidueField v.valuationSubring) j.fieldRange :=
    Module.Finite.equiv j.equivFieldRange.toLinearEquiv
  let U : OpenSubgroup
      Gal(ResidueField w.valuationSubring / ResidueField v.valuationSubring) :=
    ⟨j.fieldRange.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen _⟩
  let H : OpenSubgroup Gal(Ω/K) := U.comap (henselianResidueAction v w)
    (henselianResidueAction_continuous v w)
  let F : IntermediateField K Ω := IntermediateField.fixedField (H : Subgroup Gal(Ω/K))
  have hfix : F.fixingSubgroup = (H : Subgroup Gal(Ω/K)) :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨H.toSubgroup, H.isClosed⟩ : ClosedSubgroup Gal(Ω/K))
  have hfd : FiniteDimensional K F := (InfiniteGalois.isOpen_iff_finite F).mp
    (by rw [hfix]; exact H.isOpen)
  refine ⟨F, hfd, ?_⟩
  intro n hn ⟨ζ, hζ⟩
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (n : ResidueField w.valuationSubring) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  let r : rootsOfUnity n (ResidueField w.valuationSubring) :=
    rootsOfUnity.mkOfPowEq (j ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  obtain ⟨a, ha⟩ := ValuationSubring.rootsOfUnityReduction_surjective w.valuationSubring n r
  let b : w.valuationSubring := ((a : w.valuationSubringˣ) : w.valuationSubring)
  have hbpow : b ^ n = 1 := (mem_rootsOfUnity' n (a : w.valuationSubringˣ)).mp a.property
  have hbres : residue w.valuationSubring b = j ζ :=
    congrArg (fun z : rootsOfUnity n (ResidueField w.valuationSubring) =>
      ((z : (ResidueField w.valuationSubring)ˣ) : ResidueField w.valuationSubring)) ha
  have hbfix : ∀ σ ∈ (H : Subgroup Gal(Ω/K)), σ (b : Ω) = (b : Ω) := by
    intro σ hσ
    let g : decompositionGroup K w.valuationSubring := henselianGalToDecomposition v w σ
    let c : w.valuationSubring := g • b
    have hcpow : c ^ n = 1 := by
      apply Subtype.ext
      change (σ (b : Ω)) ^ n = 1
      rw [← map_pow, show (b : Ω) ^ n = 1 from
        congrArg (fun z : w.valuationSubring => (z : Ω)) hbpow, map_one]
    have hcres : residue w.valuationSubring c = residue w.valuationSubring b := by
      change henselianResidueAction v w σ (residue w.valuationSubring b) = _
      rw [hbres]
      exact (IntermediateField.mem_fixingSubgroup_iff j.fieldRange _).mp hσ _ ⟨ζ, rfl⟩
    have hca : rootsOfUnity.mkOfPowEq c hcpow = a := by
      apply ValuationSubring.rootsOfUnityReduction_injective w.valuationSubring n
      apply rootsOfUnity.coe_injective
      exact hcres
    exact congrArg (fun z : rootsOfUnity n w.valuationSubring =>
      (((z : w.valuationSubringˣ) : w.valuationSubring) : Ω)) hca
  let η : F := ⟨(b : Ω), by
    intro σ
    exact hbfix σ σ.property⟩
  refine ⟨η, ?_⟩
  constructor
  · apply Subtype.ext
    exact congrArg (fun z : w.valuationSubring => (z : Ω)) hbpow
  · intro m hm
    apply hζ.dvd_of_pow_eq_one m
    apply j.injective
    change j (ζ ^ m) = j 1
    rw [map_pow, map_one, ← hbres, ← map_pow]
    have hbm : b ^ m = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : F => (z : Ω)) hm
    rw [hbm, map_one]

end ValuationTheory.Henselian
