/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.KummerResidue
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianResidueAction
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.BaseChange
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.GroupTheory.PGroup

/-!
# Nontrivial inertia from prime-degree residue-trivial extensions

A selected valuation above a prime-degree Galois extension with unchanged
residue field yields a nontrivial finite inertia p-group.
-/

namespace ValuationTheory.DiscreteValuationField

open RamificationTheory.HilbertRamification.ValuationSubring

universe u v w t

/-- A prime-degree extension with unchanged residue field gives a nontrivial
p-group inertia layer inside every selected overfield valuation. -/
theorem exists_finite_inertia_pGroup_of_prime_residue_trivial_extension
    {K L Ω : Type u} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    [FiniteDimensional K L] [IsGalois K L]
    (D : HenselianDVF.{u, v} K) (T : HenselianDVF.{u, w} L)
    [D.valuation.HasExtension T.valuation]
    {Γ : Type t} [LinearOrderedCommGroupWithZero Γ]
    (z : Valuation Ω Γ) [T.valuation.HasExtension z]
    (p : ℕ) [Fact p.Prime] (hdegree : Module.finrank K L = p)
    (hres : Function.Surjective (algebraMap D.residueField T.residueField)) :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      IsPGroup p (inertiaGroup K (z.valuationSubring.comap E.toIntermediateField.val.toRingHom)) ∧
      ∃ τ : inertiaGroup K (z.valuationSubring.comap E.toIntermediateField.val.toRingHom),
        τ ≠ 1 := by
  classical
  have hcardL : Nat.card Gal(L/K) = p := (IsGalois.card_aut_eq_finrank K L).trans hdegree
  obtain ⟨σ, hσord⟩ := exists_prime_orderOf_dvd_card' p (by rw [hcardL])
  have hσres : henselianResidueAction D.valuation T.valuation σ = 1 := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := hres x
    exact (henselianResidueAction D.valuation T.valuation σ).commutes y
  let τ : inertiaGroup K T.valuation.valuationSubring :=
    ⟨henselianGalToDecomposition D.valuation T.valuation σ, congrArg AlgEquiv.toRingEquiv hσres⟩
  have hτ : τ ≠ 1 := by
    intro h
    have hσ : σ = 1 := congrArg
      (fun x : inertiaGroup K T.valuation.valuationSubring =>
        inertiaGroupToAut (K := K) T.valuation.valuationSubring x) h
    rw [hσ, orderOf_one] at hσord
    exact (Fact.out : p.Prime).ne_one hσord.symm
  let j : L →ₐ[K] Ω := IsScalarTower.toAlgHom K L Ω
  let E₀ : IntermediateField K Ω := j.fieldRange
  have : FiniteDimensional K E₀ := Module.Finite.equiv j.equivFieldRange.toLinearEquiv
  have : IsGalois K E₀ := IsGalois.of_algEquiv j.equivFieldRange
  let E : FiniteGaloisIntermediateField K Ω := ⟨E₀⟩
  let e : E ≃ₐ[K] L := j.equivFieldRange.symm
  let B : _root_.ValuationSubring E := T.valuation.valuationSubring.comap e.toRingHom
  have hB : B = z.valuationSubring.comap E.toIntermediateField.val.toRingHom := by
    ext x
    change T.valuation (e x) ≤ 1 ↔ z (E.toIntermediateField.val x) ≤ 1
    have he : algebraMap L Ω (e x) = E.toIntermediateField.val x := by
      change j (j.equivFieldRange.symm x) = (x : Ω)
      exact congrArg (fun y : E₀ => (y : Ω)) (j.equivFieldRange.apply_symm_apply x)
    rw [← he]
    exact (_root_.Valuation.HasExtension.val_map_le_one_iff T.valuation z (e x)).symm
  have hsquare : e.toRingHom.comp (algebraMap K E) =
      (algebraMap K L).comp (RingHom.id K) := by
    apply RingHom.ext
    intro a
    exact e.commutes a
  let tE : inertiaGroup K B :=
    _root_.HilbertRamification.ValuationSubring.galoisPullback_inertiaGroupMap
      (RingHom.id K) e.toRingHom hsquare T.valuation.valuationSubring τ
  have htE : tE ≠ 1 := by
    intro h
    apply hτ
    apply Subtype.ext
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    have heq := _root_.HilbertRamification.galoisPullback_galoisPullback_commutes
      (RingHom.id K) e.toRingHom hsquare
      (inertiaGroupToAut (K := K) T.valuation.valuationSubring τ) y
    change e (inertiaGroupToAut (K := K) B tE y) = σ (e y) at heq
    rw [h, map_one] at heq
    exact heq.symm
  have hcardE : Nat.card Gal(E/K) = p := by
    rw [IsGalois.card_aut_eq_finrank]
    exact e.toLinearEquiv.finrank_eq.trans hdegree
  have hPGal : IsPGroup p Gal(E/K) := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hcardE)
  have hPB : IsPGroup p (inertiaGroup K B) :=
    hPGal.of_injective (inertiaGroupToAut (K := K) B)
      (fun a b h => Subtype.ext (Subtype.ext h))
  refine ⟨E, ?_, ?_⟩
  · rw [← hB]
    exact hPB
  · rw [← hB]
    exact ⟨tE, htE⟩

end ValuationTheory.DiscreteValuationField
