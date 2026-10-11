/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianTorsionRoots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Lifting and finiteness of primary roots

Hensel lifting supplies primitive roots, while injectivity of torsion reduction
transfers finiteness of each primary component in residue characteristic zero.
-/

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

universe u v

variable {K : Type u} [Field K] (F : HenselianDVF.{u, v} K)

/-- A primitive root of prime order in the residue field lifts to the field. -/
theorem primitiveRoots_prime_nonempty_of_residue
    [CharZero F.residueField] {p : ℕ} (hp : p.Prime)
    (hres : (primitiveRoots p F.residueField).Nonempty) :
    (primitiveRoots p K).Nonempty := by
  obtain ⟨ζ, hζ⟩ := hres
  have hprim := (mem_primitiveRoots hp.pos).mp hζ
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : F.residueField) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  let ξ : rootsOfUnity p F.residueField := rootsOfUnity.mkOfPowEq ζ hprim.pow_eq_one
  let η : rootsOfUnity p K := (F.fieldRootsOfUnityReductionEquiv p).symm ξ
  have hηpow : ((η : Kˣ) : K) ^ p = 1 :=
    (mem_rootsOfUnity' p (η : Kˣ)).mp η.property
  have hηne : ((η : Kˣ) : K) ≠ 1 := by
    intro h
    have hη : η = 1 := rootsOfUnity.coe_injective h
    have hξ : ξ = 1 := by
      rw [← (F.fieldRootsOfUnityReductionEquiv p).apply_symm_apply ξ]
      change F.fieldRootsOfUnityReductionEquiv p η = 1
      rw [hη, map_one]
    apply hprim.ne_one hp.one_lt
    exact congrArg (fun z : rootsOfUnity p F.residueField =>
      ((z : F.residueFieldˣ) : F.residueField)) hξ
  exact ⟨((η : Kˣ) : K), (mem_primitiveRoots hp.pos).mpr
    (isPrimitiveRoot_of_mem_nthRootsFinset hp
      ((Polynomial.mem_nthRootsFinset hp.pos 1).mpr hηpow) hηne)⟩

/-- In residue characteristic zero, finiteness of the residual primary roots
implies finiteness of the primary roots in the Henselian field. -/
theorem finite_primaryComponent_of_finite_residuePrimaryComponent
    [CharZero F.residueField] {p : ℕ} (hp : p.Prime)
    [Finite (CommGroup.primaryComponent F.residueFieldˣ p)] :
    Finite (CommGroup.primaryComponent Kˣ p) := by
  let i : CommGroup.primaryComponent Kˣ p →* CommGroup.torsion Kˣ :=
    (CommGroup.primaryComponent Kˣ p).inclusion (by
      intro z hz
      obtain ⟨n, hn⟩ := (CommGroup.mem_primaryComponent).mp hz
      exact (CommGroup.mem_torsion z).mpr
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ n, pow_pos hp.pos n, hn⟩))
  let f : CommGroup.primaryComponent Kˣ p →* F.residueFieldˣ :=
    (CommGroup.torsion F.residueFieldˣ).subtype.comp (F.toDVF.torsionReduction.comp i)
  have hf (z : CommGroup.primaryComponent Kˣ p) :
      f z ∈ CommGroup.primaryComponent F.residueFieldˣ p := by
    obtain ⟨n, hn⟩ := (CommGroup.mem_primaryComponent).mp z.property
    refine (CommGroup.mem_primaryComponent).mpr ⟨n, ?_⟩
    have hzn : z ^ (p ^ n) = 1 := Subtype.ext hn
    rw [← map_pow, hzn, map_one]
  let g := f.codRestrict (CommGroup.primaryComponent F.residueFieldˣ p) hf
  apply Finite.of_injective g
  intro a b hab
  apply Subtype.ext
  have hred : F.toDVF.torsionReduction (i a) = F.toDVF.torsionReduction (i b) :=
    Subtype.ext (congrArg (fun z : CommGroup.primaryComponent F.residueFieldˣ p =>
      (z : F.residueFieldˣ)) hab)
  exact congrArg (fun z : CommGroup.torsion Kˣ => (z : Kˣ))
    (F.torsionReduction_injective hred)

/-- The corresponding set of field roots is finite. -/
theorem finite_primePowerRoots_of_finite_residuePrimaryComponent
    [CharZero F.residueField] {p : ℕ} (hp : p.Prime)
    [Finite (CommGroup.primaryComponent F.residueFieldˣ p)] :
    Set.Finite {z : K | ∃ n : ℕ, z ^ (p ^ n) = 1} := by
  have : Finite (CommGroup.primaryComponent Kˣ p) :=
    F.finite_primaryComponent_of_finite_residuePrimaryComponent hp
  let f : {z : K | ∃ n : ℕ, z ^ (p ^ n) = 1} → CommGroup.primaryComponent Kˣ p :=
    fun z => ⟨Units.mk0 z.val (by
      obtain ⟨n, hn⟩ := z.property
      intro hz
      rw [hz, zero_pow (pow_ne_zero n hp.ne_zero)] at hn
      exact zero_ne_one hn), by
        obtain ⟨n, hn⟩ := z.property
        refine (CommGroup.mem_primaryComponent).mpr ⟨n, ?_⟩
        apply Units.ext
        exact hn⟩
  have : Finite {z : K | ∃ n : ℕ, z ^ (p ^ n) = 1} := Finite.of_injective f (by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : CommGroup.primaryComponent Kˣ p => ((z : Kˣ) : K)) hab)
  exact Set.toFinite _

end ValuationTheory.DiscreteValuationField.HenselianDVF
