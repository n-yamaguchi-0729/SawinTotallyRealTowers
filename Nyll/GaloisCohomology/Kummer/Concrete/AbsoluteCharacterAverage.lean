/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.GaloisCohomology.Topology.AbsoluteGaloisMap
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteRestrictionConjugation
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Averaging absolute Galois characters

Average cyclic absolute characters over a finite relative Galois group.
The average is invariant under the relative action and preserves a common
orbit value when the group order is coprime to the character modulus.
-/

namespace KummerTheory

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype Gal(E/K)]

/-- Average a cyclic absolute character over the finite relative Galois group. -/
noncomputable def absoluteCharacterAverage (n : ℕ)
    (χ : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n)) :
    Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n) := by
  let f (δ : Gal(E/K)) : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n) :=
    χ.comp (Field.absoluteGaloisGroup.map δ.toRingHom)
  refine
    { toFun := fun σ => Multiplicative.ofAdd ((Fintype.card Gal(E/K) : ZMod n)⁻¹ *
        ∑ δ : Gal(E/K), (f δ σ).toAdd)
      map_one' := ?_
      map_mul' := ?_
      continuous_toFun := ?_ }
  · change (Fintype.card Gal(E/K) : ZMod n)⁻¹ *
      ∑ δ : Gal(E/K), (f δ 1).toAdd = 0
    simp only [map_one, toAdd_one, Finset.sum_const_zero, mul_zero]
  · intro σ τ
    change (Fintype.card Gal(E/K) : ZMod n)⁻¹ *
      ∑ δ : Gal(E/K), (f δ (σ * τ)).toAdd = _
    simp only [map_mul, toAdd_mul, Finset.sum_add_distrib, mul_add]
    rfl
  · change Continuous fun σ => (Fintype.card Gal(E/K) : ZMod n)⁻¹ *
      ∑ δ : Gal(E/K), (f δ σ).toAdd
    exact continuous_const.mul (continuous_finsetSum _ fun δ _ => (f δ).continuous)

/-- Averaging is invariant under every relative field automorphism. -/
theorem absoluteCharacterAverage_map (n : ℕ)
    (χ : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n))
    (τ : Gal(E/K)) (σ : Gal(AlgebraicClosure E/E)) :
    absoluteCharacterAverage (K := K) n χ (Field.absoluteGaloisGroup.map τ.toRingHom σ) =
      absoluteCharacterAverage (K := K) n χ σ := by
  apply Multiplicative.toAdd.injective
  change (Fintype.card Gal(E/K) : ZMod n)⁻¹ * _ =
    (Fintype.card Gal(E/K) : ZMod n)⁻¹ * _
  congr 1
  calc
    ∑ δ : Gal(E/K), (χ (Field.absoluteGaloisGroup.map δ.toRingHom
        (Field.absoluteGaloisGroup.map τ.toRingHom σ))).toAdd =
      ∑ δ : Gal(E/K), (χ (Field.absoluteGaloisGroup.map (τ * δ).toRingHom σ)).toAdd := by
        apply Finset.sum_congr rfl
        intro δ _
        apply congrArg Multiplicative.toAdd
        exact (DFunLike.congr_fun
          (Field.absoluteGaloisGroup.character_map_comp δ.toRingHom τ.toRingHom χ) σ).symm
    _ = ∑ δ : Gal(E/K), (χ (Field.absoluteGaloisGroup.map δ.toRingHom σ)).toAdd :=
      Equiv.sum_comp (Equiv.mulLeft τ)
        (fun δ : Gal(E/K) => (χ (Field.absoluteGaloisGroup.map δ.toRingHom σ)).toAdd)

/-- Averaging is invariant for the concrete conjugation action. -/
theorem absoluteCharacterAverage_conjugate (n : ℕ)
    (χ : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n))
    (τ : Gal(E/K)) (σ : Gal(AlgebraicClosure E/E)) :
    absoluteCharacterAverage (K := K) n χ (absoluteGaloisConjugate τ.toRingEquiv σ) =
      absoluteCharacterAverage (K := K) n χ σ :=
  (character_map_symm_eq_absoluteGaloisConjugate τ.toRingEquiv
    (absoluteCharacterAverage (K := K) n χ) σ).symm.trans
      (absoluteCharacterAverage_map n χ τ.symm σ)

/-- A common value on an orbit is preserved when the group order is invertible. -/
theorem absoluteCharacterAverage_eq_of_forall (n : ℕ)
    (hn : (Fintype.card Gal(E/K)).Coprime n)
    (χ : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n))
    (σ : Gal(AlgebraicClosure E/E)) (a : Multiplicative (ZMod n))
    (ha : ∀ δ : Gal(E/K), χ (Field.absoluteGaloisGroup.map δ.toRingHom σ) = a) :
    absoluteCharacterAverage (K := K) n χ σ = a := by
  apply Multiplicative.toAdd.injective
  change (Fintype.card Gal(E/K) : ZMod n)⁻¹ *
    ∑ δ : Gal(E/K), (χ (Field.absoluteGaloisGroup.map δ.toRingHom σ)).toAdd = a.toAdd
  simp only [ha, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, ZMod.inv_mul_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr hn), one_mul]

end KummerTheory
