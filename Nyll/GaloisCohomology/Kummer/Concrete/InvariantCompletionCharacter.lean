/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.GaloisCohomology.Kummer.Concrete.ProlongationCharacterApproximation
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteCharacterAverage
import Nyll.ValuedFieldTheory.Valuation.Completion.EquivariantMap
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.EquivFin

/-!
# Invariant lifts of completion characters

A finite Galois extension containing the required roots of unity admits
a simultaneous lift of prescribed completion characters. Averaging the
lift over the Galois group gives invariance while retaining every local
character when the extension degree is prime to the modulus.
-/

namespace KummerTheory

open ValuationTheory.DiscreteValuationField
open Field.absoluteGaloisGroup

universe u v w z

/-- Prescribed local characters admit an invariant simultaneous lift over a
prime-to-modulus finite Galois extension containing the relevant roots of unity. -/
theorem exists_invariant_completion_character
    {ι : Type*} [Finite ι] {K : Type u} {E : Type w}
    [Field K] [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (D : ι → DVF.{u, v} K)
    (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))
    (V : ι → DVF.{w, z} E)
    [hV : ∀ i, (D i).valuation.HasExtension (V i).valuation]
    (n : ℕ+) [NeZero ((n : ℕ) : E)]
    (hn : (Nat.card Gal(E/K)).Coprime (n : ℕ))
    (hmu : (primitiveRoots (n : ℕ) E).Nonempty)
    (χ : ∀ i, Gal(AlgebraicClosure (D i).valuation.Completion/(D i).valuation.Completion) →ₜ*
      Multiplicative (ZMod (n : ℕ))) :
    ∃ ψ : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod (n : ℕ)),
      (∀ (δ : Gal(E/K)) (σ : Gal(AlgebraicClosure E/E)),
        ψ (absoluteGaloisConjugate δ.toRingEquiv σ) = ψ σ) ∧
      ∀ i, (ψ.comp (map (algebraMap E (V i).valuation.Completion)) :
        Gal(AlgebraicClosure (V i).valuation.Completion/(V i).valuation.Completion) →ₜ*
          Multiplicative (ZMod (n : ℕ))) =
        (χ i).comp (map (DVF.completionMap (D i) (V i))) := by
  classical
  let : Fintype Gal(E/K) := Fintype.ofFinite Gal(E/K)
  let W (j : ι × Gal(E/K)) : DVF.{w,z} E :=
    { ValueGroup := (V j.1).ValueGroup
      valuation := (V j.1).valuation.comap j.2.toRingHom
      instRankOneDiscrete := Valuation.isRankOneDiscrete_comap_ringEquiv
        (V j.1).valuation j.2.toRingEquiv }
  have hWext : ∀ j : ι × Gal(E/K), (D j.1).valuation.HasExtension (W j).valuation := by
    intro j
    constructor
    intro x y
    change (D j.1).valuation x ≤ (D j.1).valuation y ↔
      (V j.1).valuation (j.2 (algebraMap K E x)) ≤
        (V j.1).valuation (j.2 (algebraMap K E y))
    rw [j.2.commutes, j.2.commutes]
    exact _root_.Valuation.HasExtension.val_isEquiv_comap
      (vR := (D j.1).valuation) (vA := (V j.1).valuation) x y
  obtain ⟨φ, hφ⟩ := exists_completion_character_on_prolongations D hD W Prod.fst n hmu χ
  let ψ := absoluteCharacterAverage (K := K) (n : ℕ) φ
  refine ⟨ψ, fun δ σ => absoluteCharacterAverage_conjugate (n : ℕ) φ δ σ, ?_⟩
  intro i
  apply ContinuousMonoidHom.ext
  intro σ
  apply absoluteCharacterAverage_eq_of_forall (n : ℕ)
    (by simpa only [Nat.card_eq_fintype_card] using hn) φ
  intro δ
  let j : ι × Gal(E/K) := (i, δ)
  have : (D i).valuation.HasExtension (W j).valuation := hWext j
  have hequiv : (W j).valuation.IsEquiv ((V i).valuation.comap δ.toRingHom) :=
    _root_.Valuation.IsEquiv.refl
  let g := DVF.completionRingEquiv (W j) (V i) δ.toRingEquiv hequiv
  have hg : (algebraMap E (V i).valuation.Completion).comp δ.toRingHom =
      g.toRingHom.comp (algebraMap E (W j).valuation.Completion) := by
    ext x
    exact (DVF.completionRingEquiv_algebraMap (W j) (V i) δ.toRingEquiv hequiv x).symm
  have hgbase : g.toRingHom.comp (DVF.completionMap (D i) (W j)) =
      DVF.completionMap (D i) (V i) :=
    DVF.completionRingEquiv_comp_completionMap (D i) (W j) (V i) δ hequiv
  have heq : (φ.comp (map δ.toRingHom)).comp
      (map (algebraMap E (V i).valuation.Completion)) =
      (φ.comp (map (algebraMap E (W j).valuation.Completion))).comp (map g.toRingHom) :=
    (character_map_comp δ.toRingHom (algebraMap E (V i).valuation.Completion) φ).symm.trans
      ((congrArg (fun f => φ.comp (map f)) hg).trans
        (character_map_comp (algebraMap E (W j).valuation.Completion) g.toRingHom φ))
  exact (DFunLike.congr_fun heq σ).trans
    ((DFunLike.congr_fun (hφ j) (map g.toRingHom σ)).trans
      (DFunLike.congr_fun
        ((character_map_comp (DVF.completionMap (D i) (W j)) g.toRingHom (χ i)).symm.trans
          (congrArg (fun f => (χ i).comp (map f)) hgbase)) σ))

end KummerTheory
