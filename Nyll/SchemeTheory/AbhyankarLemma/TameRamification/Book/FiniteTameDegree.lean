/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Kummer.Tower
import Nyll.SchemeTheory.AbhyankarLemma.Kummer.TameRadicalGeneration
import Nyll.ValuedFieldTheory.LocalField.Unramified.FiniteSupport

/-!
# Degree identities for finite tame exponential-valued extensions

This file supplies the finite maximal-unramified and degree identities needed
to compare the exponential-valuation presentation with the canonical DVF
presentation.  It is stated entirely in the production
`AlgebraicNumberTheory.Valuations` API.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory.Valuations

open scoped IntermediateField

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

/-- In a finite extension, the maximal unramified subextension is itself a
finite unramified extension. -/
theorem maximalUnramifiedSubextension_finiteUnramified
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    let T := maximalUnramifiedSubextension v w hExt
    let wT := exponentialValuationRestrict w T
    let hKT := exponentialValuationRestrict_extends v w hExt T
    FiniteUnramifiedExtension v wT hKT := by
  classical
  let T := maximalUnramifiedSubextension v w hExt
  let wT := exponentialValuationRestrict w T
  let hKT := exponentialValuationRestrict_extends v w hExt T
  have hfg : (⊤ : IntermediateField K T).FG :=
    IntermediateField.fg_top K T
  obtain ⟨s, hs⟩ := hfg
  have hsupport : ∀ x : T, ∃ E : IntermediateField K L,
      (x : L) ∈ E ∧ FiniteUnramifiedSubextension v w hExt E := by
    intro x
    exact exists_finiteUnramifiedSubextension_of_mem_maximal
      v w hExt hhens x.property
  choose E hxE hE using hsupport
  let U : IntermediateField K L :=
    ⨆ x : T, ⨆ (_hx : x ∈ s), E x
  have hUunramified : FiniteUnramifiedSubextension v w hExt U := by
    exact finiteUnramifiedSubextension_finset_iSup
      v w hExt hhens s E (fun x _hx ↦ hE x)
  have hUleT : U ≤ T := by
    dsimp [U]
    apply iSup_le
    intro x
    apply iSup_le
    intro _hx
    exact finiteUnramifiedSubextension_le_maximal v w hExt (hE x)
  have hsU : (↑s : Set T) ⊆ U.comap T.val := by
    intro x hx
    change (x : L) ∈ U
    have hExU : E x ≤ U :=
      le_iSup_of_le x (le_iSup_of_le hx le_rfl)
    exact hExU (hxE x)
  have htopLe : (⊤ : IntermediateField K T) ≤ U.comap T.val := by
    rw [← hs]
    exact IntermediateField.adjoin_le_iff.mpr hsU
  have hTleU : T ≤ U := by
    intro x hx
    let xT : T := ⟨x, hx⟩
    have hxComap : xT ∈ U.comap T.val := htopLe (Set.mem_univ xT)
    exact hxComap
  have hUT : U = T := le_antisymm hUleT hTleU
  rw [hUT] at hUunramified
  rcases hUunramified with ⟨hfinT, hTunramified⟩
  let : FiniteDimensional K T := hfinT
  exact hTunramified

/-- A finite tame extension satisfies the exponential ramification
fundamental identity. -/
theorem finiteTamelyRamifiedExtension_fundamental_identity
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hTame : FiniteTamelyRamifiedExtension v w hExt) :
    Module.finrank K L =
      exponentialRamificationIndex v w * exponentialResidueDegree v w hExt := by
  classical
  rcases hTame with ⟨hp, hsep, hdegree⟩
  let T := maximalUnramifiedSubextension v w hExt
  let wT := exponentialValuationRestrict w T
  let hKT : ∀ a : K, wT (algebraMap K T a) = v a :=
    exponentialValuationRestrict_extends v w hExt T
  let hTL : ∀ a : T, w (algebraMap T L a) = wT a := by
    intro a
    rfl
  have hTUnram : FiniteUnramifiedExtension v wT hKT :=
    maximalUnramifiedSubextension_finiteUnramified v w hExt hhens
  have hdegreeKT : Module.finrank K T =
      exponentialResidueDegree v wT hKT :=
    finiteUnramifiedExtension_degree_eq_residueDegree v wT hKT hTUnram
  have heKT : exponentialRamificationIndex v wT = 1 :=
    exponentialRamificationIndex_eq_one_of_finiteUnramifiedExtension
      v wT hKT hTUnram
  have hhensT : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wT).valuation :=
    henselianValuation_of_algebraic_extension v wT hKT hhens
  have hcharT : residueCharacteristic v = residueCharacteristic wT :=
    residueCharacteristic_eq_of_exact_extension v wT hKT
  have hpT : PositiveResidueCharacteristic wT := by
    change residueCharacteristic wT ≠ 0
    rw [← hcharT]
    exact hp
  have hresTL : Function.Surjective (tameResidueFieldMap wT w hTL) :=
    maximalUnramifiedSubextension_residueMap_surjective_of_separable
      v w hExt hhens hsep
  have hfTL : exponentialResidueDegree wT w hTL = 1 :=
    exponentialResidueDegree_eq_one_of_surjective wT w hTL hresTL
  have hrad : GeneratedOverMaximalUnramifiedByRadicals v w hExt :=
    generatedOverMaximalUnramifiedByRadicals_of_finiteTame
      v w hExt hhens ⟨hp, hsep, hdegree⟩
  change GeneratedByRadicalsPrimeTo T (residueCharacteristic v) at hrad
  rcases hrad with ⟨r, m, a, alpha, hmpos, hmcop, hpow, hgen⟩
  have hmcopT : ∀ i, Nat.Coprime (m i) (residueCharacteristic wT) := by
    intro i
    rw [← hcharT]
    exact hmcop i
  have heTL : exponentialRamificationIndex wT w = Module.finrank T L :=
    exponentialRamificationIndex_eq_finrank_of_radical_family
      wT w hTL hhensT hpT hresTL r m a alpha hmpos hmcopT hpow hgen
  have heTower : exponentialRamificationIndex v wT *
      exponentialRamificationIndex wT w = exponentialRamificationIndex v w :=
    exponentialRamificationIndex_mul_in_tower v wT w hKT hTL
  have hfTower : exponentialResidueDegree v wT hKT *
      exponentialResidueDegree wT w hTL = exponentialResidueDegree v w hExt :=
    exponentialResidueDegree_mul_in_tower v wT w hKT hTL hExt
  have heWhole : exponentialRamificationIndex v w =
      exponentialRamificationIndex wT w := by
    rw [heKT, one_mul] at heTower
    exact heTower.symm
  have hfWhole : exponentialResidueDegree v w hExt =
      exponentialResidueDegree v wT hKT := by
    rw [hfTL, mul_one] at hfTower
    exact hfTower.symm
  calc
    Module.finrank K L = Module.finrank K T * Module.finrank T L :=
      (Module.finrank_mul_finrank K T L).symm
    _ = exponentialResidueDegree v wT hKT *
        exponentialRamificationIndex wT w := by rw [hdegreeKT, heTL]
    _ = exponentialRamificationIndex wT w *
        exponentialResidueDegree v wT hKT := Nat.mul_comm _ _
    _ = exponentialRamificationIndex v w *
        exponentialResidueDegree v w hExt := by rw [heWhole, hfWhole]

/-- In a finite tame extension, the degree over the maximal unramified
subextension is the exponential ramification index. -/
theorem finiteTamelyRamifiedExtension_finrank_maximalUnramified_eq_ramificationIndex
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hTame : FiniteTamelyRamifiedExtension v w hExt) :
    Module.finrank (maximalUnramifiedSubextension v w hExt) L =
      exponentialRamificationIndex v w := by
  let T := maximalUnramifiedSubextension v w hExt
  let wT := exponentialValuationRestrict w T
  let hKT := exponentialValuationRestrict_extends v w hExt T
  let hTL : ∀ a : T, w (algebraMap T L a) = wT a := by
    intro a
    rfl
  have hfundamental : Module.finrank K L =
      exponentialRamificationIndex v w * exponentialResidueDegree v w hExt :=
    finiteTamelyRamifiedExtension_fundamental_identity v w hExt hhens hTame
  have hTunram : FiniteUnramifiedExtension v wT hKT :=
    maximalUnramifiedSubextension_finiteUnramified v w hExt hhens
  have hdegreeKT : Module.finrank K T =
      exponentialResidueDegree v wT hKT :=
    finiteUnramifiedExtension_degree_eq_residueDegree v wT hKT hTunram
  have hresTL : Function.Surjective (tameResidueFieldMap wT w hTL) :=
    maximalUnramifiedSubextension_residueMap_surjective_of_separable
      v w hExt hhens hTame.2.1
  have hfTL : exponentialResidueDegree wT w hTL = 1 :=
    exponentialResidueDegree_eq_one_of_surjective wT w hTL hresTL
  have hfTower : exponentialResidueDegree v wT hKT *
      exponentialResidueDegree wT w hTL = exponentialResidueDegree v w hExt :=
    exponentialResidueDegree_mul_in_tower v wT w hKT hTL hExt
  have hf : exponentialResidueDegree v w hExt =
      exponentialResidueDegree v wT hKT := by
    rw [hfTL, mul_one] at hfTower
    exact hfTower.symm
  have hfieldTower : Module.finrank K T * Module.finrank T L =
      Module.finrank K L := Module.finrank_mul_finrank K T L
  have hleftPos : 0 < exponentialResidueDegree v wT hKT := by
    rw [← hdegreeKT]
    exact Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hleftPos
  calc
    exponentialResidueDegree v wT hKT * Module.finrank T L =
        Module.finrank K T * Module.finrank T L := by rw [hdegreeKT]
    _ = Module.finrank K L := hfieldTower
    _ = exponentialRamificationIndex v w *
        exponentialResidueDegree v w hExt := hfundamental
    _ = exponentialRamificationIndex v w *
        exponentialResidueDegree v wT hKT := by rw [hf]
    _ = exponentialResidueDegree v wT hKT *
        exponentialRamificationIndex v w := Nat.mul_comm _ _

end AlgebraicNumberTheory.Valuations

end
