/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Kummer.RadicalRepresentatives

/-!
# Tame ramification implies radical generation

The corrected representatives of all value-group cosets generate an
intermediate field with the same value group and residue field as the target.
The immediate prime-to-`p` lemma then identifies that field with the target.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations

section FiniteTameRadicalGeneration

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

local instance exponentialValueGroupQuotientAddCommGroupForward
    {F E : Type u} [Field F] [Field E]
    (v : LubinTate.Valuations.ExponentialValuation F)
    (w : LubinTate.Valuations.ExponentialValuation E) :
    AddCommGroup (ExponentialValueGroupQuotient v w) := by
  unfold ExponentialValueGroupQuotient
  infer_instance

/-- A finite tame extension is generated over its maximal unramified
subextension by prime-to-characteristic radicals. -/
theorem generatedOverMaximalUnramifiedByRadicals_of_finiteTame
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hTame : FiniteTamelyRamifiedExtension v w hExt) :
    GeneratedOverMaximalUnramifiedByRadicals v w hExt := by
  classical
  rcases hTame with ⟨hp, hsep, hdegree⟩
  let T := maximalUnramifiedSubextension v w hExt
  let wT := exponentialValuationRestrict w T
  let hKT : ∀ a : K, wT (algebraMap K T a) = v a :=
    exponentialValuationRestrict_extends v w hExt T
  let hTL : ∀ a : T, w (algebraMap T L a) = wT a := by
    intro a
    rfl
  have hhensT : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wT).valuation :=
    henselianValuation_of_algebraic_extension v wT hKT hhens
  have hcharT :
      residueCharacteristic v = residueCharacteristic wT :=
    residueCharacteristic_eq_of_exact_extension v wT hKT
  have hpT : PositiveResidueCharacteristic wT := by
    change residueCharacteristic wT ≠ 0
    rw [← hcharT]
    exact hp
  have hdegreeT : Nat.Coprime (Module.finrank T L)
      (residueCharacteristic wT) := by
    rw [← hcharT]
    exact hdegree
  have hresT : Function.Surjective (tameResidueFieldMap wT w hTL) :=
    maximalUnramifiedSubextension_residueMap_surjective_of_separable
      v w hExt hhens hsep
  let Q := ExponentialValueGroupQuotient wT w
  let : Finite Q :=
    exponentialValueGroupQuotient_finite_of_finiteDimensional wT w hTL
  let : Fintype Q := Fintype.ofFinite Q
  have hrad : ∀ q : Q,
      ∃ (m : ℕ) (a : T) (alpha : L),
        0 < m ∧
          Nat.Coprime m (residueCharacteristic wT) ∧
            alpha ^ m = algebraMap T L a ∧
              ∃ halpha0 : alpha ≠ 0,
                exponentialValueCoset wT w alpha halpha0 = q := by
    intro q
    exact exists_prime_to_radical_representing_valueCoset
      wT w hTL hhensT hpT hdegreeT hresT q
  choose m a alpha hmpos hmcop hpow halpha0 hclass using hrad
  let M : IntermediateField T L :=
    IntermediateField.adjoin T (Set.range alpha)
  let wM := exponentialValuationRestrict w M
  let hTM : ∀ t : T, wM (algebraMap T M t) = wT t := by
    intro t
    rfl
  let hML : ∀ z : M, w (algebraMap M L z) = wM z := by
    intro z
    rfl
  have halphaM (q : Q) : alpha q ∈ M := by
    exact IntermediateField.subset_adjoin T (Set.range alpha)
      (Set.mem_range_self q)
  have hvalueM : exponentialValueSubgroup w =
      exponentialValueSubgroup wM := by
    ext r
    constructor
    · rintro ⟨x, hx0, hxValue⟩
      let q : Q := exponentialValueCoset wT w x hx0
      have hcoset :
          exponentialValueCoset wT w x hx0 =
            exponentialValueCoset wT w (alpha q) (halpha0 q) := by
        exact (hclass q).symm
      obtain ⟨t, ht0, htValue⟩ :=
        exists_base_element_mul_value_eq_of_exponentialValueCoset_eq
          wT w hTL hx0 (halpha0 q) hcoset
      let z : M :=
        ⟨algebraMap T L t * alpha q,
          M.mul_mem (M.algebraMap_mem t) (halphaM q)⟩
      have hz0 : z ≠ 0 := by
        intro hz
        have hzL := congrArg (fun y : M ↦ (y : L)) hz
        exact (mul_ne_zero
          ((map_ne_zero (algebraMap T L)).2 ht0) (halpha0 q))
          (by simpa [z] using hzL)
      refine ⟨z, hz0, ?_⟩
      change w (algebraMap T L t * alpha q) = (r : WithTop ℝ)
      rw [← htValue]
      exact hxValue
    · rintro ⟨z, hz0, hzValue⟩
      have hzL0 : (z : L) ≠ 0 := by
        intro hz
        exact hz0 (Subtype.ext hz)
      exact ⟨(z : L), hzL0, hzValue⟩
  let VT := LubinTate.Valuations.exponentialValuationSubring wT
  let VM := LubinTate.Valuations.exponentialValuationSubring wM
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let iTM := unramifiedValuationRingValuationRingMap wT wM hTM
  let iML := unramifiedValuationRingValuationRingMap wM w hML
  let iTL := unramifiedValuationRingValuationRingMap wT w hTL
  let : IsLocalHom iTM :=
    unramifiedValuationRingValuationRingMap_isLocalHom wT wM hTM
  let : IsLocalHom iML :=
    unramifiedValuationRingValuationRingMap_isLocalHom wM w hML
  let : IsLocalHom iTL :=
    unramifiedValuationRingValuationRingMap_isLocalHom wT w hTL
  let kT := IsLocalRing.ResidueField VT
  let kM := IsLocalRing.ResidueField VM
  let ell := IsLocalRing.ResidueField W
  let fTM : kT →+* kM := IsLocalRing.ResidueField.map iTM
  let fML : kM →+* ell := IsLocalRing.ResidueField.map iML
  let fTL : kT →+* ell := IsLocalRing.ResidueField.map iTL
  have hi : iTL = iML.comp iTM := by
    ext x
    rfl
  have hf : fTL = fML.comp fTM := by
    dsimp only [fTL, fML, fTM]
    simpa only [hi] using
      (IsLocalRing.ResidueField.map_comp iTM iML)
  have hresTL : Function.Surjective fTL := by
    exact hresT
  have hresML : Function.Surjective fML := by
    intro y
    obtain ⟨x, hx⟩ := hresTL y
    refine ⟨fTM x, ?_⟩
    calc
      fML (fTM x) = (fML.comp fTM) x := rfl
      _ = fTL x := by rw [← hf]
      _ = y := hx
  have hresM : Function.Surjective (tameResidueFieldMap wM w hML) := by
    exact hresML
  have hhensM : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wM).valuation :=
    henselianValuation_of_algebraic_extension wT wM hTM hhensT
  have hdegreeDvd : Module.finrank M L ∣ Module.finrank T L := by
    refine ⟨Module.finrank T M, ?_⟩
    rw [mul_comm, Module.finrank_mul_finrank]
  have hdegreeMOverT : Nat.Coprime (Module.finrank M L)
      (residueCharacteristic wT) :=
    Nat.Coprime.of_dvd_left hdegreeDvd hdegreeT
  have hcharM :
      residueCharacteristic wT = residueCharacteristic wM :=
    residueCharacteristic_eq_of_exact_extension wT wM hTM
  have hpM : PositiveResidueCharacteristic wM := by
    change residueCharacteristic wM ≠ 0
    rw [← hcharM]
    exact hpT
  have hdegreeM : Nat.Coprime (Module.finrank M L)
      (residueCharacteristic wM) := by
    rw [← hcharM]
    exact hdegreeMOverT
  have hfinrankM : Module.finrank M L = 1 :=
    finrank_eq_one_of_valueSubgroup_eq_of_residue_surjective_of_coprime
      wM w hML hhensM hpM hdegreeM hvalueM hresM
  have hMtop : M = (⊤ : IntermediateField T L) :=
    IntermediateField.finrank_eq_one_iff_eq_top.mp hfinrankM
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  have hrange : Set.range (fun i : Fin (Fintype.card Q) ↦ alpha (e.symm i)) =
      Set.range alpha := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨e q, by simp⟩
  refine ⟨Fintype.card Q,
    (fun i ↦ m (e.symm i)),
    (fun i ↦ a (e.symm i)),
    (fun i ↦ alpha (e.symm i)), ?_, ?_, ?_, ?_⟩
  · intro i
    exact hmpos (e.symm i)
  · intro i
    rw [hcharT]
    exact hmcop (e.symm i)
  · intro i
    exact hpow (e.symm i)
  · rw [hrange]
    exact hMtop

end FiniteTameRadicalGeneration

end Valuations
end AlgebraicNumberTheory

end
