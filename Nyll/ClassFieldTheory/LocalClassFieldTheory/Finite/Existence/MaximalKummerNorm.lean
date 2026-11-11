/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.SetTheory.Cardinal.Finite
public import Nyll.GaloisCohomology.Kummer.Concrete.LocalMaximalKummerExtension
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.GaloisCohomology.Kummer.Concrete.MaximalKummerSubgroup

/-!
# Norm group of the maximal Kummer extension

When the base field contains the `n`-th roots of unity, Kummer duality and
finite local reciprocity identify the norm subgroup of the maximal
exponent-`n` Kummer extension with the subgroup of `n`-th powers.
-/



@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open CyclicCohomology KummerTheory ClassFormation
open LocalFieldTheory.DiscreteValuationField LocalFieldTheory

universe u v

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {Omega : Type v} [Field Omega] [Algebra K Omega] [IsSepClosure K Omega]

/-- The Galois group of the maximal exponent-`n` Kummer extension is
canonically equivalent to the local power-class group. -/
noncomputable def chosenMaximalKummerGaloisEquivPowerQuotient
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Gal(kummerRadicalExtension (K := K) (Omega := Omega) n
        (KummerTheory.maximalKummerSubgroup K n).1/K) ≃*
      Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  let Delta := KummerTheory.maximalKummerSubgroup K n
  let E := kummerRadicalExtension (K := K) (Omega := Omega) n Delta.1
  let R := RestrictedRadicalQuotient n Delta
  let M := nthRootsSubgroup E (n : ℕ)
  letI : Finite R :=
    KummerTheory.finite_maximalRestrictedRadicalQuotient K n hnK
  have hRExponent : ∀ r : R, r ^ (n : ℕ) = 1 :=
    restrictedRadicalQuotient_pow_eq_one n Delta
  let dualR := Classical.choice (finiteNthRootsCharacterDuality
    (G := R) (K := K) (L := E) n hmu hRExponent)
  exact
    (kummerRadicalExtensionRestrictedTransposeMulEquiv
      (K := K) (Omega := Omega) n hnK hmu Delta).trans
      (dualR.trans
        (KummerTheory.maximalRestrictedRadicalQuotientEquiv K n).symm)

/-- Local reciprocity and Kummer duality identify the norm quotient of the
maximal Kummer extension with the local power-class group. -/
noncomputable def maximalKummerNormQuotientEquivPowerQuotient
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    let E := kummerRadicalExtension (K := K) (Omega := Omega) n
      (KummerTheory.maximalKummerSubgroup K n).1
    NormQuotient K E ≃* Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  let Delta := KummerTheory.maximalKummerSubgroup K n
  let E := kummerRadicalExtension (K := K) (Omega := Omega) n Delta.1
  letI : IsGalois K E :=
    kummerRadicalExtension_isGalois (K := K) (Omega := Omega) n Delta.1
  letI : FiniteDimensional K E :=
    KummerTheory.maximalKummerRadicalExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu
  letI : IsMulCommutative Gal(E/K) :=
    kummerRadicalExtension_isMulCommutative
      (K := K) (Omega := Omega) n hmu Delta.1
  letI : CommGroup Gal(E/K) :=
    CommGroup.mk (fun a b => IsMulCommutative.is_comm.comm a b)
  letI : IsAbelianGalois K E :=
    kummerRadicalExtension_isAbelianGalois
      (K := K) (Omega := Omega) n hmu Delta.1
  exact
    (Classical.choose (Universe.quotientEquiv_existsUnique K E).exists).toMulEquiv.trans
      (chosenMaximalKummerGaloisEquivPowerQuotient
        (K := K) (Omega := Omega) n hnK hmu)

/-- Every `n`-th power is a norm from the maximal exponent-`n` Kummer
extension. -/
theorem powMonoidHom_range_le_maximalKummerNormSubgroup
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    let E := kummerRadicalExtension (K := K) (Omega := Omega) n
      (KummerTheory.maximalKummerSubgroup K n).1
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range ≤ localNormSubgroup K E := by
  let Delta := KummerTheory.maximalKummerSubgroup K n
  let E := kummerRadicalExtension (K := K) (Omega := Omega) n Delta.1
  let : IsGalois K E :=
    kummerRadicalExtension_isGalois (K := K) (Omega := Omega) n Delta.1
  let : FiniteDimensional K E :=
    KummerTheory.maximalKummerRadicalExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu
  let : IsMulCommutative Gal(E/K) :=
    kummerRadicalExtension_isMulCommutative
      (K := K) (Omega := Omega) n hmu Delta.1
  let : CommGroup Gal(E/K) :=
    CommGroup.mk (fun a b => IsMulCommutative.is_comm.comm a b)
  let : IsAbelianGalois K E :=
    kummerRadicalExtension_isAbelianGalois
      (K := K) (Omega := Omega) n hmu Delta.1
  change (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range ≤ localNormSubgroup K E
  intro x hx
  obtain ⟨y, rfl⟩ :=
    (MonoidHom.mem_range (G := Kˣ)).1 hx
  rw [← Universe.abelianLocalArtinMonoidHom_ker K E, MonoidHom.mem_ker,
    powMonoidHom_apply, map_pow]
  exact kummerRadicalExtension_galois_pow_eq_one
    (K := K) (Omega := Omega) n hmu Delta.1
      (Universe.abelianLocalArtinMonoidHom K E y)

/-- If the base field contains the `n`-th roots of unity, the norm subgroup
of the maximal exponent-`n` Kummer extension is exactly `Kˣⁿ`. -/
theorem maximalKummerNormSubgroup_eq_powMonoidHom_range
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    let E := kummerRadicalExtension (K := K) (Omega := Omega) n
      (KummerTheory.maximalKummerSubgroup K n).1
    localNormSubgroup K E = (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  let Delta := KummerTheory.maximalKummerSubgroup K n
  let E := kummerRadicalExtension (K := K) (Omega := Omega) n Delta.1
  let P := (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
  let N := localNormSubgroup K E
  let : IsGalois K E :=
    kummerRadicalExtension_isGalois (K := K) (Omega := Omega) n Delta.1
  let : FiniteDimensional K E :=
    KummerTheory.maximalKummerRadicalExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu
  let : Finite (Kˣ ⧸ P) :=
    LocalFieldTheory.finite_nthPowerQuotient_of_natCast_ne_zero
      K (n : ℕ) hnK
  let : P.FiniteIndex := P.finiteIndex_of_finite_quotient
  have hle : P ≤ N :=
    powMonoidHom_range_le_maximalKummerNormSubgroup
      (K := K) (Omega := Omega) n hnK hmu
  let : Finite (NormQuotient K E) :=
    Finite.of_equiv (Kˣ ⧸ P)
      (maximalKummerNormQuotientEquivPowerQuotient
        (K := K) (Omega := Omega) n hnK hmu).symm.toEquiv
  have hindex : N.index = P.index := by
    change Nat.card (NormQuotient K E) =
      Nat.card (Kˣ ⧸ P)
    exact Nat.card_congr
      (maximalKummerNormQuotientEquivPowerQuotient
        (K := K) (Omega := Omega) n hnK hmu).toEquiv
  apply le_antisymm
  · by_contra hnot
    have hne : P ≠ N := by
      intro hPN
      apply hnot
      exact hPN.symm.le
    have hlt : P < N := lt_of_le_of_ne hle hne
    have hindexLt : N.index < P.index := Subgroup.index_strictAnti hlt
    rw [hindex] at hindexLt
    exact (Nat.lt_irrefl _ hindexLt)
  · exact hle

end LocalClassFieldTheory

end
