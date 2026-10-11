/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerH1

/-!
# Evaluating absolute Kummer characters

The absolute Kummer character of a power class evaluates as the Galois
quotient of any root with the prescribed power.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K] [CharZero K]

/-- The absolute Kummer character of a unit class is computed from any
`n`-th root of that unit in the algebraic closure. -/
theorem absoluteKummerContinuousNthRootsCharacterEquiv_apply_of_pow_eq
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (β : (AlgebraicClosure K)ˣ)
    (hβ : β ^ (n : ℕ) =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a)
    (σ : Field.absoluteGaloisGroup K) :
    ((absoluteKummerContinuousNthRootsCharacterEquiv K n hmu
        (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ :
      DiscreteNthRootsSubgroup (AlgebraicClosure K) (n : ℕ)) :
        (AlgebraicClosure K)ˣ) =
      rootQuotient (K := K) (L := AlgebraicClosure K) β σ := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := AlgebraicClosure K) n
  let δ : D.carrier := unitsEquivAbsoluteRadicalCarrier K n a
  let hbase :=
    nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := AlgebraicClosure K) n hmu
  let hfixed := nthRootsOfUnity_fixed (K := K) (L := AlgebraicClosure K) n hbase
  have hδ : δ.1 = a := by
    dsimp only [δ, unitsEquivAbsoluteRadicalCarrier, MulEquiv.trans_apply]
    exact MulEquiv.subgroupCongr_apply
      (finiteKummerRadicalSubgroup_algebraicClosure_eq_top K n).symm
      (Subgroup.topEquiv.symm a)
  have hclass :
      absolutePowerClassEquivRadicalQuotient K n
        (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) =
      D.radicalQuotientMk δ := by
    unfold absolutePowerClassEquivRadicalQuotient
    simp only [MulEquiv.trans_apply]
    apply D.radicalQuotientMulEquiv.injective
    rw [MulEquiv.apply_symm_apply, D.radicalQuotientMk_apply]
    erw [QuotientGroup.congr_apply]
    rfl
  change ((infiniteKummerContinuousQuotientCharacter n hbase
      (absolutePowerClassEquivRadicalQuotient K n
        (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range))).toMonoidHom σ :
      (AlgebraicClosure K)ˣ) =
    rootQuotient (K := K) (L := AlgebraicClosure K) β σ
  rw [hclass, infiniteKummerContinuousQuotientCharacter_toMonoidHom,
    D.quotientKummerCharacterWithoutSection_mk]
  change D.rootCharacter δ hfixed σ =
    rootQuotient (K := K) (L := AlgebraicClosure K) β σ
  exact (D.rootCharacter_eq_of_same_pow hfixed δ (hδ ▸ hβ) σ).symm

end ClassFieldTower.Martinet.Shafarevich
