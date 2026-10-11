/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.InfiniteCharacterEquiv
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Kummer characters over the separable closure

For an exponent nonzero in the base field, every unit has a root in the
separable closure. The existing Galois Kummer equivalence therefore applies
without a perfectness or characteristic-zero hypothesis.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K]

/-- Every base unit admits an `n`-th root in the separable closure when `n`
is nonzero in the base field. -/
theorem finiteKummerRadicalSubgroup_separableClosure_eq_top
    (n : ℕ+) [NeZero ((n : ℕ) : K)] :
    finiteKummerRadicalSubgroup (K := K) (L := SeparableClosure K) n = ⊤ := by
  have : NeZero ((n : ℕ) : SeparableClosure K) :=
    NeZero.nat_of_injective (f := algebraMap K (SeparableClosure K))
      (algebraMap K (SeparableClosure K)).injective
  apply top_unique
  intro a _
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap K (SeparableClosure K) (a : K)) (n : ℕ)
  have hβ_ne : β ≠ 0 := by
    intro hzero
    have hmap_zero : algebraMap K (SeparableClosure K) (a : K) = 0 := by
      rw [← hβ, hzero, zero_pow n.ne_zero]
    exact a.ne_zero ((algebraMap K (SeparableClosure K)).injective
      (hmap_zero.trans (map_zero (algebraMap K (SeparableClosure K))).symm))
  refine ⟨Units.mk0 β hβ_ne, ?_⟩
  exact Units.ext hβ

private def unitsEquivSeparableRadicalCarrier
    (n : ℕ+) [NeZero ((n : ℕ) : K)] :
    Kˣ ≃* (chosenFiniteKummerRadicalDatum
      (K := K) (L := SeparableClosure K) n).carrier :=
  Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr
      (finiteKummerRadicalSubgroup_separableClosure_eq_top K n).symm)

private theorem map_powerRange_unitsEquivSeparableRadicalCarrier
    (n : ℕ+) [NeZero ((n : ℕ) : K)] :
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range.map
        (unitsEquivSeparableRadicalCarrier K n).toMonoidHom =
      (chosenFiniteKummerRadicalDatum
        (K := K) (L := SeparableClosure K) n).ambientNthPowersSubgroup := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := SeparableClosure K) n
  ext a
  constructor
  · rintro ⟨x, ⟨b, rfl⟩, rfl⟩
    exact D.mem_ambientNthPowersSubgroup_iff.mpr ⟨b, rfl⟩
  · intro ha
    obtain ⟨b, hb⟩ := D.mem_ambientNthPowersSubgroup_iff.mp ha
    let x : Kˣ := a.1
    have hx : x = b ^ (n : ℕ) := hb.symm
    refine ⟨x, ⟨b, hx.symm⟩, ?_⟩
    apply Subtype.ext
    rfl

private def separablePowerClassEquivRadicalQuotient
    (n : ℕ+) [NeZero ((n : ℕ) : K)] :
    Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range ≃*
      (chosenFiniteKummerRadicalDatum
        (K := K) (L := SeparableClosure K) n).RadicalQuotient :=
  (QuotientGroup.congr
      (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
      (chosenFiniteKummerRadicalDatum
        (K := K) (L := SeparableClosure K) n).ambientNthPowersSubgroup
      (unitsEquivSeparableRadicalCarrier K n)
      (map_powerRange_unitsEquivSeparableRadicalCarrier K n)).trans
    (chosenFiniteKummerRadicalDatum
      (K := K) (L := SeparableClosure K) n).radicalQuotientMulEquiv.symm

/-- Power classes identify with continuous Kummer characters of the actual
separable closure, in arbitrary characteristic prime to the exponent. -/
def separableKummerContinuousNthRootsCharacterEquiv
    (n : ℕ+) [NeZero ((n : ℕ) : K)]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range ≃*
      (Gal(SeparableClosure K/K) →ₜ*
        DiscreteNthRootsSubgroup (SeparableClosure K) (n : ℕ)) :=
  (separablePowerClassEquivRadicalQuotient K n).trans
    (infiniteKummerContinuousCharacterEquivOfPrimitiveRoots
      (K := K) (Ω := SeparableClosure K) n hmu)

/-- Evaluation uses any root with the prescribed power, independently of
the root chosen in constructing the character equivalence. -/
theorem separableKummerContinuousNthRootsCharacterEquiv_apply_of_pow_eq
    (n : ℕ+) [NeZero ((n : ℕ) : K)]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (β : (SeparableClosure K)ˣ)
    (hβ : β ^ (n : ℕ) =
      Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (σ : Gal(SeparableClosure K/K)) :
    ((separableKummerContinuousNthRootsCharacterEquiv K n hmu
        (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ :
      DiscreteNthRootsSubgroup (SeparableClosure K) (n : ℕ)) :
        (SeparableClosure K)ˣ) =
      rootQuotient (K := K) (L := SeparableClosure K) β σ := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := SeparableClosure K) n
  let δ : D.carrier := unitsEquivSeparableRadicalCarrier K n a
  let hbase := nthRootsOfUnityInBase_of_primitiveRoots
    (K := K) (L := SeparableClosure K) n hmu
  let hfixed := nthRootsOfUnity_fixed (K := K) (L := SeparableClosure K) n hbase
  have hδ : δ.1 = a := by
    dsimp only [δ, unitsEquivSeparableRadicalCarrier, MulEquiv.trans_apply]
    exact MulEquiv.subgroupCongr_apply
      (finiteKummerRadicalSubgroup_separableClosure_eq_top K n).symm
      (Subgroup.topEquiv.symm a)
  have hclass :
      separablePowerClassEquivRadicalQuotient K n
        (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) =
      D.radicalQuotientMk δ := by
    unfold separablePowerClassEquivRadicalQuotient
    simp only [MulEquiv.trans_apply]
    apply D.radicalQuotientMulEquiv.injective
    rw [MulEquiv.apply_symm_apply, D.radicalQuotientMk_apply]
    erw [QuotientGroup.congr_apply]
    rfl
  change ((infiniteKummerContinuousQuotientCharacter n hbase
      (separablePowerClassEquivRadicalQuotient K n
        (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range))).toMonoidHom σ :
      (SeparableClosure K)ˣ) =
    rootQuotient (K := K) (L := SeparableClosure K) β σ
  rw [hclass, infiniteKummerContinuousQuotientCharacter_toMonoidHom,
    D.quotientKummerCharacterWithoutSection_mk]
  change D.rootCharacter δ hfixed σ =
    rootQuotient (K := K) (L := SeparableClosure K) β σ
  exact (D.rootCharacter_eq_of_same_pow hfixed δ (hδ ▸ hβ) σ).symm

end ClassFieldTower.Martinet.Shafarevich
