/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.NoetherNormalization.IntegralRelation
import Mathlib.RingTheory.NoetherNormalization

/-!
# Power-triangular normalization over an arbitrary field

This file exposes the power-triangular change of variables used in Nagata's
proof of Noether normalization.  The degree-coding argument is adapted from
`Mathlib.RingTheory.NoetherNormalization` (Apache-2.0; authors Riccardo
Brasca, Sihan Su, Wan Lin, and Xiaoyang Su), where the corresponding
declarations are private.

The distinguished variable is `X 0`.  Every other variable `X i` is sent to
`X i + X 0 ^ mᵢ`, with rapidly growing exponents `mᵢ`.  Distinct monomials of
a fixed nonzero polynomial then acquire distinct degrees in `X 0`, so the
transformed polynomial has invertible leading coefficient over every field.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06

open Polynomial MvPolynomial Nat RingHom List

variable {K : Type*} [Field K] {n : ℕ}

/-- The base used to encode monomial exponent vectors as natural numbers. -/
def powerNormalizationBase (F : MvPolynomial (Fin (n + 1)) K) : ℕ :=
  2 + F.totalDegree

/-- The power assigned to a variable in the power-triangular substitution. -/
def powerNormalizationExponent
    (F : MvPolynomial (Fin (n + 1)) K) (i : Fin (n + 1)) : ℕ :=
  powerNormalizationBase F ^ i.1

/--
The power-triangular algebra map fixing `X 0` and sending every other `X i`
to `X i + c • X 0 ^ powerNormalizationExponent F i`.
-/
noncomputable abbrev powerChangeFirstAux
    (F : MvPolynomial (Fin (n + 1)) K) (c : K) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K]
      MvPolynomial (Fin (n + 1)) K :=
  aeval fun i =>
    if i = 0 then X 0
    else X i + c • X 0 ^ powerNormalizationExponent F i

@[simp]
theorem powerChangeFirstAux_X_zero
    (F : MvPolynomial (Fin (n + 1)) K) (c : K) :
    powerChangeFirstAux F c (X 0) = X 0 := by
  simp [powerChangeFirstAux]

@[simp]
theorem powerChangeFirstAux_X_succ
    (F : MvPolynomial (Fin (n + 1)) K) (c : K) (i : Fin n) :
    powerChangeFirstAux F c (X i.succ) =
      X i.succ + c • X 0 ^ powerNormalizationExponent F i.succ := by
  simp [powerChangeFirstAux]

theorem powerChangeFirstAux_comp_neg
    (F : MvPolynomial (Fin (n + 1)) K) (c : K) :
    (powerChangeFirstAux F c).comp (powerChangeFirstAux F (-c)) =
      AlgHom.id K (MvPolynomial (Fin (n + 1)) K) := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp [powerChangeFirstAux]

/-- The power-triangular substitution as an algebra equivalence. -/
noncomputable abbrev powerChangeFirstEquiv
    (F : MvPolynomial (Fin (n + 1)) K) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K]
      MvPolynomial (Fin (n + 1)) K :=
  AlgEquiv.ofAlgHom (powerChangeFirstAux F 1) (powerChangeFirstAux F (-1))
    (powerChangeFirstAux_comp_neg F 1)
    (by simpa using powerChangeFirstAux_comp_neg F (-1))

section LeadingCoefficient

variable (F : MvPolynomial (Fin (n + 1)) K)
variable (v w : Fin (n + 1) →₀ ℕ)

local notation3 "up" => powerNormalizationBase F
local notation3 "r" => powerNormalizationExponent F
local notation3 "T" => powerChangeFirstEquiv F

lemma powerDigits_lt_base {v : Fin (n + 1) →₀ ℕ}
    (vlt : ∀ i, v i < up) :
    ∀ l ∈ ofFn v, l < up := by
  grind

lemma power_weightedSum_ne
    (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (hne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠
      ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine hne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq
    (Nat.lt_add_right F.totalDegree one_lt_two)
    (by simp) (powerDigits_lt_base F vlt) (powerDigits_lt_base F wlt)
  simpa only [powerNormalizationBase, powerNormalizationExponent,
    ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h

lemma degreeOf_zero_powerChange_monomial {a : K} (ha : a ≠ 0) :
    (T (monomial v a)).degreeOf 0 =
      ∑ i : Fin (n + 1), r i * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq,
    Finsupp.prod_pow v fun a => X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod,
    map_pow, AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, ite_eq_left, Fin.succ_ne_zero, ite_false, one_smul,
    map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := K) i) +
        Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ)
      (leadingCoeff_ne_zero.mp <| by
        simp [powerNormalizationExponent, powerNormalizationBase, add_comm,
          leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha])
      (mul_ne_zero (by simp)
        (Finset.prod_ne_zero_iff.mpr (fun i _ => h i))),
    natDegree_mul (by simp)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => h i)),
    natDegree_prod _ _ (fun i _ => h i), natDegree_finSuccEquiv,
    degreeOf_C]
  simpa only [powerNormalizationBase, powerNormalizationExponent,
    natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero,
    one_mul, add_right_inj] using
    Finset.sum_congr rfl (fun i _ => by
      rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

/--
Distinct monomials in the support of `F` acquire distinct degrees in `X 0`
after the power-triangular substitution.
-/
lemma degreeOf_powerChange_ne_of_ne
    (hv : v ∈ F.support) (hw : w ∈ F.support) (hne : v ≠ w) :
    (T (monomial v (F.coeff v))).degreeOf 0 ≠
      (T (monomial w (F.coeff w))).degreeOf 0 := by
  rw [degreeOf_zero_powerChange_monomial F v (mem_support_iff.mp hv),
    degreeOf_zero_powerChange_monomial F w (mem_support_iff.mp hw)]
  refine power_weightedSum_ne F v w (fun i => ?_) (fun i => ?_) hne <;>
  exact lt_of_le_of_lt
    ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree F i))
    (by simp [powerNormalizationBase])

lemma leadingCoeff_finSuccEquiv_powerChange_monomial :
    (finSuccEquiv K n
      (T ((monomial v) (F.coeff v)))).leadingCoeff =
        algebraMap K _ (F.coeff v) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq,
      finSuccEquiv_apply, eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply,
      leadingCoeff_C, map_pow, leadingCoeff_pow, algebraMap_eq]
    have h :
        ∀ j,
          ((finSuccEquiv K n)
            ((powerChangeFirstAux F 1) (X j))).leadingCoeff = 1 :=
      fun j => by
        by_cases hj : j = 0
        · simp [hj, finSuccEquiv_apply]
        · simp only [powerChangeFirstAux, aeval_eq_bind₁, bind₁_X_right,
            ite_eq_right hj, one_smul, map_add, map_pow]
          obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hj
          simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero,
            powerNormalizationExponent, powerNormalizationBase, add_comm]
    simp only [h, one_pow, Finset.prod_const_one, mul_one]
  exact fun i => pow_zero _

/--
Every nonzero polynomial admits the canonical power-triangular change for
which it is monic up to a unit as a polynomial in `X 0`.
-/
theorem powerChangeFirst_leadingCoeff_isUnit (hF : F ≠ 0) :
    IsUnit (finSuccEquiv K n (T F)).leadingCoeff := by
  obtain ⟨v, hv, hvmax⟩ :=
    Finset.exists_max_image F.support
      (fun v => (T (monomial v (F.coeff v))).degreeOf 0)
      (support_nonempty.mpr hF)
  set h := fun w => (MvPolynomial.monomial w) (F.coeff w)
  simp only [← natDegree_finSuccEquiv] at hvmax
  replace hvmax :
      ∀ x ∈ F.support \ {v},
        (finSuccEquiv K n (T (h x))).degree <
          (finSuccEquiv K n (T (h v))).degree := by
    intro x hx
    obtain ⟨hxF, hxv⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (hvmax x hxF) ?_
    simpa only [natDegree_finSuccEquiv] using
      degreeOf_powerChange_ne_of_ne F x v hxF hv
        (ne_of_not_mem_cons hxv)
  have hcoeff :
      (finSuccEquiv K n
        (T (h v + ∑ x ∈ F.support \ {v}, h x))).leadingCoeff =
          (finSuccEquiv K n (T (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <|
      (lt_of_le_of_lt (degree_sum_le _ _) ?_)
    have hvne : h v ≠ 0 := by
      simpa [h] using mem_support_iff.mp hv
    replace hvne : finSuccEquiv K n (T (h v)) ≠ 0 := fun heq =>
      hvne <| by
        simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using heq
    exact
      (Finset.sup_lt_iff <|
        Ne.bot_lt (fun x => hvne <| degree_eq_bot.mp x)).mpr hvmax
  nth_rw 2 [← F.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hv h]
  rw [leadingCoeff_finSuccEquiv_powerChange_monomial] at hcoeff
  simpa only [hcoeff, algebraMap_eq] using
    (mem_support_iff.mp hv).isUnit.map MvPolynomial.C

end LeadingCoefficient

/--
The transformed tail coordinates in an arbitrary `K`-algebra.  They are the
inverse-coordinate expressions for `powerChangeFirstEquiv F`.
-/
def powerTailCoordinatesFirst
    {A : Type*} [CommRing A] [Algebra K A]
    (F : MvPolynomial (Fin (n + 1)) K)
    (x : Fin (n + 1) → A) : Fin n → A :=
  fun i =>
    x i.succ -
      x 0 ^ powerNormalizationExponent F i.succ

/-- The full inverse-coordinate tuple, retaining the first coordinate. -/
def powerCoordinatesFirst
    {A : Type*} [CommRing A] [Algebra K A]
    (F : MvPolynomial (Fin (n + 1)) K)
    (x : Fin (n + 1) → A) : Fin (n + 1) → A :=
  Fin.cons (x 0) (powerTailCoordinatesFirst F x)

@[simp]
theorem powerCoordinatesFirst_zero
    {A : Type*} [CommRing A] [Algebra K A]
    (F : MvPolynomial (Fin (n + 1)) K)
    (x : Fin (n + 1) → A) :
    powerCoordinatesFirst F x 0 = x 0 := rfl

@[simp]
theorem powerCoordinatesFirst_succ
    {A : Type*} [CommRing A] [Algebra K A]
    (F : MvPolynomial (Fin (n + 1)) K)
    (x : Fin (n + 1) → A) (i : Fin n) :
    powerCoordinatesFirst F x i.succ =
      x i.succ - x 0 ^ powerNormalizationExponent F i.succ := rfl

/--
Evaluating the power transform at its inverse-coordinate tuple recovers
evaluation at the original tuple.
-/
theorem aeval_powerChangeFirst_powerCoordinates
    {A : Type*} [CommRing A] [Algebra K A]
    (F : MvPolynomial (Fin (n + 1)) K)
    (x : Fin (n + 1) → A)
    (P : MvPolynomial (Fin (n + 1)) K) :
    aeval (powerCoordinatesFirst F x) (powerChangeFirstEquiv F P) =
      aeval x P := by
  simp only [powerChangeFirstEquiv, AlgEquiv.ofAlgHom_apply,
    powerChangeFirstAux]
  rw [comp_aeval_apply]
  have hpoints :
      (fun i : Fin (n + 1) =>
        (aeval (powerCoordinatesFirst F x) :
          MvPolynomial (Fin (n + 1)) K →ₐ[K] A)
          (if i = 0 then X 0
            else X i + (1 : K) •
              X 0 ^ powerNormalizationExponent F i)) = x := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      simp [powerCoordinatesFirst, powerTailCoordinatesFirst]
  rw [hpoints]

/--
A nonzero relation makes the first coordinate integral over the algebra
generated by the canonical power-tail coordinates.
-/
theorem powerCoordinatesFirst_isIntegral
    {A : Type*} [CommRing A] [Algebra K A]
    (x : Fin (n + 1) → A) {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F ≠ 0) (hrel : aeval x F = 0) :
    IsIntegral
      (Algebra.adjoin K (Set.range (powerTailCoordinatesFirst F x))) (x 0) := by
  let t : Fin n → A := powerTailCoordinatesFirst F x
  let S : Subalgebra K A := Algebra.adjoin K (Set.range t)
  let p : Polynomial (MvPolynomial (Fin n) K) :=
    finSuccEquiv K n (powerChangeFirstEquiv F F)
  have hpunit : IsUnit p.leadingCoeff := by
    exact powerChangeFirst_leadingCoeff_isUnit F hF
  let q : Polynomial (MvPolynomial (Fin n) K) := hpunit.unit⁻¹ • p
  have hqmonic : q.Monic :=
    Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hpunit
  have hpzero :
      Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom (x 0) p = 0 := by
    calc
      Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom (x 0) p =
          MvPolynomial.aeval (Fin.cons (x 0) t)
            (powerChangeFirstEquiv F F) :=
        (aeval_finCons_eq_eval₂_finSuccEquiv
          (K := K) (x 0) t (powerChangeFirstEquiv F F)).symm
      _ = MvPolynomial.aeval (powerCoordinatesFirst F x)
          (powerChangeFirstEquiv F F) := by
        rfl
      _ = MvPolynomial.aeval x F :=
        aeval_powerChangeFirst_powerCoordinates F x F
      _ = 0 := hrel
  have hqzero :
      Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom (x 0) q = 0 := by
    dsimp only [q]
    rw [Units.smul_def, Polynomial.eval₂_smul]
    exact mul_eq_zero_of_right _ hpzero
  let coeffHom : MvPolynomial (Fin n) K →ₐ[K] S :=
    (MvPolynomial.aeval t).codRestrict S fun P => by
      change MvPolynomial.aeval t P ∈ Algebra.adjoin K (Set.range t)
      rw [← aeval_range]
      exact ⟨P, rfl⟩
  let qS : Polynomial S := q.map coeffHom.toRingHom
  change IsIntegral S (x 0)
  refine ⟨qS, ?_, ?_⟩
  · exact hqmonic.map coeffHom.toRingHom
  · change Polynomial.eval₂ (algebraMap S A) (x 0) qS = 0
    dsimp only [qS]
    rw [Polynomial.eval₂_map]
    have hcomp :
        (algebraMap S A).comp coeffHom.toRingHom =
          (MvPolynomial.aeval t).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        change ((coeffHom (C a) : S) : A) = MvPolynomial.aeval t (C a)
        rfl
      · intro i
        change ((coeffHom (X i) : S) : A) = MvPolynomial.aeval t (X i)
        rfl
    rw [hcomp]
    exact hqzero

/--
Every canonical power-tail coordinate belongs to the algebra generated by the
original tuple.
-/
theorem adjoin_powerTailCoordinatesFirst_le
    {A : Type*} [CommRing A] [Algebra K A]
    (F : MvPolynomial (Fin (n + 1)) K)
    (x : Fin (n + 1) → A) :
    Algebra.adjoin K (Set.range (powerTailCoordinatesFirst F x)) ≤
      Algebra.adjoin K (Set.range x) := by
  rw [Algebra.adjoin_le_iff]
  rintro y ⟨i, rfl⟩
  have hx₀ : x 0 ∈ Algebra.adjoin K (Set.range x) :=
    Algebra.subset_adjoin ⟨(0 : Fin (n + 1)), rfl⟩
  exact Subalgebra.sub_mem _
    (Algebra.subset_adjoin ⟨i.succ, rfl⟩)
    (Subalgebra.pow_mem _
      hx₀ (powerNormalizationExponent F i.succ))

/--
The canonical power-tail coordinates together with the retained first
coordinate generate the same algebra as the original tuple.
-/
theorem adjoin_range_eq_adjoin_powerTailCoordinatesFirst_union
    {A : Type*} [CommRing A] [Algebra K A]
    (F : MvPolynomial (Fin (n + 1)) K)
    (x : Fin (n + 1) → A) :
    Algebra.adjoin K (Set.range x) =
      Algebra.adjoin K
        (Set.range (powerTailCoordinatesFirst F x) ∪ {x 0}) := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Algebra.subset_adjoin (Set.mem_union_right _ rfl)
    · have ht :
          powerTailCoordinatesFirst F x j ∈
            Algebra.adjoin K
              (Set.range (powerTailCoordinatesFirst F x) ∪ {x 0}) :=
        Algebra.subset_adjoin (Set.mem_union_left _ ⟨j, rfl⟩)
      have hx₀ :
          x 0 ∈
            Algebra.adjoin K
              (Set.range (powerTailCoordinatesFirst F x) ∪ {x 0}) :=
        Algebra.subset_adjoin (Set.mem_union_right _ rfl)
      rw [show x j.succ =
          powerTailCoordinatesFirst F x j +
            x 0 ^ powerNormalizationExponent F j.succ by
        simp [powerTailCoordinatesFirst]]
      exact Subalgebra.add_mem _ ht
        (Subalgebra.pow_mem _ hx₀
          (powerNormalizationExponent F j.succ))
  · rw [Algebra.adjoin_le_iff]
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨i, rfl⟩ := hy
      exact adjoin_powerTailCoordinatesFirst_le F x
        (Algebra.subset_adjoin ⟨i, rfl⟩)
    · have hy : y = x 0 := hy
      subst y
      exact Algebra.subset_adjoin ⟨0, rfl⟩

/--
If the retained first coordinate is integral over the canonical power-tail
algebra, then every element generated by the original tuple is integral over
that tail algebra.
-/
theorem isIntegral_of_mem_adjoin_range_powerFirst
    {A : Type*} [CommRing A] [Algebra K A]
    (F : MvPolynomial (Fin (n + 1)) K)
    (x : Fin (n + 1) → A)
    (hfirst :
      IsIntegral
        (Algebra.adjoin K (Set.range (powerTailCoordinatesFirst F x)))
        (x 0)) :
    ∀ y ∈ Algebra.adjoin K (Set.range x),
      IsIntegral
        (Algebra.adjoin K (Set.range (powerTailCoordinatesFirst F x))) y := by
  let t : Fin n → A := powerTailCoordinatesFirst F x
  let S : Subalgebra K A := Algebra.adjoin K (Set.range t)
  have hfirst' : IsIntegral S (x 0) := hfirst
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      refine Fin.cases hfirst' (fun j => ?_) i
      have ht_mem : t j ∈ S := Algebra.subset_adjoin ⟨j, rfl⟩
      have ht : IsIntegral S (t j) := by
        change IsIntegral S ((algebraMap S A) ⟨t j, ht_mem⟩)
        exact isIntegral_algebraMap
      rw [show x j.succ =
          t j + x 0 ^ powerNormalizationExponent F j.succ by
        simp [t, powerTailCoordinatesFirst]]
      exact ht.add (hfirst'.pow _)
  | algebraMap a =>
      have ha_mem : algebraMap K A a ∈ S :=
        Subalgebra.algebraMap_mem S a
      change IsIntegral S ((algebraMap S A) ⟨algebraMap K A a, ha_mem⟩)
      exact isIntegral_algebraMap
  | add a b ha hb hia hib =>
      exact hia.add hib
  | mul a b ha hb hia hib =>
      exact hia.mul hib

/--
Existential form of `powerCoordinatesFirst_isIntegral`, exposing the powers
assigned to the `n` tail coordinates.
-/
theorem exists_powerCoordinatesFirst_isIntegral
    {A : Type*} [CommRing A] [Algebra K A]
    (x : Fin (n + 1) → A) {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F ≠ 0) (hrel : aeval x F = 0) :
    ∃ m : Fin n → ℕ,
      IsIntegral
        (Algebra.adjoin K
          (Set.range fun i =>
            x i.succ - x 0 ^ m i)) (x 0) := by
  refine ⟨fun i => powerNormalizationExponent F i.succ, ?_⟩
  change
    IsIntegral
      (Algebra.adjoin K (Set.range (powerTailCoordinatesFirst F x))) (x 0)
  exact powerCoordinatesFirst_isIntegral x hF hrel

/--
One arbitrary-field generator-reducing step.  It exposes the chosen power
family and returns both the generating equality and integrality of the whole
old generated algebra over the new `n`-element tail algebra.
-/
theorem exists_generatorReducing_powerTail
    {A : Type*} [CommRing A] [Algebra K A]
    (x : Fin (n + 1) → A) {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F ≠ 0) (hrel : aeval x F = 0) :
    ∃ m : Fin n → ℕ,
      let t : Fin n → A := fun i => x i.succ - x 0 ^ m i
      Algebra.adjoin K (Set.range t) ≤ Algebra.adjoin K (Set.range x) ∧
        Algebra.adjoin K (Set.range x) =
          Algebra.adjoin K (Set.range t ∪ {x 0}) ∧
        ∀ y ∈ Algebra.adjoin K (Set.range x),
          IsIntegral (Algebra.adjoin K (Set.range t)) y := by
  let m : Fin n → ℕ := fun i => powerNormalizationExponent F i.succ
  refine ⟨m, ?_, ?_, ?_⟩
  · change
      Algebra.adjoin K (Set.range (powerTailCoordinatesFirst F x)) ≤
        Algebra.adjoin K (Set.range x)
    exact adjoin_powerTailCoordinatesFirst_le F x
  · change
      Algebra.adjoin K (Set.range x) =
        Algebra.adjoin K
          (Set.range (powerTailCoordinatesFirst F x) ∪ {x 0})
    exact adjoin_range_eq_adjoin_powerTailCoordinatesFirst_union F x
  · change
      ∀ y ∈ Algebra.adjoin K (Set.range x),
        IsIntegral
          (Algebra.adjoin K (Set.range (powerTailCoordinatesFirst F x))) y
    exact isIntegral_of_mem_adjoin_range_powerFirst F x
      (powerCoordinatesFirst_isIntegral x hF hrel)

end Chapter06
end FieldArithmetic
