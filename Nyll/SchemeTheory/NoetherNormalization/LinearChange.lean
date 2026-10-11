/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.NoetherNormalization.Nonvanishing

/-!
# Linear changes of variables for Noether normalization

This file formalizes the triangular linear substitution used in
Fried--Jarden, Lemma 22.5.1.  It fixes the first variable and sends each
remaining variable `Xᵢ` to `Xᵢ + cᵢ X₀`.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06

open MvPolynomial

variable {K : Type*} [Field K]

/--
The triangular linear substitution fixing `X₀` and sending
`Xᵢ₊₁` to `Xᵢ₊₁ + cᵢ X₀`.
-/
def linearChangeFirst {n : ℕ} (c : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  aeval fun i => Fin.cases (X 0) (fun j => X j.succ + C (c j) * X 0) i

@[simp]
theorem linearChangeFirst_X_zero {n : ℕ} (c : Fin n → K) :
    linearChangeFirst c (X 0) = X 0 := by
  simp [linearChangeFirst]

@[simp]
theorem linearChangeFirst_X_succ {n : ℕ} (c : Fin n → K) (i : Fin n) :
    linearChangeFirst c (X i.succ) = X i.succ + C (c i) * X 0 := by
  simp [linearChangeFirst]

theorem linearChangeFirst_comp_neg {n : ℕ} (c : Fin n → K) :
    (linearChangeFirst c).comp (linearChangeFirst (-c)) =
      AlgHom.id K (MvPolynomial (Fin (n + 1)) K) := by
  simp only [linearChangeFirst]
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp

/-- The triangular linear substitution as an algebra equivalence. -/
def linearChangeFirstEquiv {n : ℕ} (c : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  AlgEquiv.ofAlgHom (linearChangeFirst c) (linearChangeFirst (-c))
    (linearChangeFirst_comp_neg c)
    (by simpa using linearChangeFirst_comp_neg (-c))

theorem linearChangeFirst_isHomogeneous {n d : ℕ} (c : Fin n → K)
    {F : MvPolynomial (Fin (n + 1)) K} (hF : F.IsHomogeneous d) :
    (linearChangeFirst c F).IsHomogeneous d := by
  let y : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K :=
    fun i => Fin.cases (X 0) (fun j => X j.succ + C (c j) * X 0) i
  change (aeval y F).IsHomogeneous d
  have hsub : ∀ i, (y i).IsHomogeneous 1 := by
    intro i
    dsimp only [y]
    refine Fin.cases ?_ ?_ i
    · exact isHomogeneous_X K 0
    · intro j
      exact (isHomogeneous_X K j.succ).add
        (isHomogeneous_C_mul_X (c j) 0)
  simpa only [one_mul] using hF.aeval y hsub

/--
Evaluating the triangular transform at `(1, 0, ..., 0)` is the same as
evaluating the original polynomial at `(1, c₁, ..., cₙ)`.
-/
theorem eval_linearChangeFirst_finCons_one_zero {n : ℕ} (c : Fin n → K)
    (F : MvPolynomial (Fin (n + 1)) K) :
    eval (Fin.cons 1 0) (linearChangeFirst c F) = eval (Fin.cons 1 c) F := by
  simp only [linearChangeFirst, aeval_def, MvPolynomial.algebraMap_eq]
  rw [← eval_assoc]
  refine congrArg (fun z : Fin (n + 1) → K => eval z F) ?_
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp

/--
Evaluation through `finSuccEquiv`: the first multivariable coordinate becomes
the univariate polynomial variable and the remaining coordinates evaluate the
coefficients.
-/
theorem aeval_finCons_eq_eval₂_finSuccEquiv
    {A : Type*} [CommRing A] [Algebra K A] {n : ℕ}
    (x₀ : A) (x : Fin n → A) (F : MvPolynomial (Fin (n + 1)) K) :
    aeval (Fin.cons x₀ x) F =
      Polynomial.eval₂ (aeval x).toRingHom x₀ (finSuccEquiv K n F) := by
  let φ : Polynomial (MvPolynomial (Fin n) K) →ₐ[K] A :=
    Polynomial.eval₂AlgHom (aeval x) x₀ (fun _ => Commute.all _ _)
  change aeval (Fin.cons x₀ x) F =
    (φ.comp (finSuccEquiv K n).toAlgHom) F
  congr 1
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_iff_succ]
  simp [φ, finSuccEquiv_X_zero, finSuccEquiv_X_succ]

/-- The `n` tail coordinates after the inverse triangular change. -/
def linearTailCoordinatesFirst
    {A : Type*} [CommRing A] [Algebra K A] {n : ℕ}
    (c : Fin n → K) (x : Fin (n + 1) → A) : Fin n → A :=
  fun i => x i.succ - algebraMap K A (c i) * x 0

/-- The full tuple after the inverse triangular change. -/
def linearCoordinatesFirst
    {A : Type*} [CommRing A] [Algebra K A] {n : ℕ}
    (c : Fin n → K) (x : Fin (n + 1) → A) : Fin (n + 1) → A :=
  Fin.cons (x 0) (linearTailCoordinatesFirst c x)

@[simp]
theorem linearCoordinatesFirst_zero
    {A : Type*} [CommRing A] [Algebra K A] {n : ℕ}
    (c : Fin n → K) (x : Fin (n + 1) → A) :
    linearCoordinatesFirst c x 0 = x 0 := rfl

@[simp]
theorem linearCoordinatesFirst_succ
    {A : Type*} [CommRing A] [Algebra K A] {n : ℕ}
    (c : Fin n → K) (x : Fin (n + 1) → A) (i : Fin n) :
    linearCoordinatesFirst c x i.succ =
      x i.succ - algebraMap K A (c i) * x 0 := rfl

/--
The triangular substitution evaluated at its inverse coordinate change
recovers evaluation at the original tuple.
-/
theorem aeval_linearChangeFirst_linearCoordinates
    {A : Type*} [CommRing A] [Algebra K A] {n : ℕ}
    (c : Fin n → K) (x : Fin (n + 1) → A)
    (F : MvPolynomial (Fin (n + 1)) K) :
    aeval (linearCoordinatesFirst c x) (linearChangeFirst c F) = aeval x F := by
  simp only [linearChangeFirst]
  rw [comp_aeval_apply]
  have hpoints :
      (fun i : Fin (n + 1) =>
        (aeval (linearCoordinatesFirst c x) :
          MvPolynomial (Fin (n + 1)) K →ₐ[K] A)
          (Fin.cases (X 0) (fun j => X j.succ + C (c j) * X 0) i)) = x := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      simp
  rw [hpoints]

/--
For a homogeneous polynomial, evaluation at `(1, 0, ..., 0)` extracts the
constant coefficient of its coefficient of `X₀ᵈ`.
-/
theorem eval_finCons_one_zero_eq_constantCoeff_coeff {n d : ℕ}
    {F : MvPolynomial (Fin (n + 1)) K} (hF : F.IsHomogeneous d) :
    eval (Fin.cons 1 0) F =
      MvPolynomial.constantCoeff ((finSuccEquiv K n F).coeff d) := by
  by_cases hF₀ : F = 0
  · subst F
    simp
  have hdeg : (finSuccEquiv K n F).natDegree < d + 1 := by
    linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDegree F 0,
      hF.totalDegree hF₀]
  have aux :
      ∀ i ∈ Finset.range d,
        MvPolynomial.constantCoeff ((finSuccEquiv K n F).coeff i) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply (hF.finSuccEquiv_coeff_isHomogeneous i (d - i) (by omega)).coeff_eq_zero
    simp only [map_zero]
    rw [← Nat.sub_ne_zero_iff_lt] at hi
    exact hi.symm
  simp_rw [eval_eq_eval_mv_eval', Polynomial.eval_one_map,
    Polynomial.eval_eq_sum_range' hdeg, MvPolynomial.eval_zero, one_pow, mul_one,
    map_sum, Finset.sum_range_succ,
    Finset.sum_eq_zero aux, zero_add]

/--
The coefficient of `X₀ᵈ` after the triangular substitution of a degree-`d`
homogeneous polynomial is the scalar obtained by evaluating it at
`(1, c₁, ..., cₙ)`.
-/
theorem coeff_finSuccEquiv_linearChangeFirst {n d : ℕ} (c : Fin n → K)
    {F : MvPolynomial (Fin (n + 1)) K} (hF : F.IsHomogeneous d) :
    (finSuccEquiv K n (linearChangeFirst c F)).coeff d =
      C (eval (Fin.cons 1 c) F) := by
  have hG : (linearChangeFirst c F).IsHomogeneous d :=
    linearChangeFirst_isHomogeneous c hF
  have hcoeff :
      ((finSuccEquiv K n (linearChangeFirst c F)).coeff d).IsHomogeneous 0 :=
    hG.finSuccEquiv_coeff_isHomogeneous d 0 (add_zero d)
  have hdegree :
      ((finSuccEquiv K n (linearChangeFirst c F)).coeff d).totalDegree = 0 :=
    (totalDegree_zero_iff_isHomogeneous (Fin n)).mpr hcoeff
  rw [totalDegree_eq_zero_iff_eq_C.mp hdegree]
  congr 1
  change MvPolynomial.constantCoeff
      ((finSuccEquiv K n (linearChangeFirst c F)).coeff d) =
        eval (Fin.cons 1 c) F
  rw [← eval_finCons_one_zero_eq_constantCoeff_coeff hG]
  exact eval_linearChangeFirst_finCons_one_zero c F

/--
A coefficient whose distinguished-variable exponent is larger than the
homogeneous degree vanishes.
-/
theorem coeff_finSuccEquiv_eq_zero_of_isHomogeneous_lt {n i j : ℕ}
    {F : MvPolynomial (Fin (n + 1)) K} (hF : F.IsHomogeneous i) (hij : i < j) :
    (finSuccEquiv K n F).coeff j = 0 := by
  ext m
  rw [AddMonoidAlgebra.coeff_zero, finSuccEquiv_coeff_coeff]
  apply hF.coeff_eq_zero
  rw [Finsupp.degree_eq_weight_one]
  simp only [Finsupp.weight_apply, smul_eq_mul, mul_one, Finsupp.sum_cons]
  have htail_degree :
      m.sum (fun _ e => e) = m.degree := by
    rfl
  rw [htail_degree]
  omega

/-- The top homogeneous component of a nonzero polynomial is nonzero. -/
theorem homogeneousComponent_totalDegree_ne_zero {σ : Type*}
    {F : MvPolynomial σ K} (hF : F ≠ 0) :
    homogeneousComponent F.totalDegree F ≠ 0 := by
  classical
  have hs : F.support.Nonempty := support_nonempty.mpr hF
  obtain ⟨m, hm, hdegree⟩ :=
    Finset.sup_mem_of_nonempty (f := fun m : σ →₀ ℕ => m.sum fun _ e => e) hs
  have hmdegree : m.degree = F.totalDegree := by
    exact hdegree
  intro hzero
  have hcoeff := congrArg (fun P : MvPolynomial σ K => P.coeff m) hzero
  rw [coeff_homogeneousComponent, ite_eq_left hmdegree, AddMonoidAlgebra.coeff_zero] at hcoeff
  exact (mem_support_iff.mp hm) hcoeff

/--
At the top total degree, the transformed polynomial and the transform of its
top homogeneous component have the same `X₀` coefficient.
-/
theorem coeff_finSuccEquiv_linearChangeFirst_eq_top {n : ℕ}
    (c : Fin n → K) (F : MvPolynomial (Fin (n + 1)) K) :
    (finSuccEquiv K n (linearChangeFirst c F)).coeff F.totalDegree =
      (finSuccEquiv K n
        (linearChangeFirst c (homogeneousComponent F.totalDegree F))).coeff F.totalDegree := by
  let d := F.totalDegree
  have hsum :
      (∑ i ∈ Finset.range (d + 1), homogeneousComponent i F) = F := by
    simpa only [d] using sum_homogeneousComponent (φ := F)
  change (finSuccEquiv K n (linearChangeFirst c F)).coeff d =
    (finSuccEquiv K n (linearChangeFirst c (homogeneousComponent d F))).coeff d
  calc
    _ = (finSuccEquiv K n (linearChangeFirst c
        (∑ i ∈ Finset.range (d + 1), homogeneousComponent i F))).coeff d := by
      rw [hsum]
    _ = _ := by
      have hlower :
          (∑ i ∈ Finset.range d,
            (finSuccEquiv K n
              (linearChangeFirst c (homogeneousComponent i F))).coeff d) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply coeff_finSuccEquiv_eq_zero_of_isHomogeneous_lt
          (linearChangeFirst_isHomogeneous c (homogeneousComponent_isHomogeneous i F))
        exact Finset.mem_range.mp hi
      rw [Finset.sum_range_succ]
      simp only [map_add, Polynomial.coeff_add, map_sum, Polynomial.finsetSum_coeff]
      rw [hlower, zero_add]

/-- Coefficients above total degree remain zero after the linear change. -/
theorem coeff_finSuccEquiv_linearChangeFirst_eq_zero_of_totalDegree_lt {n j : ℕ}
    (c : Fin n → K) (F : MvPolynomial (Fin (n + 1)) K) (hj : F.totalDegree < j) :
    (finSuccEquiv K n (linearChangeFirst c F)).coeff j = 0 := by
  let d := F.totalDegree
  have hsum :
      (∑ i ∈ Finset.range (d + 1), homogeneousComponent i F) = F := by
    simpa only [d] using sum_homogeneousComponent (φ := F)
  rw [← hsum]
  simp only [map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  apply coeff_finSuccEquiv_eq_zero_of_isHomogeneous_lt
    (linearChangeFirst_isHomogeneous c (homogeneousComponent_isHomogeneous i F))
  have hi : i < d + 1 := Finset.mem_range.mp hi
  dsimp only [d] at hi
  omega

/--
Over an infinite field, a nonzero homogeneous polynomial admits a triangular
linear change for which its `X₀ᵈ` coefficient is a unit.
-/
theorem exists_linearChangeFirst_coeff_isUnit [Infinite K]
    {n d : ℕ} {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F.IsHomogeneous d) (hF₀ : F ≠ 0) :
    ∃ c : Fin n → K,
      IsUnit ((finSuccEquiv K n (linearChangeFirst c F)).coeff d) := by
  obtain ⟨c, hc⟩ := exists_eval_finCons_one_ne_zero hF hF₀
  refine ⟨c, ?_⟩
  rw [coeff_finSuccEquiv_linearChangeFirst c hF]
  exact hc.isUnit.map MvPolynomial.C

/--
Over an infinite field, every nonzero polynomial admits a triangular linear
change for which the resulting univariate polynomial in `X₀` has unit leading
coefficient.
-/
theorem exists_linearChangeFirst_leadingCoeff_isUnit [Infinite K]
    {n : ℕ} {F : MvPolynomial (Fin (n + 1)) K} (hF : F ≠ 0) :
    ∃ c : Fin n → K,
      IsUnit (finSuccEquiv K n (linearChangeFirst c F)).leadingCoeff := by
  let H := homogeneousComponent F.totalDegree F
  have hH : H.IsHomogeneous F.totalDegree := homogeneousComponent_isHomogeneous _ _
  have hH₀ : H ≠ 0 := homogeneousComponent_totalDegree_ne_zero hF
  obtain ⟨c, hc⟩ := exists_linearChangeFirst_coeff_isUnit hH hH₀
  refine ⟨c, ?_⟩
  let p := finSuccEquiv K n (linearChangeFirst c F)
  have hcoeff :
      IsUnit (p.coeff F.totalDegree) := by
    rw [show p.coeff F.totalDegree =
      (finSuccEquiv K n (linearChangeFirst c H)).coeff F.totalDegree by
        exact coeff_finSuccEquiv_linearChangeFirst_eq_top c F]
    exact hc
  have hnatDegree : p.natDegree ≤ F.totalDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    exact coeff_finSuccEquiv_linearChangeFirst_eq_zero_of_totalDegree_lt c F hj
  have hnatDegree_eq : p.natDegree = F.totalDegree :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hnatDegree hcoeff.ne_zero
  rw [← hnatDegree_eq, Polynomial.coeff_natDegree] at hcoeff
  exact hcoeff

end Chapter06
end FieldArithmetic
