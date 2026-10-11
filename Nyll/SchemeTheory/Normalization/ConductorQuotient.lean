/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The normalization quotient of an affine curve

Fried--Jarden, Lemma 6.3.1 states that, for an affine integral curve
`R = K[x, y]` with function field `F` and normalization `S` in `F`, the
quotient `S / R` is finite-dimensional over `K`.

This file develops the conductor and finite-dimensional quotient argument
used in the proof.  The general theorem that normalization of a one-dimensional
affine algebra over an arbitrary field is module-finite is kept as the next
source-producing frontier; mathlib's current integral-closure finiteness
theorem assumes a finite separable extension.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace NormalizationQuotient

open scoped nonZeroDivisors Pointwise TensorProduct

universe u v w

variable (K : Type u) (R : Type v) (F : Type w)
variable [Field K] [CommRing R] [IsDomain R] [Field F]
variable [Algebra K R] [Algebra R F] [Algebra K F]
variable [IsScalarTower K R F] [IsFractionRing R F]

/-- The normalization of `R` in its chosen fraction field `F`. -/
abbrev Normalization := integralClosure R F

/-- The copy of `R` inside its normalization, as an `R`-submodule. -/
def baseSubmoduleR : Submodule R (Normalization R F) :=
  LinearMap.range (Algebra.linearMap R (Normalization R F))

/-- The copy of `R` inside its normalization, as a `K`-subspace. -/
def baseSubmodule : Submodule K (Normalization R F) :=
  (baseSubmoduleR R F).restrictScalars K

omit [IsDomain R] [IsFractionRing R F] in
theorem mem_baseSubmodule_iff (s : Normalization R F) :
    s ∈ baseSubmodule K R F ↔
      ∃ r : R, algebraMap R (Normalization R F) r = s :=
  Iff.rfl

/-- The quotient of the normalization by the original affine ring. -/
abbrev Quotient :=
  Normalization R F ⧸ baseSubmodule K R F

/--
Elements of the normalization which a fixed element `z : R` sends back
into `R`.
-/
def denominatorSubmodule (z : R) :
    Submodule R (Normalization R F) :=
  (baseSubmoduleR R F).comap
    (Algebra.lmul R (Normalization R F) (algebraMap R (Normalization R F) z))

omit [IsDomain R] [IsFractionRing R F] in
@[simp]
theorem mem_denominatorSubmodule_iff (z : R) (s : Normalization R F) :
    s ∈ denominatorSubmodule R F z ↔
      algebraMap R (Normalization R F) z * s ∈ baseSubmoduleR R F :=
  Iff.rfl

/--
A finite `R`-module contained in the fraction field admits a single nonzero
common denominator.  Applied to the normalization, this is the conductor
element `z` in the proof of Fried--Jarden, Lemma 6.3.1.
-/
theorem exists_nonzero_commonDenominator
    [Module.Finite R (Normalization R F)] :
    ∃ z : R, z ≠ 0 ∧ denominatorSubmodule R F z = ⊤ := by
  classical
  obtain ⟨n, g, hg⟩ :=
    Module.Finite.exists_fin
      (R := R) (M := Normalization R F)
  choose a b hab using fun i : Fin n =>
    IsLocalization.exists_mk'_eq (nonZeroDivisors R) (g i : F)
  let z : R := ∏ i, (b i : R)
  refine ⟨z, ?_, ?_⟩
  · dsimp [z]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      mem_nonZeroDivisors_iff_ne_zero.mp (b i).property
  · apply top_unique
    rw [← hg]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change
      algebraMap R (Normalization R F) z * g i ∈
        baseSubmoduleR R F
    let c : R := ∏ j ∈ Finset.univ.erase i, (b j : R)
    have hz : z = (b i : R) * c := by
      dsimp [z, c]
      exact (Finset.mul_prod_erase Finset.univ
        (fun j => (b j : R)) (Finset.mem_univ i)).symm
    have hden :
        algebraMap R F (b i : R) * (g i : F) =
          algebraMap R F (a i) := by
      rw [← hab i]
      exact
        IsLocalization.mk'_spec'
          (S := F) (M := nonZeroDivisors R) (a i) (b i)
    refine ⟨c * a i, ?_⟩
    apply Subtype.ext
    change
      algebraMap R F (c * a i) =
        algebraMap R F z * (g i : F)
    rw [hz, map_mul, map_mul]
    calc
      algebraMap R F c * algebraMap R F (a i) =
          algebraMap R F c *
            (algebraMap R F (b i : R) * (g i : F)) := by rw [hden]
      _ = (algebraMap R F (b i : R) * algebraMap R F c) *
            (g i : F) := by ring

omit [IsDomain R] in
/-- The original domain embeds into its normalization. -/
theorem algebraMap_normalization_injective :
    Function.Injective (algebraMap R (Normalization R F)) := by
  intro x y hxy
  apply IsFractionRing.injective R F
  exact congrArg Subtype.val hxy

/-- The algebra map identifies `R` with its image in the normalization. -/
def baseEmbeddingEquiv :
    R ≃ₗ[R] baseSubmoduleR R F :=
  LinearEquiv.ofBijective
    (Algebra.linearMap R (Normalization R F)).rangeRestrict
    ⟨by
      intro x y hxy
      apply algebraMap_normalization_injective R F
      exact congrArg Subtype.val hxy,
      LinearMap.surjective_rangeRestrict _⟩

/--
Multiplication by a common denominator, with codomain restricted back to
`R`.
-/
def commonDenominatorMap (z : R)
    (hz : denominatorSubmodule R F z = ⊤) :
    Normalization R F →ₗ[R] R :=
  (baseEmbeddingEquiv R F).symm.toLinearMap.comp <|
    (Algebra.lmul R (Normalization R F)
      (algebraMap R (Normalization R F) z)).codRestrict
      (baseSubmoduleR R F) fun s => by
        change s ∈ denominatorSubmodule R F z
        rw [hz]
        exact Submodule.mem_top

omit [IsDomain R] in
theorem algebraMap_commonDenominatorMap
    (z : R) (hz : denominatorSubmodule R F z = ⊤)
    (s : Normalization R F) :
    algebraMap R (Normalization R F) (commonDenominatorMap R F z hz s) =
      algebraMap R (Normalization R F) z * s := by
  let t : baseSubmoduleR R F :=
    ⟨algebraMap R (Normalization R F) z * s, by
      change s ∈ denominatorSubmodule R F z
      rw [hz]
      exact Submodule.mem_top⟩
  have ht := (baseEmbeddingEquiv R F).apply_symm_apply t
  exact congrArg Subtype.val ht

omit [IsDomain R] in
theorem commonDenominatorMap_algebraMap
    (z r : R) (hz : denominatorSubmodule R F z = ⊤) :
    commonDenominatorMap R F z hz
        (algebraMap R (Normalization R F) r) = z * r := by
  apply algebraMap_normalization_injective R F
  rw [algebraMap_commonDenominatorMap]
  exact (map_mul (algebraMap R (Normalization R F)) z r).symm

theorem commonDenominatorMap_injective
    {z : R} (hz0 : z ≠ 0)
    (hz : denominatorSubmodule R F z = ⊤) :
    Function.Injective (commonDenominatorMap R F z hz) := by
  intro s t hst
  have hzS :
      algebraMap R (Normalization R F) z ≠ 0 :=
    by simpa using (algebraMap_normalization_injective R F).ne hz0
  apply mul_left_cancel₀ hzS
  calc
    algebraMap R (Normalization R F) z * s =
        algebraMap R (Normalization R F)
          (commonDenominatorMap R F z hz s) :=
      (algebraMap_commonDenominatorMap R F z hz s).symm
    _ = algebraMap R (Normalization R F)
          (commonDenominatorMap R F z hz t) := by rw [hst]
    _ = algebraMap R (Normalization R F) z * t :=
      algebraMap_commonDenominatorMap R F z hz t

/-- The common-denominator map, viewed over the constant field. -/
def commonDenominatorMapK (z : R)
    (hz : denominatorSubmodule R F z = ⊤) :
    Normalization R F →ₗ[K] R :=
  (commonDenominatorMap R F z hz).restrictScalars K

omit [IsDomain R] in
@[simp]
theorem commonDenominatorMapK_apply
    (z : R) (hz : denominatorSubmodule R F z = ⊤)
    (s : Normalization R F) :
    commonDenominatorMapK K R F z hz s =
      commonDenominatorMap R F z hz s :=
  rfl

/-- The principal `K`-subspace `zR` of `R`. -/
def principalSubmodule (z : R) : Submodule K R :=
  (z • (⊤ : Submodule R R)).restrictScalars K

omit [IsDomain R] [Algebra R F] [IsScalarTower K R F]
  [IsFractionRing R F] in
theorem mem_principalSubmodule_iff (z r : R) :
    r ∈ principalSubmodule K R z ↔ ∃ a : R, z * a = r := by
  change r ∈ z • (⊤ : Submodule R R) ↔ ∃ a : R, z * a = r
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, smul_eq_mul]

/-- The vector-space quotient `R / zR`. -/
abbrev PrincipalQuotient (z : R) :=
  R ⧸ principalSubmodule K R z

omit [IsDomain R] in
/-- Multiplication by the conductor sends the embedded copy of `R` into `zR`. -/
theorem commonDenominatorMap_maps_base
    (z : R) (hz : denominatorSubmodule R F z = ⊤) :
    baseSubmodule K R F ≤
      (principalSubmodule K R z).comap
        (commonDenominatorMapK K R F z hz) := by
  intro s hs
  obtain ⟨r, hr⟩ :
      ∃ r : R, algebraMap R (Normalization R F) r = s :=
    (mem_baseSubmodule_iff K R F s).mp hs
  have heq :
      commonDenominatorMapK K R F z hz
          (algebraMap R (Normalization R F) r) = z * r :=
    commonDenominatorMap_algebraMap R F z r hz
  have hmem : z * r ∈ principalSubmodule K R z :=
    (mem_principalSubmodule_iff K R z (z * r)).mpr ⟨r, rfl⟩
  have hbase :
      commonDenominatorMapK K R F z hz
          (algebraMap R (Normalization R F) r) ∈
        principalSubmodule K R z :=
    heq.symm ▸ hmem
  change commonDenominatorMapK K R F z hz s ∈
    principalSubmodule K R z
  exact congrArg (commonDenominatorMapK K R F z hz) hr ▸ hbase

/--
The injection `S/R → R/zR` from the proof of Fried--Jarden, Lemma 6.3.1.
It sends the class of `s` to the class of `zs`.
-/
def quotientToPrincipal (z : R)
    (hz : denominatorSubmodule R F z = ⊤) :
    Quotient K R F →ₗ[K] PrincipalQuotient K R z :=
  Submodule.mapQ
    (baseSubmodule K R F)
    (principalSubmodule K R z)
    (commonDenominatorMapK K R F z hz)
    (commonDenominatorMap_maps_base K R F z hz)

omit [IsDomain R] in
@[simp]
theorem quotientToPrincipal_mk
    (z : R) (hz : denominatorSubmodule R F z = ⊤)
    (s : Normalization R F) :
    quotientToPrincipal K R F z hz
        (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk (commonDenominatorMap R F z hz s) :=
  by simp [quotientToPrincipal]

theorem quotientToPrincipal_injective
    {z : R} (hz0 : z ≠ 0)
    (hz : denominatorSubmodule R F z = ⊤) :
    Function.Injective (quotientToPrincipal K R F z hz) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  change quotientToPrincipal K R F z hz q = 0 at hq
  obtain ⟨s, rfl⟩ :=
    Submodule.Quotient.mk_surjective (baseSubmodule K R F) q
  rw [quotientToPrincipal_mk,
    Submodule.Quotient.mk_eq_zero] at hq
  change
    commonDenominatorMap R F z hz s ∈
      z • (⊤ : Submodule R R) at hq
  rw [Submodule.mem_smul_pointwise_iff_exists] at hq
  obtain ⟨r, -, hr⟩ := hq
  rw [Submodule.Quotient.mk_eq_zero]
  change s ∈ baseSubmoduleR R F
  refine ⟨r, ?_⟩
  have hzS :
      algebraMap R (Normalization R F) z ≠ 0 := by
    simpa using (algebraMap_normalization_injective R F).ne hz0
  apply mul_left_cancel₀ hzS
  calc
    algebraMap R (Normalization R F) z *
        algebraMap R (Normalization R F) r =
      algebraMap R (Normalization R F) (z * r) := by
        rw [map_mul]
    _ = algebraMap R (Normalization R F)
        (commonDenominatorMap R F z hz s) := by
          rw [← hr]
          rfl
    _ = algebraMap R (Normalization R F) z * s :=
      algebraMap_commonDenominatorMap R F z hz s

section PolynomialNormalization

variable [Algebra (Polynomial K) R]
variable [IsScalarTower K (Polynomial K) R]
variable [Algebra.IsIntegral (Polynomial K) R]

omit [Algebra K R] [IsScalarTower K (Polynomial K) R] in
/--
In an integral domain integral over `K[X]`, every nonzero principal ideal
contains a nonzero polynomial from `K[X]`.

This is the source of the polynomial `g(x) ∈ zR` in the proof of
Fried--Jarden, Lemma 6.3.1.
-/
theorem exists_nonzero_polynomial_multiple
    (z : R) (hz : z ≠ 0) :
    ∃ g : Polynomial K, g ≠ 0 ∧
      ∃ r : R, algebraMap (Polynomial K) R g = z * r := by
  let I : Ideal R := Ideal.span ({z} : Set R)
  have hI : I ≠ ⊥ := by
    intro hbot
    have hzmem : z ∈ I :=
      Ideal.mem_span_singleton_self z
    rw [hbot] at hzmem
    exact hz (by simpa using hzmem)
  have hcomap :
      I.comap (algebraMap (Polynomial K) R) ≠ ⊥ :=
    Ideal.IsIntegral.under_ne_bot (Polynomial K) hI
  obtain ⟨g, hgmem, hg0⟩ :=
    (I.comap (algebraMap (Polynomial K) R)).ne_bot_iff.mp hcomap
  refine ⟨g, hg0, ?_⟩
  change algebraMap (Polynomial K) R g ∈ I at hgmem
  obtain ⟨r, hr⟩ :=
    Ideal.mem_span_singleton'.mp hgmem
  exact ⟨r, by simpa [mul_comm] using hr.symm⟩

omit [Algebra K R] [IsScalarTower K (Polynomial K) R] in
/--
The polynomial in a nonzero principal ideal may be chosen monic.
-/
theorem exists_monic_polynomial_multiple
    (z : R) (hz : z ≠ 0) :
    ∃ q : Polynomial K, q.Monic ∧
      ∃ r : R, algebraMap (Polynomial K) R q = z * r := by
  classical
  obtain ⟨g, hg0, r, hr⟩ :=
    exists_nonzero_polynomial_multiple K R z hz
  refine ⟨normalize g, Polynomial.monic_normalize hg0,
    algebraMap (Polynomial K) R (normUnit g : Polynomial K) * r, ?_⟩
  rw [normalize_apply, map_mul, hr]
  ring

omit [IsDomain R] [Algebra.IsIntegral (Polynomial K) R] in
/--
Reduction modulo a monic polynomial of `K[X]` makes every finite
`K[X]`-module finite-dimensional over `K`.
-/
theorem quotSMulTop_finite_of_monic
    [Module.Finite (Polynomial K) R]
    (q : Polynomial K) (hq : q.Monic) :
    Module.Finite K (QuotSMulTop q R) := by
  let Q := Polynomial K ⧸ Ideal.span ({q} : Set (Polynomial K))
  let T := Q ⊗[Polynomial K] R
  let : Module.Finite K Q :=
    hq.finite_quotient
  let : Module.Finite Q T := by
    infer_instance
  let : Module.Finite K T :=
    Module.Finite.trans Q T
  exact
    Module.Finite.equiv
      ((QuotSMulTop.equivQuotTensor q R).restrictScalars K).symm

/--
For a finite integral `K[X]`-domain, quotienting by a nonzero element is
finite-dimensional over `K`.
-/
theorem principalQuotient_finite
    [Module.Finite (Polynomial K) R]
    (z : R) (hz : z ≠ 0) :
    Module.Finite K (PrincipalQuotient K R z) := by
  classical
  obtain ⟨q, hq, r₀, hqz⟩ :=
    exists_monic_polynomial_multiple K R z hz
  let P : Submodule (Polynomial K) R :=
    q • (⊤ : Submodule (Polynomial K) R)
  have hle :
      P.restrictScalars K ≤ principalSubmodule K R z := by
    intro x hx
    have hxP : x ∈ P := hx
    change x ∈ q • (⊤ : Submodule (Polynomial K) R) at hxP
    rw [Submodule.mem_smul_pointwise_iff_exists] at hxP
    obtain ⟨a, -, ha⟩ := hxP
    apply (mem_principalSubmodule_iff K R z x).mpr
    refine ⟨r₀ * a, ?_⟩
    calc
      z * (r₀ * a) = (z * r₀) * a := by ring
      _ = algebraMap (Polynomial K) R q * a := by rw [hqz]
      _ = q • a := by rw [Algebra.smul_def]
      _ = x := ha
  let f :
      (R ⧸ P.restrictScalars K) →ₗ[K]
        PrincipalQuotient K R z :=
    Submodule.mapQ
      (P.restrictScalars K)
      (principalSubmodule K R z)
      LinearMap.id hle
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ :=
      Submodule.Quotient.mk_surjective
        (principalSubmodule K R z) y
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    simp [f]
  let e :
      (R ⧸ P.restrictScalars K) ≃ₗ[K] QuotSMulTop q R := by
    simpa [P] using
      Submodule.Quotient.restrictScalarsEquiv K P
  let g :
      QuotSMulTop q R →ₗ[K] PrincipalQuotient K R z :=
    f.comp e.symm.toLinearMap
  have hg : Function.Surjective g :=
    hf.comp e.symm.surjective
  let : Module.Finite K (QuotSMulTop q R) :=
    quotSMulTop_finite_of_monic K R q hq
  exact Module.Finite.of_surjective g hg

end PolynomialNormalization

section FiniteNormalization

variable [Algebra (Polynomial K) R]
variable [IsScalarTower K (Polynomial K) R]
variable [Module.Finite (Polynomial K) R]
variable [Module.Finite R (Normalization R F)]

/--
The complete conductor argument of Fried--Jarden, Lemma 6.3.1, from
module-finiteness of the normalization.

The separate normalization-finiteness input is exactly the classical theorem
cited in the first sentence of the printed proof.
-/
theorem normalizationQuotient_finite_of_normalization_finite :
    Module.Finite K (Quotient K R F) := by
  let : Algebra.IsIntegral (Polynomial K) R :=
    Algebra.IsIntegral.of_finite (Polynomial K) R
  obtain ⟨z, hz0, hz⟩ :=
    exists_nonzero_commonDenominator R F
  let : Module.Finite K (PrincipalQuotient K R z) :=
    principalQuotient_finite K R z hz0
  exact
    FiniteDimensional.of_injective
      (quotientToPrincipal K R F z hz)
      (quotientToPrincipal_injective K R F hz0 hz)

end FiniteNormalization

end NormalizationQuotient
end Chapter06
end FieldArithmetic
