/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_isPullback_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Projective space under extension of coefficients

The morphism of projective spaces induced by an algebra map is a pullback of
the structural morphism. Polynomial scalar extension identifies the affine
charts and their overlaps.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open HomogeneousLocalization TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace ProjSpace
open _root_.AlgebraicGeometry.ProjSpace
open _root_.AlgebraicGeometry.ProjSpace
open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

section ProjBaseChange

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (n : ℕ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/-- The homomorphism between standard homogeneous localization charts induced by coefficient
    extension. -/
def awayMapX (j : Fin (n + 1)) :
    Away 𝒜R (MvPolynomial.X j) →+* Away 𝒜A (MvPolynomial.X j) :=
  (mvMapGraded_X R A n j ▸
    HomogeneousLocalization.Away.map (mvMapGraded R A n) (MvPolynomial.X j))

theorem awayMapX_mk_aux (j : Fin (n + 1))
    {y : MvPolynomial (Fin (n + 1)) A}
    (h : (mvMapGraded R A n) (MvPolynomial.X j) = y) (hy : y ∈ 𝒜A 1)
    (d : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (hp : p ∈ 𝒜R (d • 1)) :
    (h ▸ Away.map (mvMapGraded R A n) (MvPolynomial.X j))
        (Away.mk 𝒜R (X_mem_one R n j) d p hp)
      = Away.mk 𝒜A hy d ((mvMapGraded R A n) p)
          ((mvMapGraded R A n).map_mem hp) := by
  subst h
  exact Away.map_mk (mvMapGraded R A n) (X j)
    (X_mem_one R n j) d p hp

theorem awayMapX_mk (j : Fin (n + 1)) (d : ℕ)
    (p : MvPolynomial (Fin (n + 1)) R) (hp : p ∈ 𝒜R (d • 1)) :
    awayMapX R A n j
        (Away.mk 𝒜R (X_mem_one R n j) d p hp)
      = Away.mk 𝒜A (X_mem_one A n j) d
          (MvPolynomial.map (algebraMap R A) p)
          ((mem_homogeneousSubmodule _ _).mpr
            (((mem_homogeneousSubmodule _ _).mp hp).map _)) := by
  exact awayMapX_mk_aux R A n j (mvMapGraded_X R A n j)
    (X_mem_one A n j) d p hp

theorem C_mem_zero {S : Type u} [CommRing S] (r : S) :
    (C r : MvPolynomial (Fin (n + 1)) S)
      ∈ homogeneousSubmodule (Fin (n + 1)) S ((0 : ℕ) • 1) := by
  rw [zero_smul]; exact (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_C _ r)

theorem algebraMap_eq_mk_zero {S : Type u} [CommRing S]
    (j : Fin (n + 1)) (r : S) :
    algebraMap S (Away (homogeneousSubmodule (Fin (n + 1)) S) (X j)) r
      = Away.mk _ (X_mem_one S n j) 0 (C r)
          (C_mem_zero n r) := by
  refine HomogeneousLocalization.val_injective (𝒜 := homogeneousSubmodule (Fin (n + 1)) S)
    (Submonoid.powers (X j)) ?_
  rw [val_algebraMap, Away.val_mk, ← Localization.mk_one_eq_algebraMap]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))

theorem awayMapX_algebraMap (j : Fin (n + 1)) :
    (awayMapX R A n j).comp (algebraMap R (Away 𝒜R (X j)))
      = (algebraMap A (Away 𝒜A (X j))).comp (algebraMap R A) := by
  ext r
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_eq_mk_zero n j,
    algebraMap_eq_mk_zero n j (algebraMap R A r), awayMapX_mk,
    Away.val_mk, Away.val_mk, MvPolynomial.map_C]

theorem awayMapX_ratio (j k : Fin (n + 1)) :
    awayMapX R A n j (ratio R n j k)
      = ratio A n j k := by
  rw [ratio, awayMapX_mk, ratio]
  congr 1
  exact MvPolynomial.map_X _ k

section AwayChart

variable {S : Type u} [CommRing S] (j : Fin (n + 1))

local notation "𝒜S" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S

theorem val_aeval_ratio_monomial (d : {k // k ≠ j} →₀ ℕ) (c : S) :
    (MvPolynomial.aeval (R := S) (fun k : {k // k ≠ j} => ratio S n j k.1)
        (MvPolynomial.monomial d c)).val
      = Localization.mk
          (c • ∏ k ∈ d.support, (X k.1 : MvPolynomial (Fin (n + 1)) S) ^ d k)
          (⟨(X j) ^ (∑ k ∈ d.support, d k), ∑ k ∈ d.support, d k, rfl⟩
            : Submonoid.powers (X j : MvPolynomial (Fin (n + 1)) S)) := by
  have hval : (HomogeneousLocalization.val : Away 𝒜S (X j) → _)
      = (algebraMap (Away 𝒜S (X j)) (Localization.Away (X j))) := rfl
  rw [aeval_monomial, Finsupp.prod, hval, map_mul, map_prod]
  simp only [map_pow, ratio, ← hval, Away.val_mk,
    val_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_pow, Localization.mk_prod, Localization.mk_mul]
  congr 1
  · rw [MvPolynomial.smul_eq_C_mul]
  · refine Subtype.ext ?_
    push_cast
    simp only [Finset.prod_pow_eq_pow_sum, pow_one, one_mul]

theorem exponent_inj (N : ℕ) :
    Function.Injective fun d : {k // k ≠ j} →₀ ℕ =>
      d.mapDomain (Subtype.val : {k // k ≠ j} → Fin (n + 1))
        + Finsupp.single j (N - ∑ k ∈ d.support, d k) := by
  intro d d' h
  refine DFunLike.ext _ _ fun k => ?_
  have := DFunLike.congr_fun h k.1
  simp only [Finsupp.add_apply, Finsupp.single_apply, ite_eq_right (Ne.symm k.2), add_zero,
    Finsupp.mapDomain_apply_of_injective Subtype.val_injective] at this
  exact this

theorem aeval_ratio_injective :
    Function.Injective
      (MvPolynomial.aeval (R := S) (fun k : {k // k ≠ j} => ratio S n j k.1)
        : MvPolynomial {k // k ≠ j} S →ₐ[S] Away 𝒜S (X j)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro p hp
  replace hp := congrArg HomogeneousLocalization.val hp
  rw [HomogeneousLocalization.val_zero, MvPolynomial.as_sum p, map_sum,
    show (HomogeneousLocalization.val : Away 𝒜S (X j) → _)
      = (algebraMap (Away 𝒜S (X j)) (Localization.Away (X j))) from rfl, map_sum] at hp
  simp only [← show (HomogeneousLocalization.val : Away 𝒜S (X j) → _)
      = (algebraMap (Away 𝒜S (X j)) (Localization.Away (X j))) from rfl,
    val_aeval_ratio_monomial] at hp
  set N := (p.support.sup fun d => ∑ k ∈ d.support, d k) with hN
  let ι := algebraMap (MvPolynomial (Fin (n + 1)) S)
    (Localization.Away (X j : MvPolynomial (Fin (n + 1)) S))
  have hXcancel : ∀ q : MvPolynomial (Fin (n + 1)) S, X j * q = 0 → q = 0 := fun q hq =>
    (MvPolynomial.X_mul_cancel_left_iff (i := j)).mp (hq.trans (mul_zero _).symm)
  have hι : Function.Injective ι :=
    IsLocalization.injective (M := Submonoid.powers (X j : MvPolynomial (Fin (n+1)) S))
      _ (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff.mpr
        ⟨hXcancel, fun q hq => hXcancel q (mul_comm q _ ▸ hq)⟩))
  have hp' := congrArg (· * ι ((X j)^N)) hp
  simp only [zero_mul, Finset.sum_mul] at hp'
  have hterm : ∀ d ∈ p.support,
      Localization.mk (p.coeff d • ∏ k ∈ d.support, (X k.1 : MvPolynomial _ S) ^ d k)
          (⟨(X j)^(∑ k ∈ d.support, d k), _, rfl⟩
            : Submonoid.powers (X j : MvPolynomial _ S))
        * ι ((X j)^N)
      = ι ((p.coeff d • ∏ k ∈ d.support, (X k.1 : MvPolynomial _ S) ^ d k)
          * (X j)^(N - ∑ k ∈ d.support, d k)) := by
    intro d hd
    rw [show (ι ((X j)^N) : Localization.Away (X j : MvPolynomial (Fin (n+1)) S))
        = Localization.mk ((X j)^N) (1 : Submonoid.powers _) from
      (Localization.mk_one_eq_algebraMap _).symm,
      Localization.mk_mul, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    push_cast
    simp only [one_mul, mul_one]
    rw [mul_left_comm, ← pow_add,
      Nat.add_sub_cancel' (Finset.le_sup (f := fun d => ∑ k ∈ d.support, d k) hd)]
  rw [Finset.sum_congr rfl hterm, ← map_sum] at hp'
  replace hp' := hι (hp'.trans (map_zero ι).symm)
  have hform : ∀ d ∈ p.support,
      (p.coeff d • ∏ k ∈ d.support, (X k.1 : MvPolynomial (Fin (n+1)) S) ^ d k)
        * (X j)^(N - ∑ k ∈ d.support, d k)
      = (MvPolynomial.monomial
          (d.mapDomain Subtype.val + Finsupp.single j (N - ∑ k ∈ d.support, d k)))
          (p.coeff d) := by
    intro d _
    rw [MvPolynomial.monomial_eq, Finsupp.prod_add_index (by simp)
        (by intros; exact pow_add _ _ _),
      show ((Finsupp.single j (N - ∑ k ∈ d.support, d k)).prod
            fun i e => (X i : MvPolynomial (Fin (n + 1)) S) ^ e)
          = (X j)^(N - ∑ k ∈ d.support, d k) from
        Finsupp.prod_single_index (pow_zero _),
      Finsupp.prod_mapDomain_index_inj Subtype.val_injective, Finsupp.prod,
      MvPolynomial.smul_eq_C_mul, mul_assoc]
  rw [Finset.sum_congr rfl hform] at hp'
  ext d₀
  by_cases hd₀ : d₀ ∈ p.support
  · have hcoef := congrArg (fun q : MvPolynomial (Fin (n + 1)) S => q.coeff (d₀.mapDomain
      Subtype.val
      + Finsupp.single j (N - ∑ k ∈ d₀.support, d₀ k))) hp'
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
      AddMonoidAlgebra.coeff_zero] at hcoef
    rw [Finset.sum_congr rfl (fun d _ => if_congr
      ⟨fun h => exponent_inj n j N h, fun h => h ▸ rfl⟩ rfl rfl),
      Finset.sum_ite_eq' p.support d₀ (fun d => p.coeff d), ite_eq_left hd₀] at hcoef
    exact hcoef.trans (by simp)
  · exact (MvPolynomial.notMem_support_iff.mp hd₀).trans (by simp)

/-- The algebra equivalence identifying the standard chart with a polynomial ring in coordinate
    ratios. -/
def awayChartEquiv :
    MvPolynomial {k // k ≠ j} S ≃ₐ[S] Away 𝒜S (MvPolynomial.X j) :=
  AlgEquiv.ofBijective
    (MvPolynomial.aeval fun k : {k // k ≠ j} => ratio S n j k.1)
    ⟨aeval_ratio_injective n j, by
      rw [← AlgHom.range_eq_top, eq_top_iff, ← adjoin_range_ratio S n j,
        Algebra.adjoin_le_iff]
      rintro _ ⟨k, rfl⟩
      rcases eq_or_ne k j with rfl | hk
      · exact ratio_self S n k ▸ one_mem _
      · exact ⟨MvPolynomial.X ⟨k, hk⟩, MvPolynomial.aeval_X _ _⟩⟩

theorem awayChartEquiv_X (k : {k // k ≠ j}) :
    (awayChartEquiv (S := S) n j) (MvPolynomial.X k)
      = ratio S n j k.1 :=
  MvPolynomial.aeval_X _ _

end AwayChart

section AwayBC

variable (j : Fin (n + 1))

local instance algebra_away_R :
    Algebra R (Away 𝒜A (MvPolynomial.X j)) :=
  ((algebraMap A (Away 𝒜A (X j))).comp (algebraMap R A)).toAlgebra

/-- The coefficient ring algebra homomorphism between the standard localization charts. -/
def awayMapXₐ :
    Away 𝒜R (MvPolynomial.X j) →ₐ[R] Away 𝒜A (MvPolynomial.X j) where
  toRingHom := awayMapX R A n j
  commutes' r := RingHom.congr_fun (awayMapX_algebraMap R A n j) r

/-- The algebra homomorphism from the extended coefficient ring into its projective chart. -/
def incAₐ : A →ₐ[R] Away 𝒜A (MvPolynomial.X j) where
  toRingHom := algebraMap A (Away 𝒜A (X j))
  commutes' _ := rfl

/-- The algebra equivalence between scalar extension of a polynomial ring and polynomials over the
    extended coefficients. -/
def scalarRTensorAlgEquiv' (σ : Type*) : MvPolynomial σ R ⊗[R] A ≃ₐ[R] MvPolynomial σ A :=
  (Algebra.TensorProduct.comm R (MvPolynomial σ R) A).trans
    ((MvPolynomial.algebraTensorAlgEquiv R A).restrictScalars R)

theorem scalarRTensor_tmul_one {σ : Type*}
    (p : MvPolynomial σ R) :
    scalarRTensorAlgEquiv' R A σ (p ⊗ₜ (1 : A))
      = MvPolynomial.map (algebraMap R A) p := by
  simp only [scalarRTensorAlgEquiv', AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

theorem scalarRTensor_one_tmul {σ : Type*} (a : A) :
    scalarRTensorAlgEquiv' R A σ ((1 : MvPolynomial σ R) ⊗ₜ a)
      = MvPolynomial.C a := by
  simp only [scalarRTensorAlgEquiv', AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul, map_one,
    MvPolynomial.smul_eq_C_mul, mul_one]

theorem awayMapX_chart_compat :
    (awayMapXₐ R A n j).comp
        (awayChartEquiv (S := R) n j).toAlgHom
      = AlgHom.comp
          ({ toRingHom := (awayChartEquiv (S := A) n j).toRingEquiv.toRingHom
             commutes' := fun r => by
               exact (awayChartEquiv (S := A) n j).commutes (algebraMap R A r) }
            : MvPolynomial {k // k ≠ j} A →ₐ[R] Away 𝒜A (X j))
          (MvPolynomial.mapAlgHom (Algebra.ofId R A)) := by
  refine MvPolynomial.algHom_ext fun k => ?_
  simp only [AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply,
    MvPolynomial.map_X, awayMapXₐ, AlgHom.coe_mk]
  erw [awayChartEquiv_X (S := R) n j k]
  rw [awayMapX_ratio]
  exact (awayChartEquiv_X (S := A) n j k).symm

/-- The ring equivalence identifying the scalar extension of a homogeneous localization chart. -/
def awayMvPolyBaseChangeEquiv :
    (Away 𝒜R (MvPolynomial.X j)) ⊗[R] A ≃+* Away 𝒜A (MvPolynomial.X j) := by
  classical
  refine RingEquiv.ofBijective
    (Algebra.TensorProduct.productMap (awayMapXₐ R A n j)
      (incAₐ R A n j)).toRingHom ?_
  rw [show ((Algebra.TensorProduct.productMap _ _ : _ →ₐ[R] _).toRingHom : _ → _)
    = (Algebra.TensorProduct.productMap (awayMapXₐ R A n j)
        (incAₐ R A n j) : _ → _) from rfl]
  have hcongr : Function.Bijective
      (Algebra.TensorProduct.congr
        (awayChartEquiv (S := R) n j) (AlgEquiv.refl (A₁ := A))
        : MvPolynomial {k // k ≠ j} R ⊗[R] A → Away 𝒜R (X j) ⊗[R] A) :=
    (Algebra.TensorProduct.congr _ _).bijective
  rw [← Function.Bijective.of_comp_iff
    (Algebra.TensorProduct.productMap (awayMapXₐ R A n j)
      (incAₐ R A n j) : _ → _) hcongr]
  have hcomp : (Algebra.TensorProduct.productMap (awayMapXₐ R A n j)
          (incAₐ R A n j)).comp
        (Algebra.TensorProduct.congr
          (awayChartEquiv (S := R) n j) AlgEquiv.refl).toAlgHom
      = AlgHom.comp
          ({ toRingHom := (awayChartEquiv (S := A) n j).toRingEquiv.toRingHom
             commutes' := fun r => by
               exact (awayChartEquiv (S := A) n j).commutes (algebraMap R A r) }
            : MvPolynomial {k // k ≠ j} A →ₐ[R] Away 𝒜A (X j))
          (scalarRTensorAlgEquiv' R A {k // k ≠ j}).toAlgHom := by
    refine DFunLike.ext _ _ fun z => ?_
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul q a =>
      have hL := DFunLike.congr_fun (awayMapX_chart_compat R A n j) q
      simp only [AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply] at hL
      have hcongr_tmul :
          (Algebra.TensorProduct.congr
              (awayChartEquiv (S := R) n j) (AlgEquiv.refl (A₁ := A)))
            (q ⊗ₜ a)
          = (awayChartEquiv (S := R) n j q) ⊗ₜ[R] a := by
        rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]; rfl
      have hstr_split :
          scalarRTensorAlgEquiv' R A {k // k ≠ j} (q ⊗ₜ a)
          = MvPolynomial.map (algebraMap R A) q * C a := by
        have hsplit : (q ⊗ₜ[R] a : MvPolynomial {k // k ≠ j} R ⊗[R] A)
            = (q ⊗ₜ (1 : A)) * ((1 : MvPolynomial {k // k ≠ j} R) ⊗ₜ a) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [hsplit, map_mul, scalarRTensor_tmul_one,
          scalarRTensor_one_tmul]
      simp only [AlgHom.coe_comp, Function.comp_apply]
      erw [hcongr_tmul]
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      erw [hstr_split, map_mul, ← hL]
      congr 1
      exact ((awayChartEquiv (S := A) n j).commutes a).symm
  rw [show (Algebra.TensorProduct.productMap _ _ : _ → _) ∘
        (Algebra.TensorProduct.congr
          (awayChartEquiv (S := R) n j) AlgEquiv.refl : _ → _)
      = ((Algebra.TensorProduct.productMap (awayMapXₐ R A n j)
            (incAₐ R A n j)).comp
          (Algebra.TensorProduct.congr
            (awayChartEquiv (S := R) n j) AlgEquiv.refl).toAlgHom : _ → _) from rfl,
    hcomp]
  exact (awayChartEquiv (S := A) n j).bijective.comp
    (scalarRTensorAlgEquiv' R A {k // k ≠ j}).bijective

theorem awayMvPolyBaseChangeEquiv_tmul_one (x : Away 𝒜R (MvPolynomial.X j)) :
    awayMvPolyBaseChangeEquiv R A n j (x ⊗ₜ 1)
      = awayMapX R A n j x := by
  simp [awayMvPolyBaseChangeEquiv, RingEquiv.ofBijective,
    Algebra.TensorProduct.productMap_apply_tmul, awayMapXₐ]

theorem awayMvPolyBaseChangeEquiv_one_tmul (a : A) :
    awayMvPolyBaseChangeEquiv R A n j (1 ⊗ₜ a)
      = algebraMap A (Away 𝒜A (X j)) a := by
  simp [awayMvPolyBaseChangeEquiv, RingEquiv.ofBijective,
    Algebra.TensorProduct.productMap_apply_tmul, incAₐ]

end AwayBC

theorem awayMap_fromZero_compat (s : MvPolynomial (Fin (n + 1)) R) :
    (Away.map (mvMapGraded R A n) s).comp
        ((HomogeneousLocalization.fromZeroRingHom 𝒜R _).comp
          (grad0Equiv R n).toRingHom)
      = ((HomogeneousLocalization.fromZeroRingHom 𝒜A _).comp
          (grad0Equiv A n).toRingHom).comp (algebraMap R A) := by
  ext r
  change (Localization.mk _ _ : Localization.Away ((mvMapGraded R A n) s))
    = Localization.mk _ _
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp [grad0Equiv, mvMapGraded, MvPolynomial.map_C]

theorem w_chart {d : ℕ} (hd : 0 < d)
    (s : MvPolynomial (Fin (n + 1)) R) (hs : s ∈ 𝒜R d) :
    Proj.awayι 𝒜A ((mvMapGraded R A n) s)
        ((mvMapGraded R A n).map_mem hs) hd
      ≫ (Proj.map (mvMapGraded R A n)
          (irrelevant_le_map_mvMapGraded R A n)) ≫ π R n
    = Proj.awayι 𝒜A ((mvMapGraded R A n) s)
        ((mvMapGraded R A n).map_mem hs) hd
      ≫ π A n ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [← Category.assoc, Proj.awayι_comp_map (mvMapGraded R A n)
      (irrelevant_le_map_mvMapGraded R A n) hd s hs,
    π, π]
  simp only [Category.assoc]
  rw [← Category.assoc (Proj.awayι 𝒜R s hs hd), Proj.awayι_toSpecZero,
    ← Category.assoc (Proj.awayι 𝒜A _ _ hd), Proj.awayι_toSpecZero]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (Spec.map <| CommRingCat.ofHom ·)
    (awayMap_fromZero_compat R A n s)

theorem w :
    (Proj.map (mvMapGraded R A n)
        (irrelevant_le_map_mvMapGraded R A n)) ≫ π R n
      = π A n ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  refine (Proj.mapAffineOpenCover (mvMapGraded R A n)
    (irrelevant_le_map_mvMapGraded R A n)).openCover.hom_ext _ _ fun i => ?_
  obtain ⟨⟨d, hd⟩, s, hs⟩ := i
  exact w_chart R A n hd s hs

/-- The isomorphism from the pullback of a standard affine chart to the corresponding chart after
    coefficient extension. -/
def chartIso (j : Fin (n + 1)) :
    (Scheme.Pullback.openCoverOfLeft (affineOpenCover R n).openCover
        (π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A)))).X j
      ≅ Spec (.of (Away 𝒜A (MvPolynomial.X j))) :=
  pullback.congrHom (awayι_comp_π R n j) rfl
    ≪≫ pullbackSpecIso R (Away 𝒜R (MvPolynomial.X j)) A
    ≪≫ (Scheme.Spec.mapIso
        (awayMvPolyBaseChangeEquiv R A n j).toCommRingCatIso.op).symm

theorem projMap_preimage_basicOpen_X (j : Fin (n + 1)) :
    Proj.map (mvMapGraded R A n) (irrelevant_le_map_mvMapGraded R A n)
        ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen _ (X j : MvPolynomial (Fin (n + 1)) R)
      = AlgebraicGeometry.Proj.basicOpen _ (X j : MvPolynomial (Fin (n + 1)) A) := by
  rw [AlgebraicGeometry.Proj.map_preimage_basicOpen]
  exact congrArg (AlgebraicGeometry.Proj.basicOpen _) (MvPolynomial.map_X _ j)

theorem map_preimage_basicOpen_X' (j : Fin (n + 1)) :
    map R A n ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen _ (X j : MvPolynomial (Fin (n + 1)) R)
      = AlgebraicGeometry.Proj.basicOpen _ (X j : MvPolynomial (Fin (n + 1)) A) :=
  projMap_preimage_basicOpen_X R A n j

theorem isPullback_map' :
    IsPullback (map R A n) (π A n) (π R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  rw [map_eq]
  set gmap := Spec.map (CommRingCat.ofHom (algebraMap R A))
  set c := pullback.lift
    (Proj.map (mvMapGraded R A n) (irrelevant_le_map_mvMapGraded R A n))
    (π A n) (w R A n) with hc
  have hkey : ∀ j : Fin (n + 1),
      Proj.awayι 𝒜A (MvPolynomial.X j) (X_mem_one A n j) one_pos ≫ c
      = (chartIso R A n j).inv
        ≫ (Scheme.Pullback.openCoverOfLeft (affineOpenCover R n).openCover
            (π R n) gmap).f j := by
    intro j
    have haux : ∀ {y : MvPolynomial (Fin (n + 1)) A}
        (h : (mvMapGraded R A n) (X j) = y) (hy : y ∈ 𝒜A 1),
        Proj.awayι 𝒜A y hy one_pos
            ≫ Proj.map (mvMapGraded R A n) (irrelevant_le_map_mvMapGraded R A n)
          = Spec.map (CommRingCat.ofHom
              (h ▸ HomogeneousLocalization.Away.map (mvMapGraded R A n) (X j)))
            ≫ Proj.awayι 𝒜R (X j) (X_mem_one R n j) one_pos := by
      intro y h hy; subst h
      exact Proj.awayι_comp_map (mvMapGraded R A n)
        (irrelevant_le_map_mvMapGraded R A n) one_pos (X j)
        (X_mem_one R n j)
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hc, pullback.lift_fst,
        haux (mvMapGraded_X R A n j) (X_mem_one A n j)]
      erw [chartIso, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv,
        Functor.mapIso_hom, Iso.op_hom, Scheme.Pullback.openCoverOfLeft_f,
        pullback.congrHom_inv]
      erw [Category.assoc, Category.assoc, Category.assoc]
      erw [pullback.lift_fst, pullback.lift_fst_assoc]
      simp only [Category.comp_id, affineOpenCover_f]
      rw [pullbackSpecIso_inv_fst_assoc,
        show Scheme.Spec.map
            (awayMvPolyBaseChangeEquiv R A n j).toCommRingCatIso.hom.op
          = Spec.map (CommRingCat.ofHom
              (awayMvPolyBaseChangeEquiv R A n j).toRingHom) from rfl,
        ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (· ≫ Proj.awayι 𝒜R (X j) (X_mem_one R n j) one_pos)
        (congrArg (Spec.map <| CommRingCat.ofHom ·)
          (RingHom.ext fun x =>
            (awayMvPolyBaseChangeEquiv_tmul_one R A n j x).symm))
    · rw [Category.assoc, hc, pullback.lift_snd, awayι_comp_π A n j]
      erw [chartIso, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv,
        Functor.mapIso_hom, Iso.op_hom, Scheme.Pullback.openCoverOfLeft_f,
        pullback.congrHom_inv]
      erw [Category.assoc, Category.assoc, Category.assoc]
      erw [pullback.lift_snd, pullback.lift_snd_assoc]
      simp only [Category.comp_id]
      rw [pullbackSpecIso_inv_snd,
        show Scheme.Spec.map
            (awayMvPolyBaseChangeEquiv R A n j).toCommRingCatIso.hom.op
          = Spec.map (CommRingCat.ofHom
              (awayMvPolyBaseChangeEquiv R A n j).toRingHom) from rfl,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (Spec.map <| CommRingCat.ofHom ·)
        (RingHom.ext fun a =>
          (awayMvPolyBaseChangeEquiv_one_tmul R A n j a).symm)
  have : IsIso c := by
    set 𝒰 := Scheme.Pullback.openCoverOfLeft (affineOpenCover R n).openCover
      (π R n) gmap
    refine IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
      𝒰 fun (j : Fin (n + 1)) => ?_
    have hbase : IsOpenImmersion ((affineOpenCover R n).openCover.f j) :=
      inferInstanceAs (IsOpenImmersion ((affineOpenCover R n).openCover.f
        (show (affineOpenCover R n).openCover.I₀ from j)))
    have hcover : IsOpenImmersion (𝒰.f j) :=
      inferInstanceAs (IsOpenImmersion (𝒰.f (show 𝒰.I₀ from j)))
    rw [MorphismProperty.isomorphisms.iff]
    change IsIso (pullback.snd c (𝒰.f j))
    have hrange : Set.range
          (Proj.awayι 𝒜A (X j) (X_mem_one A n j) one_pos).base
        = Set.range (pullback.fst c (𝒰.f j)).base := by
      have h𝒰f : (𝒰.f j).opensRange
          = pullback.fst (π R n) gmap ⁻¹ᵁ
              ((affineOpenCover R n).openCover.f j).opensRange := by
        refine TopologicalSpace.Opens.ext ?_
        have := Scheme.Pullback.range_map
          ((affineOpenCover R n).openCover.f j ≫ π R n) gmap
          (π R n) gmap
          ((affineOpenCover R n).openCover.f j)
          (𝟙 _) (𝟙 _) (by simp) (by simp)
        refine this.trans ?_
        rw [show Set.range (𝟙 (Spec (.of A)) : Spec (.of A) ⟶ Spec (.of A)) =
          Set.univ from Set.range_id,
          Set.preimage_univ, Set.inter_univ]
        exact (Scheme.Hom.coe_preimage (f := pullback.fst (π R n) gmap)
          (U := ((affineOpenCover R n).openCover.f j).opensRange)).symm
      have key : (pullback.fst c (𝒰.f j)).opensRange
          = (Proj.awayι 𝒜A (X j) (X_mem_one A n j) one_pos).opensRange := by
        rw [Scheme.Hom.opensRange_pullbackFst (𝒰.f j) c, h𝒰f,
          ← Scheme.Hom.comp_preimage, hc, pullback.lift_fst,
          show ((affineOpenCover R n).openCover.f j).opensRange
            = AlgebraicGeometry.Proj.basicOpen _ (X j) from
            Proj.opensRange_awayι 𝒜R (X j) (X_mem_one R n j) one_pos,
          projMap_preimage_basicOpen_X R A n j,
          Proj.opensRange_awayι 𝒜A (X j) (X_mem_one A n j) one_pos]
      exact (congrArg SetLike.coe key).symm
    let e := IsOpenImmersion.isoOfRangeEq
      (Proj.awayι 𝒜A (X j) (X_mem_one A n j) one_pos)
      (pullback.fst c (𝒰.f j)) hrange
    have hsnd : e.hom ≫ pullback.snd c (𝒰.f j) = (chartIso R A n j).inv := by
      rw [show e.hom = pullback.lift _ (chartIso R A n j).inv (hkey j) from
        (cancel_mono (pullback.fst _ _)).mp
          ((IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).trans (pullback.lift_fst _ _ _).symm)]
      exact pullback.lift_snd _ _ _
    have : IsIso (e.hom ≫ pullback.snd c (𝒰.f j)) := hsnd ▸ inferInstance
    exact IsIso.of_isIso_comp_left e.hom (pullback.snd c (𝒰.f j))
  exact IsPullback.of_iso_pullback ⟨w R A n⟩ (asIso c)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end ProjBaseChange

end AlgebraicGeometry.ProjSpace

theorem _root_.AlgebraicGeometry.ProjSpace.isPullback_map (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) :
    IsPullback (AlgebraicGeometry.ProjSpace.map R A n) (AlgebraicGeometry.ProjSpace.π A n)
        (AlgebraicGeometry.ProjSpace.π R n)
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  AlgebraicGeometry.ProjSpace.isPullback_map' R A n

end
end AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map
end ProofImplementation
