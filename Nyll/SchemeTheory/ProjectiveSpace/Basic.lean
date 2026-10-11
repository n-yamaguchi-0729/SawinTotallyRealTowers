/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ProjSpace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Projective space and its standard charts

Projective space is constructed from graded polynomial rings together with its standard
affine charts, maps and fibre products. Chow data records the resulting projective
compactification constructions.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

section PnSetup

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The identification of the degree zero homogeneous polynomials with the coefficient ring. -/
def grad0Equiv : R ≃+* (𝒜 0) where
  toFun r := ⟨C r, (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_C _ r)⟩
  invFun p := MvPolynomial.constantCoeff p.1
  left_inv r := by simp
  right_inv p := by
    ext : 1
    have hp : p.1.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 _).mp p.2
    ext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [MvPolynomial.constantCoeff]
    · rw [MvPolynomial.coeff_C, ite_eq_right (Ne.symm hd)]
      by_contra h
      refine hd (Finsupp.ext fun i => ?_)
      have hdeg : (Finsupp.weight (1 : Fin (n + 1) → ℕ)) d = 0 := hp (fun h0 => h h0.symm)
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
        Finsupp.sum] at hdeg
      by_cases hi : i ∈ d.support
      · exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hdeg i hi
      · exact Finsupp.notMem_support_iff.mp hi
  map_mul' a b := by ext : 1; simp
  map_add' a b := by ext : 1; simp

/-- The structure morphism of projective space to the coefficient spectrum. -/
def π : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (grad0Equiv R n).toRingHom)

instance finiteType_mvPolynomial :
    Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin (n + 1)) R) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, eq_top_iff.mpr fun p _ => ?_⟩⟩
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _ (⟨C r, (mem_homogeneousSubmodule 0 _).mpr
      (isHomogeneous_C _ r)⟩ : 𝒜 0)
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p j hp =>
    exact Subalgebra.mul_mem _ (hp trivial)
      (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))))

instance isProper_π : IsProper (π R n) := by
  unfold π
  have : IsProper (Proj.toSpecZero 𝒜) := inferInstance
  have : IsIso (CommRingCat.ofHom (grad0Equiv R n).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (grad0Equiv R n).bijective
  have : IsIso (Spec.map (CommRingCat.ofHom (grad0Equiv R n).toRingHom)) :=
    inferInstance
  infer_instance

end PnSetup

section StdCover

open MvPolynomial AlgebraicGeometry.Proj

variable (R : Type u) [CommRing R] (n : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

theorem irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal
      ≤ Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial _ R)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi f hf
  have hf' : f.IsHomogeneous i := (MvPolynomial.mem_homogeneousSubmodule i f).mp hf
  change f ∈ MvPolynomial.idealOfVars (Fin (n + 1)) R
  rw [← pow_one (MvPolynomial.idealOfVars _ R), MvPolynomial.mem_pow_idealOfVars_iff]
  intro x hx
  rw [MvPolynomial.mem_support_iff] at hx
  have hdeg : Finsupp.degree x = i := by
    rw [Finsupp.degree_eq_weight_one]; exact hf' hx
  omega

end StdCover

section Setup

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

theorem X_mem_one (j : Fin (n + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ∈ 𝒜 1 :=
  (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X R j)

instance algebraAway (i : Fin (n + 1)) :
    Algebra R (Away 𝒜 (MvPolynomial.X i)) :=
  ((HomogeneousLocalization.fromZeroRingHom 𝒜 _).comp
    (grad0Equiv R n).toRingHom).toAlgebra

theorem awayι_comp_π (i : Fin (n + 1)) :
    Proj.awayι 𝒜 (MvPolynomial.X i) (X_mem_one R n i) one_pos
      ≫ π R n
      = Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜 (MvPolynomial.X i)))) := by
  unfold π
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The ratio of two homogeneous coordinate variables on the standard affine chart. -/
def ratio (i k : Fin (n + 1)) : Away 𝒜 (MvPolynomial.X i) :=
  Away.mk 𝒜 (X_mem_one R n i) 1 (MvPolynomial.X k)
    (by simpa using X_mem_one R n k)

theorem ratio_self (i : Fin (n + 1)) :
    ratio R n i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [ratio, Away.val_mk, HomogeneousLocalization.val_one,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

theorem val_algebraMap (i : Fin (n + 1)) (r : R) :
    (algebraMap R (Away 𝒜 (MvPolynomial.X i)) r).val
      = algebraMap (MvPolynomial (Fin (n + 1)) R) _ (MvPolynomial.C r) := by
  rfl

end Setup

section StdCover

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The standard affine cover of projective space by its homogeneous coordinate charts. -/
def affineOpenCover : (Proj 𝒜).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan 𝒜 (fun j => MvPolynomial.X j)
    (fun j => X_mem_one R n j) (fun _ => one_pos)
    (irrelevant_le_span_X R n)

theorem affineOpenCover_f (j : Fin (n + 1)) :
    (affineOpenCover R n).openCover.f j
      = Proj.awayι 𝒜 (MvPolynomial.X j) (X_mem_one R n j) one_pos := rfl

end StdCover

section AdjoinRatio

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

theorem awayMk_monomial (i : Fin (n + 1)) (d : ℕ)
    (e : Fin (n + 1) →₀ ℕ) (hd : e.degree = d) (r : R)
    (hm : MvPolynomial.monomial e r ∈ 𝒜 (d • 1)) :
    Away.mk 𝒜 (X_mem_one R n i) d (MvPolynomial.monomial e r) hm
      = algebraMap R _ r * ∏ j, (ratio R n i j) ^ (e j) := by
  have hdsum : ∑ j, e j = d := by
    rw [← hd, Finsupp.degree]
    exact (Finset.sum_subset (Finset.subset_univ _)
      (fun j _ hj => Finsupp.notMem_support_iff.mp hj)).symm
  apply HomogeneousLocalization.val_injective
  have hval : (HomogeneousLocalization.val : Away 𝒜 (X i) → Localization.Away (X i))
      = (algebraMap (Away 𝒜 (X i)) (Localization.Away (X i))) := rfl
  rw [hval, map_mul, map_prod]
  simp only [map_pow, ratio, ← hval, Away.val_mk,
    val_algebraMap, Localization.mk_pow,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_prod, Localization.mk_mul]
  congr 1
  · rw [MvPolynomial.monomial_eq, Finsupp.prod_pow]
  · refine Subtype.ext ?_
    push_cast
    simp only [Finset.prod_pow_eq_pow_sum, pow_one, one_mul, hdsum]

theorem adjoin_range_ratio (i : Fin (n + 1)) :
    Algebra.adjoin R (Set.range (ratio R n i)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (X_mem_one R n i) z
  have ha' : a.IsHomogeneous d := (mem_homogeneousSubmodule d a).mp (by simpa using ha)
  have hdeg : ∀ e ∈ a.support, (e : Fin (n + 1) →₀ ℕ).degree = d := fun e he => by
    rw [Finsupp.degree_eq_weight_one]; exact ha' (MvPolynomial.mem_support_iff.mp he)
  have hsum : Away.mk 𝒜 (X_mem_one R n i) d a ha
      = ∑ e ∈ a.support.attach,
          Away.mk 𝒜 (X_mem_one R n i) d
            (MvPolynomial.monomial e.1 (a.coeff e.1))
            ((mem_homogeneousSubmodule _ _).mpr
              (isHomogeneous_monomial _
                (by simp only [smul_eq_mul, mul_one]; exact hdeg e.1 e.2))) := by
    apply HomogeneousLocalization.val_injective
    have hval : (HomogeneousLocalization.val : Away 𝒜 (X i) → Localization.Away (X i))
        = (algebraMap (Away 𝒜 (X i)) (Localization.Away (X i))) := rfl
    rw [hval, map_sum]
    simp only [← hval, Away.val_mk]
    rw [Finset.sum_attach a.support
      (fun e => Localization.mk (monomial e (a.coeff e))
        (⟨(X i)^d, ⟨d, rfl⟩⟩ :
          Submonoid.powers (X i : MvPolynomial (Fin (n+1)) R))),
      ← Localization.mk_sum]
    congr 1
    exact MvPolynomial.as_sum a
  rw [hsum]
  refine Subalgebra.sum_mem _ fun e _ => ?_
  rw [awayMk_monomial R n i d e.1 (hdeg e.1 e.2) (a.coeff e.1)]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.prod_mem _ fun j _ =>
      Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self j)) _)

end AdjoinRatio

section ProdOver

variable (R : Type u) [CommRing R]

/-- The recursively constructed product of projective spaces together with its structure
    morphism. -/
def prodOverAux :
    ∀ {m : ℕ}, (Fin m → ℕ) → Σ (P : Scheme.{u}), P ⟶ Spec (.of R)
  | 0, _ => ⟨Spec (.of R), 𝟙 _⟩
  | m + 1, e =>
    let prev := @prodOverAux m (e ∘ Fin.succ)
    ⟨pullback (π R (e 0)) prev.2,
     pullback.fst _ _ ≫ π R (e 0)⟩

/-- The product over the coefficient spectrum of the indexed projective spaces. -/
abbrev prodOver {m : ℕ} (e : Fin m → ℕ) : Scheme.{u} :=
  (prodOverAux R e).1

/-- The structure morphism of the indexed product of projective spaces. -/
abbrev prodOverπ {m : ℕ} (e : Fin m → ℕ) :
    prodOver R e ⟶ Spec (.of R) :=
  (prodOverAux R e).2

theorem isProper_prodOverπ {m : ℕ} (e : Fin m → ℕ) :
    IsProper (prodOverπ R e) := by
  induction m with
  | zero => exact inferInstanceAs (IsProper (𝟙 _))
  | succ m ih =>
    have := ih (e ∘ Fin.succ)
    change IsProper (pullback.fst _ _ ≫ π R (e 0))
    infer_instance

instance instIsProperProdOverπ {m : ℕ} (e : Fin m → ℕ) : IsProper (prodOverπ R e) :=
  isProper_prodOverπ R e

/-- The projection from the indexed product to the indicated projective space. -/
def prodPr :
    ∀ {m : ℕ} (e : Fin m → ℕ) (k : Fin m),
      prodOver R e ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R)
  | _m + 1, _e, ⟨0, _⟩ => pullback.fst _ _
  | _m + 1, e, ⟨k + 1, hk⟩ =>
    pullback.snd _ _ ≫ prodPr (e ∘ Fin.succ) ⟨k, Nat.succ_lt_succ_iff.mp hk⟩

theorem prodPr_comp_π {m : ℕ} (e : Fin m → ℕ) (k : Fin m) :
    prodPr R e k ≫ π R (e k) = prodOverπ R e := by
  induction m with
  | zero => exact k.elim0
  | succ m ih =>
    match k with
    | ⟨0, _⟩ => rfl
    | ⟨k + 1, hk⟩ =>
      let j : Fin m := ⟨k, Nat.succ_lt_succ_iff.mp hk⟩
      have key := ih (e ∘ Fin.succ) j
      have ha := Category.assoc
        (pullback.snd (π R (e 0)) (prodOverπ R (e ∘ Fin.succ)))
        (prodPr R (e ∘ Fin.succ) j) (π R ((e ∘ Fin.succ) j))
      have hb := congrArg (fun g : prodOver R (e ∘ Fin.succ) ⟶ Spec (.of R) =>
        pullback.snd (π R (e 0)) (prodOverπ R (e ∘ Fin.succ)) ≫ g) key
      exact ha.trans (hb.trans
        (pullback.condition (f := π R (e 0)) (g := prodOverπ R (e ∘ Fin.succ))).symm)

/-- The recursively constructed product lift together with its compatibility with the base
    morphism. -/
def prodLiftAux {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) :
    ∀ {m : ℕ} (e : Fin m → ℕ)
      (g : ∀ k, X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R))
      (_ : ∀ k, g k ≫ π R (e k) = s),
      Σ' (l : X ⟶ prodOver R e), l ≫ prodOverπ R e = s
  | 0, _, _, _ => ⟨s, Category.comp_id s⟩
  | m + 1, e, g, hg =>
    let prev := @prodLiftAux X s m (e ∘ Fin.succ)
      (fun k => g k.succ) (fun k => hg k.succ)
    ⟨pullback.lift (g 0) prev.1 (by rw [hg 0, prev.2]),
     by
      change pullback.lift (g 0) prev.1 _ ≫ pullback.fst _ _ ≫ π R (e 0) = s
      rw [← Category.assoc, pullback.lift_fst]; exact hg 0⟩

/-- The product lift determined by morphisms to each projective factor over the same base. -/
def prodLift {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) {m : ℕ} (e : Fin m → ℕ)
    (g : ∀ k, X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R))
    (hg : ∀ k, g k ≫ π R (e k) = s) :
    X ⟶ prodOver R e :=
  (prodLiftAux R s e g hg).1

theorem prodLift_comp_prodOverπ {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
    {m : ℕ} (e : Fin m → ℕ)
    (g : ∀ k, X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R))
    (hg : ∀ k, g k ≫ π R (e k) = s) :
    prodLift R s e g hg ≫ prodOverπ R e = s := by
  exact (prodLiftAux R s e g hg).2

theorem prodLift_comp_prodPr {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
    {m : ℕ} (e : Fin m → ℕ)
    (g : ∀ k, X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R))
    (hg : ∀ k, g k ≫ π R (e k) = s) (k : Fin m) :
    prodLift R s e g hg ≫ prodPr R e k = g k := by
  induction m with
  | zero => exact k.elim0
  | succ m ih =>
    match k with
    | ⟨0, _⟩ => exact pullback.lift_fst _ _ _
    | ⟨k + 1, hk⟩ =>
      change (pullback.lift _ _ _) ≫ (pullback.snd _ _ ≫
        prodPr R (e ∘ Fin.succ) ⟨k, Nat.succ_lt_succ_iff.mp hk⟩) = _
      rw [← Category.assoc, pullback.lift_snd]
      exact ih (e ∘ Fin.succ) (fun k => g k.succ) (fun k => hg k.succ)
        ⟨k, Nat.succ_lt_succ_iff.mp hk⟩

end ProdOver

section MapGraded

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (n : ℕ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/-- The graded polynomial homomorphism induced by extending the coefficient ring. -/
def mvMapGraded : 𝒜R →+*ᵍ 𝒜A where
  toRingHom := MvPolynomial.map (algebraMap R A)
  map_mem hx := (mem_homogeneousSubmodule _ _).mpr (((mem_homogeneousSubmodule _ _).mp hx).map _)

theorem mvMapGraded_X (j : Fin (n + 1)) :
    (mvMapGraded R A n) (MvPolynomial.X j) = MvPolynomial.X j :=
  MvPolynomial.map_X _ j

theorem irrelevant_le_map_mvMapGraded :
    (HomogeneousIdeal.irrelevant 𝒜A)
      ≤ HomogeneousIdeal.map (mvMapGraded R A n)
          (HomogeneousIdeal.irrelevant 𝒜R) := by
  intro a ha
  change a ∈ (HomogeneousIdeal.map (mvMapGraded R A n)
    (HomogeneousIdeal.irrelevant _)).toIdeal
  rw [HomogeneousIdeal.toIdeal_map, MvPolynomial.as_sum a]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hd0 : d ≠ 0 := by
    rintro rfl
    refine (MvPolynomial.mem_support_iff.mp hd) ?_
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha
    classical
    conv_lhs => rw [← DirectSum.sum_support_decompose (homogeneousSubmodule (Fin (n + 1)) A) a]
    rw [coeff_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [ha, AddMonoidAlgebra.coeff_zero]
      rfl
    · exact ((mem_homogeneousSubmodule i _).mp
        (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) a i).2).coeff_eq_zero
        (by simpa [Finsupp.degree] using hi0.symm)
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr (Finsupp.support_eq_empty.not.mpr hd0)
  obtain ⟨q, hq⟩ : (X j : MvPolynomial (Fin (n + 1)) A) ∣ monomial d (a.coeff d) :=
    X_dvd_monomial.mpr (Or.inr (Finsupp.mem_support_iff.mp hj))
  rw [hq, show (X j : MvPolynomial (Fin (n + 1)) A)
      = (mvMapGraded R A n).toRingHom (X j) from (map_X _ j).symm]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _
    ((HomogeneousIdeal.mem_irrelevant_iff _ _).mpr (by
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne _
        ((mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X R j)) one_ne_zero])))

/-- The morphism of projective spaces induced by extending the coefficient ring. -/
def map : Proj 𝒜A ⟶ Proj 𝒜R :=
  Proj.map (mvMapGraded R A n) (irrelevant_le_map_mvMapGraded R A n)

theorem map_eq : map R A n = Proj.map (mvMapGraded R A n) (irrelevant_le_map_mvMapGraded R A n)
    := rfl

end MapGraded

end ProjSpace

section Carrier

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

/-- A proper modification with a closed immersion into a product of projective spaces and a
    dense open where the modification is an isomorphism. -/
structure ChowDatum where
  /-- The number of projective space factors. -/
  m : ℕ
  /-- The dimension of each projective space factor. -/
  e : Fin m → ℕ
  /-- The modifying scheme. -/
  V' : Scheme.{u}
  /-- The modification morphism to the original scheme. -/
  p : V' ⟶ V
  /-- The immersion into the product of projective spaces. -/
  ι : V' ⟶ ProjSpace.prodOver R e
  /-- The modification morphism is proper. -/
  hp_proper : IsProper p
  /-- The product immersion is closed. -/
  hι_closed : IsClosedImmersion ι
  /-- The product immersion and modification commute with the base morphisms. -/
  hover : ι ≫ ProjSpace.prodOverπ R e = p ≫ π
  /-- The open subset where the modification is an isomorphism. -/
  U : V.Opens
  /-- The selected open subset is dense. -/
  hU_dense : Dense (U : Set V)
  /-- The modification restricted over the selected open is an isomorphism. -/
  hp_isoU : IsIso (pullback.snd p U.ι)

attribute [instance] ChowDatum.hp_proper ChowDatum.hι_closed ChowDatum.hp_isoU

end Carrier

section CarrierProj

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

/-- A proper modification with a closed immersion into one projective space and a dense open
    where the modification is an isomorphism. -/
structure ChowDatumProj where
  /-- The dimension of the projective space. -/
  Nd : ℕ
  /-- The modifying scheme. -/
  V' : Scheme.{u}
  /-- The modification morphism to the original scheme. -/
  p : V' ⟶ V
  /-- The immersion into projective space. -/
  ιN : V' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Nd + 1)) R)
  /-- The modification morphism is proper. -/
  hp_proper : IsProper p
  /-- The projective space immersion is closed. -/
  hιN_closed : IsClosedImmersion ιN
  /-- The projective space immersion and modification commute with the base morphisms. -/
  hoverN : ιN ≫ ProjSpace.π R Nd = p ≫ π
  /-- The open subset where the modification is an isomorphism. -/
  U : V.Opens
  /-- The selected open subset is dense. -/
  hU_dense : Dense (U : Set V)
  /-- The modification restricted over the selected open is an isomorphism. -/
  hp_isoU : IsIso (pullback.snd p U.ι)

attribute [instance] ChowDatumProj.hp_proper ChowDatumProj.hιN_closed
  ChowDatumProj.hp_isoU

end CarrierProj

end AlgebraicGeometry

end
