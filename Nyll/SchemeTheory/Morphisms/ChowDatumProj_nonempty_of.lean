/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ChowDatumProj_nonempty_of.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.Morphisms.ChowDatum_nonempty
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.TensorProduct.Basic

/-! Segre embeddings and projective Chow data for proper schemes. -/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.ChowDatumProj_nonempty_of


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open HomogeneousLocalization TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace
open _root_.AlgebraicGeometry.ProjSpace
namespace Segre
open _root_.AlgebraicGeometry.ProjSpace

section ChartHom

variable (R : Type u) [CommRing R] (n p : ℕ)

/-- The dimension of the projective space containing the Segre embedding. -/
abbrev bigN : ℕ := (n + 1) * (p + 1) - 1

theorem bigN_succ :
    (n + 1) * (p + 1) = bigN n p + 1 := by
  have h : 0 < (n + 1) * (p + 1) := Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos p)
  unfold bigN; omega

/-- Identify pairs of homogeneous-coordinate indices with Segre-coordinate indices. -/
def idx : Fin (n + 1) × Fin (p + 1) ≃ Fin (bigN n p + 1) :=
  finProdFinEquiv.trans (finCongr (bigN_succ n p))

variable (i : Fin (n + 1)) (j : Fin (p + 1))

local notation "N" => bigN n p
local notation "𝒜ˣ" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜ʸ" => MvPolynomial.homogeneousSubmodule (Fin (p + 1)) R
local notation "𝒜ᶻ" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

/-- The coordinate ring of a product of two standard affine charts. -/
abbrev Tij : Type u :=
  (Away 𝒜ˣ (MvPolynomial.X i)) ⊗[R] (Away 𝒜ʸ (MvPolynomial.X j))

local notation "Aˣ" => Away 𝒜ˣ (MvPolynomial.X i)
local notation "Aʸ" => Away 𝒜ʸ (MvPolynomial.X j)

/-- Send each Segre coordinate to the tensor product of the corresponding chart ratios. -/
def preSegre : MvPolynomial (Fin (N + 1)) R →ₐ[R] (Aˣ ⊗[R] Aʸ) :=
  MvPolynomial.aeval
    (fun α => ((ProjSpace.ratio R n i ((idx n p).symm α).1)
      ⊗ₜ[R] (ProjSpace.ratio R p j ((idx n p).symm α).2) : Aˣ ⊗[R] Aʸ))

theorem preSegre_apply (k : Fin (n + 1)) (l : Fin (p + 1)) :
    preSegre R n p i j (MvPolynomial.X (idx n p (k, l)))
      = ((ProjSpace.ratio R n i k) ⊗ₜ[R] (ProjSpace.ratio R p j l) :
          Aˣ ⊗[R] Aʸ) := by
  unfold preSegre
  rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply]

theorem preSegre_unit :
    (preSegre R n p i j).toRingHom
        (MvPolynomial.X (idx n p (i, j))) = 1 := by
  change preSegre R n p i j (MvPolynomial.X (idx n p (i, j))) = 1
  rw [preSegre_apply, ProjSpace.ratio_self, ProjSpace.ratio_self,
    Algebra.TensorProduct.one_def]

theorem preSegre_mulone :
    (preSegre R n p i j).toRingHom
        (X (idx n p (i, j))) * 1 = 1 := by
  rw [preSegre_unit, mul_one]

/-- Extend the Segre coordinate map to the chosen localized polynomial ring. -/
def segreLift :
    Localization.Away (X (idx n p (i, j)) :
      MvPolynomial (Fin (N + 1)) R) →+* Tij R n p i j :=
  Localization.awayLift (preSegre R n p i j).toRingHom
    (MvPolynomial.X (idx n p (i, j)))
    ⟨⟨(preSegre R n p i j).toRingHom (X (idx n p (i, j))),
      1, preSegre_mulone R n p i j,
      (one_mul _).trans (preSegre_unit R n p i j)⟩, rfl⟩

/-- The ring map defining the Segre embedding on a standard affine chart. -/
def segreChart :
    Away 𝒜ᶻ (MvPolynomial.X (idx n p (i, j)))
      →+* Tij R n p i j :=
  (segreLift R n p i j).comp
    (algebraMap (Away 𝒜ᶻ (MvPolynomial.X (idx n p (i, j))))
      (Localization.Away (MvPolynomial.X (idx n p (i, j)))))

theorem segreChart_ratio (k : Fin (n + 1)) (l : Fin (p + 1)) :
    segreChart R n p i j
        (ProjSpace.ratio R N (idx n p (i, j))
          (idx n p (k, l)))
      = ((ProjSpace.ratio R n i k) ⊗ₜ[R] (ProjSpace.ratio R p j l) :
          Tij R n p i j) := by
  unfold segreChart segreLift Localization.awayLift IsLocalization.Away.lift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.lift_mk'_spec, map_pow, pow_one, preSegre_unit, one_mul]
  exact preSegre_apply R n p i j k l

theorem segreChart_algebraMap (r : R) :
    segreChart R n p i j
        (algebraMap R (Away 𝒜ᶻ (X (idx n p (i, j)))) r)
      = ((1 : Aˣ) ⊗ₜ[R] algebraMap R Aʸ r : Aˣ ⊗[R] Aʸ) := by
  unfold segreChart segreLift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    ProjSpace.val_algebraMap]
  erw [IsLocalization.lift_eq]
  have := (preSegre R n p i j).commutes r
  rw [Algebra.TensorProduct.algebraMap_apply'] at this
  exact this

theorem segreChart_surjective :
    Function.Surjective (segreChart R n p i j) := by
  intro z
  suffices h : z ∈ (segreChart R n p i j).range from h
  have hswap : ∀ r, ((1:Aˣ) ⊗ₜ[R] algebraMap R Aʸ r : Aˣ ⊗[R] Aʸ)
      = (algebraMap R Aˣ r) ⊗ₜ[R] (1:Aʸ) := fun r => by
    rw [Algebra.algebraMap_eq_smul_one (A := Aʸ), Algebra.algebraMap_eq_smul_one (A := Aˣ)]
    exact (TensorProduct.smul_tmul r (1:Aˣ) (1:Aʸ)).symm
  have hR : ∀ r, ((algebraMap R Aˣ r) ⊗ₜ[R] (1 : Aʸ) : Aˣ ⊗[R] Aʸ)
      ∈ (segreChart R n p i j).range :=
    fun r => ⟨algebraMap R _ r,
      (segreChart_algebraMap R n p i j r).trans (hswap r)⟩
  have hx : ∀ k, (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Aʸ) : Aˣ ⊗[R] Aʸ)
      ∈ (segreChart R n p i j).range := fun k => by
    rw [show (1 : Aʸ) = ProjSpace.ratio R p j j from (ProjSpace.ratio_self R p j).symm]
    exact ⟨_, segreChart_ratio R n p i j k j⟩
  have hy : ∀ l, ((1 : Aˣ) ⊗ₜ[R] ProjSpace.ratio R p j l : Aˣ ⊗[R] Aʸ)
      ∈ (segreChart R n p i j).range := fun l => by
    rw [show (1 : Aˣ) = ProjSpace.ratio R n i i from (ProjSpace.ratio_self R n i).symm]
    exact ⟨_, segreChart_ratio R n p i j i l⟩
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => exact Subring.add_mem _ ha hb
  | tmul a b =>
    rw [show (a ⊗ₜ[R] b : Aˣ ⊗[R] Aʸ) = (a ⊗ₜ[R] (1:Aʸ)) * ((1:Aˣ) ⊗ₜ[R] b) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    refine Subring.mul_mem _ ?_ ?_
    · have ha : a ∈ Algebra.adjoin R (Set.range (ProjSpace.ratio R n i)) := by
        rw [ProjSpace.adjoin_range_ratio]; exact Algebra.mem_top
      refine Algebra.adjoin_induction
        (fun c ⟨k, hk⟩ => hk ▸ hx k)
        (fun r => ?_)
        (fun a b _ _ ha hb => by rw [TensorProduct.add_tmul]; exact Subring.add_mem _ ha hb)
        (fun a b _ _ ha hb => by
          rw [show ((a * b) ⊗ₜ[R] (1:Aʸ) : Aˣ ⊗[R] Aʸ) = (a ⊗ₜ 1) * (b ⊗ₜ 1) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
          exact Subring.mul_mem _ ha hb)
        ha
      exact hR r
    · have hb : b ∈ Algebra.adjoin R (Set.range (ProjSpace.ratio R p j)) := by
        rw [ProjSpace.adjoin_range_ratio]; exact Algebra.mem_top
      refine Algebra.adjoin_induction
        (fun c ⟨l, hl⟩ => hl ▸ hy l)
        (fun r => ?_)
        (fun a b _ _ ha hb => by rw [TensorProduct.tmul_add]; exact Subring.add_mem _ ha hb)
        (fun a b _ _ ha hb => by
          rw [show ((1:Aˣ) ⊗ₜ[R] (a * b) : Aˣ ⊗[R] Aʸ) = (1 ⊗ₜ a) * (1 ⊗ₜ b) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
          exact Subring.mul_mem _ ha hb)
        hb
      rw [hswap r]; exact hR r

end ChartHom

/-- Naturality of the global-sections description of maps to affine schemes, in both directions.
The source scheme is arbitrary; the two affine targets and their maps may differ. -/
theorem comp_SpecMap_eq_iff {W : Scheme.{u}} {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    (f : W ⟶ Spec (.of B)) (g : W ⟶ Spec (.of C))
    (φ : A →+* B) (ψ : A →+* C) :
    f ≫ Spec.map (CommRingCat.ofHom φ) = g ≫ Spec.map (CommRingCat.ofHom ψ) ↔
      (((Scheme.ΓSpecIso (.of B)).inv ≫ f.appTop).hom).comp φ =
        (((Scheme.ΓSpecIso (.of C)).inv ≫ g.appTop).hom).comp ψ := by
  have hφ :
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (f ≫ Spec.map (CommRingCat.ofHom φ)).appTop).hom
        = (((Scheme.ΓSpecIso (.of B)).inv ≫ f.appTop).hom).comp φ := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have hψ :
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (g ≫ Spec.map (CommRingCat.ofHom ψ)).appTop).hom
        = (((Scheme.ΓSpecIso (.of C)).inv ≫ g.appTop).hom).comp ψ := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  constructor
  · intro h
    exact hφ.symm.trans ((congrArg
      (fun t : W ⟶ Spec (.of A) => ((Scheme.ΓSpecIso (.of A)).inv ≫ t.appTop).hom) h).trans hψ)
  · intro h
    exact ext_to_Spec (CommRingCat.hom_ext (hφ.trans (h.trans hψ.symm)))

section ProductCover

variable (R : Type u) [CommRing R] (n p : ℕ)

local notation "N" => bigN n p
local notation "𝒜ˣ" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜ʸ" => MvPolynomial.homogeneousSubmodule (Fin (p + 1)) R
local notation "𝒜ᶻ" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

/-- The product affine cover induced by the standard covers of the two projective spaces. -/
def prodCover :
    (pullback (ProjSpace.π R n) (ProjSpace.π R p)).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (ProjSpace.affineOpenCover R n).openCover (ProjSpace.affineOpenCover R p).openCover _ _

-- Keep the chart inclusion at its native pullback source, independent of cover-index reduction.
private def chartInclusion (i : Fin (n + 1)) (j : Fin (p + 1)) :
    pullback
        (Proj.awayι 𝒜ˣ (X i) (ProjSpace.X_mem_one R n i) one_pos ≫ ProjSpace.π R n)
        (Proj.awayι 𝒜ʸ (X j) (ProjSpace.X_mem_one R p j) one_pos ≫ ProjSpace.π R p)
      ⟶ pullback (ProjSpace.π R n) (ProjSpace.π R p) :=
  pullback.map _ _ _ _
    (Proj.awayι 𝒜ˣ (X i) (ProjSpace.X_mem_one R n i) one_pos)
    (Proj.awayι 𝒜ʸ (X j) (ProjSpace.X_mem_one R p j) one_pos)
    (𝟙 _) (Category.comp_id _) (Category.comp_id _)

private instance chartInclusion_isOpenImmersion (i : Fin (n + 1)) (j : Fin (p + 1)) :
    IsOpenImmersion (chartInclusion R n p i j) := by
  unfold chartInclusion
  infer_instance

/-- Identify a product chart with the spectrum of its tensor-product coordinate ring. -/
def chartIso (i : Fin (n + 1)) (j : Fin (p + 1)) :
    pullback ((Proj.awayι 𝒜ˣ (X i) (ProjSpace.X_mem_one R n i) one_pos) ≫ ProjSpace.π R n)
      ((Proj.awayι 𝒜ʸ (X j) (ProjSpace.X_mem_one R p j) one_pos) ≫ ProjSpace.π R p)
      ≅ Spec (.of <| (Away 𝒜ˣ (X i)) ⊗[R] (Away 𝒜ʸ (X j))) :=
  pullback.congrHom (ProjSpace.awayι_comp_π R n i) (ProjSpace.awayι_comp_π R p j)
    ≪≫ pullbackSpecIso R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))

/-- The local Segre morphism on a product chart. -/
def chartMap (i : Fin (n + 1)) (j : Fin (p + 1)) :
    pullback ((Proj.awayι 𝒜ˣ (X i) (ProjSpace.X_mem_one R n i) one_pos) ≫ ProjSpace.π R n)
      ((Proj.awayι 𝒜ʸ (X j) (ProjSpace.X_mem_one R p j) one_pos) ≫ ProjSpace.π R p) ⟶ Proj 𝒜ᶻ :=
  (chartIso R n p i j).hom
    ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))
    ≫ Proj.awayι 𝒜ᶻ (MvPolynomial.X (idx n p (i, j)))
        (ProjSpace.X_mem_one R N (idx n p (i, j))) one_pos

theorem chartMap_over (ij : Fin (n + 1) × Fin (p + 1)) :
    chartMap R n p ij.1 ij.2 ≫ ProjSpace.π R N
      = chartInclusion R n p ij.1 ij.2
          ≫ pullback.fst _ _ ≫ ProjSpace.π R n := by
  obtain ⟨i, j⟩ := ij
  change Fin (n + 1) at i; change Fin (p + 1) at j
  change chartMap R n p i j ≫ ProjSpace.π R N
    = chartInclusion R n p i j ≫ pullback.fst _ _ ≫ ProjSpace.π R n
  rw [chartMap, Category.assoc, Category.assoc,
    ProjSpace.awayι_comp_π R N (idx n p (i, j)), chartIso, Iso.trans_hom, Category.assoc]
  conv_rhs =>
    dsimp only [chartInclusion]
    rw [← Category.assoc]
    erw [pullback.lift_fst]
    erw [Category.assoc]
    enter [2]
    rw [show (Proj.awayι 𝒜ˣ (X i) (ProjSpace.X_mem_one R n i) one_pos) ≫ ProjSpace.π R n
        = Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i))))
      from ProjSpace.awayι_comp_π R n i]
  have hcong : (pullback.fst _ _
          : pullback ((Proj.awayι 𝒜ˣ (X i) (ProjSpace.X_mem_one R n i) one_pos) ≫ ProjSpace.π R n)
              ((Proj.awayι 𝒜ʸ (X j) (ProjSpace.X_mem_one R p j) one_pos) ≫ ProjSpace.π R p) ⟶ _)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i))))
      = (pullback.congrHom (ProjSpace.awayι_comp_π R n i)
          (ProjSpace.awayι_comp_π R p j)).hom
        ≫ pullback.fst _ _
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i)))) := by
    rw [pullback.congrHom_hom, ← Category.assoc, pullback.lift_fst, Category.comp_id]
  erw [hcong]
  suffices h : (pullbackSpecIso R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))).hom
        ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))
        ≫ Spec.map (CommRingCat.ofHom
            (algebraMap R (Away 𝒜ᶻ (X (idx n p (i, j))))))
      = pullback.fst _ _
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i)))) by rw [h]
  erw [← pullbackSpecIso_hom_fst_assoc R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  change segreChart R n p i j (algebraMap R _ r)
    = Algebra.TensorProduct.includeLeftRingHom (algebraMap R (Away 𝒜ˣ (X i)) r)
  rw [segreChart_algebraMap, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.algebraMap_eq_smul_one (R := R) (A := Away 𝒜ʸ (X j)),
    Algebra.algebraMap_eq_smul_one (R := R) (A := Away 𝒜ˣ (X i))]
  exact (TensorProduct.smul_tmul r (1 : Away 𝒜ˣ (X i)) (1 : Away 𝒜ʸ (X j))).symm

@[reassoc]
theorem prodCover_fst (ij : Fin (n + 1) × Fin (p + 1)) :
    chartInclusion R n p ij.1 ij.2 ≫ pullback.fst _ _
      = (pullback.fst _ _ : pullback ((Proj.awayι 𝒜ˣ (X ij.1) (ProjSpace.X_mem_one R n ij.1)
          one_pos) ≫ ProjSpace.π R n)
      ((Proj.awayι 𝒜ʸ (X ij.2) (ProjSpace.X_mem_one R p ij.2) one_pos) ≫ ProjSpace.π R p) ⟶ _)
        ≫ Proj.awayι 𝒜ˣ (X ij.1) (ProjSpace.X_mem_one R n ij.1) one_pos := by
  dsimp only [chartInclusion]
  erw [pullback.lift_fst]

@[reassoc]
theorem prodCover_snd (ij : Fin (n + 1) × Fin (p + 1)) :
    chartInclusion R n p ij.1 ij.2 ≫ pullback.snd _ _
      = (pullback.snd _ _ : pullback ((Proj.awayι 𝒜ˣ (X ij.1) (ProjSpace.X_mem_one R n ij.1)
          one_pos) ≫ ProjSpace.π R n)
      ((Proj.awayι 𝒜ʸ (X ij.2) (ProjSpace.X_mem_one R p ij.2) one_pos) ≫ ProjSpace.π R p) ⟶ _)
        ≫ Proj.awayι 𝒜ʸ (X ij.2) (ProjSpace.X_mem_one R p ij.2) one_pos := by
  dsimp only [chartInclusion]
  erw [pullback.lift_snd]

@[reassoc]
theorem chartIso_incL (i : Fin (n + 1)) (j : Fin (p + 1)) :
    (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))))
      = pullback.fst _ _ := by
  rw [chartIso, Iso.trans_hom, Category.assoc]
  erw [pullbackSpecIso_hom_fst R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))]
  rw [pullback.congrHom_hom]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem chartIso_incR (i : Fin (n + 1)) (j : Fin (p + 1)) :
    (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R) (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))).toRingHom)
      = pullback.snd _ _ := by
  rw [chartIso, Iso.trans_hom, Category.assoc]
  erw [pullbackSpecIso_hom_snd R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))]
  rw [pullback.congrHom_hom]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem isLocElem_ratio (i k : Fin (n + 1)) :
    HomogeneousLocalization.Away.isLocalizationElem
        (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n k)
      = ProjSpace.ratio R n i k := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, ProjSpace.ratio, pow_one]

/-- On an affine Segre chart, a coordinate basic open pulls back to the intersection
of the corresponding basic opens in the two factors. -/
private theorem segreChart_preimage_ratio (i k : Fin (n + 1)) (j l : Fin (p + 1)) :
    Spec.map (CommRingCat.ofHom (segreChart R n p i j))
        ⁻¹ᵁ PrimeSpectrum.basicOpen
          (ProjSpace.ratio R N (idx n p (i, j)) (idx n p (k, l)))
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R) (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))))
          ⁻¹ᵁ PrimeSpectrum.basicOpen (ProjSpace.ratio R n i k)
        ⊓ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R) (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))).toRingHom)
          ⁻¹ᵁ PrimeSpectrum.basicOpen (ProjSpace.ratio R p j l) := by
  have hbasic :
      PrimeSpectrum.basicOpen (segreChart R n p i j
        (ProjSpace.ratio R N (idx n p (i, j)) (idx n p (k, l))))
        = PrimeSpectrum.basicOpen
            (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Away 𝒜ʸ (X j)))
          ⊓ PrimeSpectrum.basicOpen
            ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j l) := by
    rw [segreChart_ratio, ← PrimeSpectrum.basicOpen_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact (SpecMap_preimage_basicOpen (CommRingCat.ofHom (segreChart R n p i j))
      (ProjSpace.ratio R N (idx n p (i, j)) (idx n p (k, l)))).trans
    (hbasic.trans (congrArg₂
      (fun U V : Opens (PrimeSpectrum (Tij R n p i j)) => U ⊓ V)
      (SpecMap_preimage_basicOpen
        (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R) (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))))
        (ProjSpace.ratio R n i k)).symm
      (SpecMap_preimage_basicOpen
        (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R) (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))).toRingHom)
        (ProjSpace.ratio R p j l)).symm))

theorem range_SpecMap_awayMap (i k : Fin (n + 1)) :
    Set.range (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
        (ProjSpace.X_mem_one R n k)
        (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k)))).base
      = (PrimeSpectrum.basicOpen (ProjSpace.ratio R n i k)
          : Set (PrimeSpectrum (Away 𝒜ˣ (X i)))) := by
  let := (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n k)
    (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k)).toAlgebra
  let := HomogeneousLocalization.Away.isLocalization_mul
    (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n k) rfl one_ne_zero
  rw [← isLocElem_ratio R n i k]
  exact PrimeSpectrum.localization_away_comap_range _ _

theorem opensRange_prodCover_f (α : Fin (n + 1) × Fin (p + 1)) :
    (chartInclusion R n p α.1 α.2).opensRange
      = pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)
          ⁻¹ᵁ (Proj.awayι 𝒜ˣ (X α.1) (ProjSpace.X_mem_one R n α.1) one_pos).opensRange
        ⊓ pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)
          ⁻¹ᵁ (Proj.awayι 𝒜ʸ (X α.2) (ProjSpace.X_mem_one R p α.2) one_pos).opensRange := by
  have key : Set.range (chartInclusion R n p α.1 α.2).base
      = (pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)).base ⁻¹' Set.range
          ((Proj.awayι 𝒜ˣ (X α.1) (ProjSpace.X_mem_one R n α.1) one_pos)).base
        ∩ (pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)).base ⁻¹' Set.range
          ((Proj.awayι 𝒜ʸ (X α.2) (ProjSpace.X_mem_one R p α.2) one_pos)).base := by
    dsimp only [chartInclusion]
    exact Scheme.Pullback.range_map _ _ (ProjSpace.π R n) (ProjSpace.π R p)
      ((Proj.awayι 𝒜ˣ (X α.1) (ProjSpace.X_mem_one R n α.1) one_pos))
      ((Proj.awayι 𝒜ʸ (X α.2) (ProjSpace.X_mem_one R p α.2) one_pos)) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _)
  exact TopologicalSpace.Opens.ext key

theorem awayMap_ratio_transition (i k a : Fin (n + 1)) :
    (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n i)
        (mul_comm (X i) (X k) : (X i * X k : MvPolynomial (Fin (n+1)) R) = X k * X i))
      (ProjSpace.ratio R n k a)
    * (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n k)
        (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k))
      (ProjSpace.ratio R n i k)
    = (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n k)
        (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k))
      (ProjSpace.ratio R n i a) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, ProjSpace.ratio,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    pow_one, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

/-- The Segre formulas respect a change of affine coordinates in any commutative target ring.
Agreement on the first chart and on base scalars, together with the two factor transitions,
determines the homomorphism on the second chart. -/
theorem segreChart_transition {S : Type*} [CommRing S]
    (i k : Fin (n + 1)) (j l : Fin (p + 1))
    (ξ : Away 𝒜ᶻ (X (idx n p (i, j)) * X (idx n p (k, l))) →+* S)
    (τ : Tij R n p i j →+* S) (ρ : Tij R n p k l →+* S)
    (hξ : ∀ z : Away 𝒜ᶻ (X (idx n p (i, j))),
      ξ (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl z)
        = τ (segreChart R n p i j z))
    (hX : ∀ a : Fin (n + 1),
      ρ (ProjSpace.ratio R n k a ⊗ₜ[R] (1 : Away 𝒜ʸ (X l)))
        * τ (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Away 𝒜ʸ (X j)))
        = τ (ProjSpace.ratio R n i a ⊗ₜ[R] (1 : Away 𝒜ʸ (X j))))
    (hY : ∀ b : Fin (p + 1),
      ρ ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] ProjSpace.ratio R p l b)
        * τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j l)
        = τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j b))
    (hR : ∀ r : R,
      τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] algebraMap R (Away 𝒜ʸ (X j)) r)
        = ρ ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] algebraMap R (Away 𝒜ʸ (X l)) r))
    (z : Away 𝒜ᶻ (X (idx n p (k, l)))) :
    ξ (HomogeneousLocalization.awayMap 𝒜ᶻ
        (ProjSpace.X_mem_one R N (idx n p (i, j))) (mul_comm _ _) z)
      = ρ (segreChart R n p k l z) := by
  have hunit : IsUnit (τ (ProjSpace.ratio R n i k
      ⊗ₜ[R] ProjSpace.ratio R p j l)) := by
    have hux := hX i
    rw [ProjSpace.ratio_self, ← Algebra.TensorProduct.one_def, map_one] at hux
    have huy := hY j
    rw [ProjSpace.ratio_self, ← Algebra.TensorProduct.one_def, map_one] at huy
    have hfactor : τ (ProjSpace.ratio R n i k ⊗ₜ[R] ProjSpace.ratio R p j l)
        = τ (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Away 𝒜ʸ (X j)))
          * τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j l) := by
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hfactor]
    exact (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans hux)).mul
      (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans huy))
  have hz : z ∈ Algebra.adjoin R (Set.range (ProjSpace.ratio R N
      (idx n p (k, l)))) := by
    rw [ProjSpace.adjoin_range_ratio]
    exact Algebra.mem_top
  induction hz using Algebra.adjoin_induction with
  | add a b _ _ ha hb => simp only [map_add, ha, hb]
  | mul a b _ _ ha hb => simp only [map_mul, ha, hb]
  | algebraMap r =>
      have hcoeff : HomogeneousLocalization.awayMap 𝒜ᶻ
          (ProjSpace.X_mem_one R N (idx n p (i, j))) (mul_comm _ _)
          (algebraMap R (Away 𝒜ᶻ (X (idx n p (k, l)))) r)
          = HomogeneousLocalization.awayMap 𝒜ᶻ
            (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl
            (algebraMap R (Away 𝒜ᶻ (X (idx n p (i, j)))) r) := by
        change HomogeneousLocalization.awayMap 𝒜ᶻ _ _
            (HomogeneousLocalization.fromZeroRingHom _ _ (ProjSpace.grad0Equiv R N r))
          = HomogeneousLocalization.awayMap 𝒜ᶻ _ _
            (HomogeneousLocalization.fromZeroRingHom _ _ (ProjSpace.grad0Equiv R N r))
        rw [HomogeneousLocalization.awayMap_fromZeroRingHom,
          HomogeneousLocalization.awayMap_fromZeroRingHom]
      rw [hcoeff, hξ, segreChart_algebraMap, segreChart_algebraMap]
      exact hR r
  | mem z hzm =>
      obtain ⟨β, rfl⟩ := hzm
      obtain ⟨⟨a, b⟩, rfl⟩ := (idx n p).surjective β
      have hT := congrArg ξ (awayMap_ratio_transition R N
        (idx n p (i, j)) (idx n p (k, l)) (idx n p (a, b)))
      rw [map_mul, hξ, hξ, segreChart_ratio, segreChart_ratio] at hT
      rw [segreChart_ratio]
      have hXY : ρ (ProjSpace.ratio R n k a ⊗ₜ[R] ProjSpace.ratio R p l b)
          * τ (ProjSpace.ratio R n i k ⊗ₜ[R] ProjSpace.ratio R p j l)
          = τ (ProjSpace.ratio R n i a ⊗ₜ[R] ProjSpace.ratio R p j b) := by
        have hproduct := mul_mul_mul_comm
          (ρ (ProjSpace.ratio R n k a ⊗ₜ[R] (1 : Away 𝒜ʸ (X l))))
          (ρ ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] ProjSpace.ratio R p l b))
          (τ (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Away 𝒜ʸ (X j))))
          (τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j l))
        rw [hX a, hY b, ← map_mul, ← map_mul, ← map_mul,
          Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one,
          one_mul, mul_one, one_mul] at hproduct
        exact hproduct
      exact hunit.mul_right_cancel (hT.trans hXY.symm)

theorem overlap_fst_condition (ij kl : Fin (n + 1) × Fin (p + 1)) :
    (pullback.fst (chartInclusion R n p ij.1 ij.2)
          (chartInclusion R n p kl.1 kl.2)
        ≫ (chartIso R n p ij.1 ij.2).hom
        ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
      ≫ Proj.awayι 𝒜ˣ (X ij.1) (ProjSpace.X_mem_one R n ij.1) one_pos
    = (pullback.snd _ _
        ≫ (chartIso R n p kl.1 kl.2).hom
        ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
      ≫ Proj.awayι 𝒜ˣ (X kl.1) (ProjSpace.X_mem_one R n kl.1) one_pos := by
  let f := chartInclusion R n p ij.1 ij.2
  let g := chartInclusion R n p kl.1 kl.2
  let h := pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)
  let u := (chartIso R n p ij.1 ij.2).hom ≫ Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom
      (R := R) (A := Away 𝒜ˣ (X ij.1)) (B := Away 𝒜ʸ (X ij.2))))
  let v := (chartIso R n p kl.1 kl.2).hom ≫ Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom
      (R := R) (A := Away 𝒜ˣ (X kl.1)) (B := Away 𝒜ʸ (X kl.2))))
  let a := Proj.awayι 𝒜ˣ (X ij.1) (ProjSpace.X_mem_one R n ij.1) one_pos
  let b := Proj.awayι 𝒜ˣ (X kl.1) (ProjSpace.X_mem_one R n kl.1) one_pos
  have hi : u ≫ a = f ≫ h :=
    ((chartIso_incL R n p ij.1 ij.2) =≫ a).trans (prodCover_fst R n p ij).symm
  have hk : v ≫ b = g ≫ h :=
    ((chartIso_incL R n p kl.1 kl.2) =≫ b).trans (prodCover_fst R n p kl).symm
  change (pullback.fst f g ≫ u) ≫ a = (pullback.snd f g ≫ v) ≫ b
  exact (Category.assoc _ _ _).trans
    ((pullback.fst f g ≫= hi).trans
      ((Category.assoc _ _ _).symm.trans
        (((pullback.condition (f := f) (g := g)) =≫ h).trans
          ((Category.assoc _ _ _).trans
            ((pullback.snd f g ≫= hk.symm).trans (Category.assoc _ _ _).symm)))))

theorem overlap_snd_condition (ij kl : Fin (n + 1) × Fin (p + 1)) :
    (pullback.fst (chartInclusion R n p ij.1 ij.2)
          (chartInclusion R n p kl.1 kl.2)
        ≫ (chartIso R n p ij.1 ij.2).hom
        ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
      ≫ Proj.awayι 𝒜ʸ (X ij.2) (ProjSpace.X_mem_one R p ij.2) one_pos
    = (pullback.snd _ _
        ≫ (chartIso R n p kl.1 kl.2).hom
        ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
      ≫ Proj.awayι 𝒜ʸ (X kl.2) (ProjSpace.X_mem_one R p kl.2) one_pos := by
  let f := chartInclusion R n p ij.1 ij.2
  let g := chartInclusion R n p kl.1 kl.2
  let h := pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)
  let u := (chartIso R n p ij.1 ij.2).hom ≫ Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight
      (R := R) (A := Away 𝒜ˣ (X ij.1)) (B := Away 𝒜ʸ (X ij.2))).toRingHom))
  let v := (chartIso R n p kl.1 kl.2).hom ≫ Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight
      (R := R) (A := Away 𝒜ˣ (X kl.1)) (B := Away 𝒜ʸ (X kl.2))).toRingHom))
  let a := Proj.awayι 𝒜ʸ (X ij.2) (ProjSpace.X_mem_one R p ij.2) one_pos
  let b := Proj.awayι 𝒜ʸ (X kl.2) (ProjSpace.X_mem_one R p kl.2) one_pos
  have hi : u ≫ a = f ≫ h :=
    ((chartIso_incR R n p ij.1 ij.2) =≫ a).trans (prodCover_snd R n p ij).symm
  have hk : v ≫ b = g ≫ h :=
    ((chartIso_incR R n p kl.1 kl.2) =≫ b).trans (prodCover_snd R n p kl).symm
  change (pullback.fst f g ≫ u) ≫ a = (pullback.snd f g ≫ v) ≫ b
  exact (Category.assoc _ _ _).trans
    ((pullback.fst f g ≫= hi).trans
      ((Category.assoc _ _ _).symm.trans
        (((pullback.condition (f := f) (g := g)) =≫ h).trans
          ((Category.assoc _ _ _).trans
            ((pullback.snd f g ≫= hk.symm).trans (Category.assoc _ _ _).symm)))))

theorem chartMap_compat (ij kl : Fin (n + 1) × Fin (p + 1)) :
    pullback.fst (chartInclusion R n p ij.1 ij.2)
        (chartInclusion R n p kl.1 kl.2)
      ≫ chartMap R n p ij.1 ij.2
    = pullback.snd _ _ ≫ chartMap R n p kl.1 kl.2 := by
  obtain ⟨i, j⟩ := ij; obtain ⟨k, l⟩ := kl
  change Fin (n + 1) at i; change Fin (n + 1) at k
  change Fin (p + 1) at j; change Fin (p + 1) at l
  simp only [chartMap, ← Category.assoc]
  set fstW := pullback.fst (chartInclusion R n p i j)
    (chartInclusion R n p k l) with hfstW
  set sndW := pullback.snd (chartInclusion R n p i j)
    (chartInclusion R n p k l) with hsndW
  set φ_ij := (fstW ≫ (chartIso R n p i j).hom)
    ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j)) with hφij
  set φ_kl := (sndW ≫ (chartIso R n p k l).hom)
    ≫ Spec.map (CommRingCat.ofHom (segreChart R n p k l)) with hφkl
  change φ_ij ≫ Proj.awayι 𝒜ᶻ (X (idx n p (i, j)))
      (ProjSpace.X_mem_one R N _) one_pos
    = φ_kl ≫ Proj.awayι 𝒜ᶻ (X (idx n p (k, l)))
      (ProjSpace.X_mem_one R N _) one_pos
  let ηx := pullback.lift
    (fstW ≫ (chartIso R n p i j).hom
      ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (sndW ≫ (chartIso R n p k l).hom
      ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (overlap_fst_condition R n p (i, j) (k, l))
  let ηx' := ηx ≫ (Proj.pullbackAwayιIso 𝒜ˣ (ProjSpace.X_mem_one R n i) one_pos
    (ProjSpace.X_mem_one R n k) one_pos
    (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k)).hom
  have hηx_fst : ηx' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n k) rfl))
      = fstW ≫ (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left, pullback.lift_fst]
  have hηx_snd : ηx' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n i) (mul_comm _ _)))
      = sndW ≫ (chartIso R n p k l).hom
        ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    rw [show (mul_comm (X i) (X k) : (X i * X k : MvPolynomial (Fin (n+1)) R) = X k * X i)
      = (rfl : (_ : MvPolynomial (Fin (n+1)) R) = X i * X k).trans (mul_comm _ _) from rfl]
    rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right, pullback.lift_snd]
  let ηy := pullback.lift
    (fstW ≫ (chartIso R n p i j).hom
      ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
    (sndW ≫ (chartIso R n p k l).hom
      ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
    (overlap_snd_condition R n p (i, j) (k, l))
  let ηy' := ηy ≫ (Proj.pullbackAwayιIso 𝒜ʸ (ProjSpace.X_mem_one R p j) one_pos
    (ProjSpace.X_mem_one R p l) one_pos
    (rfl : (X j * X l : MvPolynomial (Fin (p+1)) R) = X j * X l)).hom
  have hηy_fst : ηy' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ʸ
      (ProjSpace.X_mem_one R p l) rfl))
      = fstW ≫ (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R)).toRingHom) := by
    rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left, pullback.lift_fst]
  have hηy_snd : ηy' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ʸ
      (ProjSpace.X_mem_one R p j) (mul_comm _ _)))
      = sndW ≫ (chartIso R n p k l).hom
        ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R)).toRingHom) := by
    rw [show (mul_comm (X j) (X l) : (X j * X l : MvPolynomial (Fin (p+1)) R) = X l * X j)
      = (rfl : (_ : MvPolynomial (Fin (p+1)) R) = X j * X l).trans (mul_comm _ _) from rfl]
    rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right, pullback.lift_snd]
  have hoi : IsOpenImmersion (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (k, l)))
      (rfl : (X (idx n p (i, j)) * X (idx n p (k, l))
        : MvPolynomial (Fin (N+1)) R) = _)))) := by
    rw [← Proj.pullbackAwayιIso_inv_fst 𝒜ᶻ (ProjSpace.X_mem_one R N _) one_pos
      (ProjSpace.X_mem_one R N _) one_pos rfl]
    infer_instance
  have hrange : Set.range (φ_ij).base ⊆ Set.range
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
        (ProjSpace.X_mem_one R N (idx n p (k, l)))
        (rfl : (X (idx n p (i, j)) * X (idx n p (k, l))
          : MvPolynomial (Fin (N+1)) R) = _)))).base := by
    rw [range_SpecMap_awayMap R N
      (idx n p (i, j)) (idx n p (k, l))]
    rintro _ ⟨w, rfl⟩
    let O : (Spec (.of (Away 𝒜ᶻ (X (idx n p (i, j)))))).Opens :=
      PrimeSpectrum.basicOpen (ProjSpace.ratio R N (idx n p (i, j)) (idx n p (k, l)))
    let Ox : (Spec (.of (Away 𝒜ˣ (X i)))).Opens :=
      PrimeSpectrum.basicOpen (ProjSpace.ratio R n i k)
    let Oy : (Spec (.of (Away 𝒜ʸ (X j)))).Opens :=
      PrimeSpectrum.basicOpen (ProjSpace.ratio R p j l)
    have hPreimage : Spec.map (CommRingCat.ofHom (segreChart R n p i j)) ⁻¹ᵁ O =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ⁻¹ᵁ Ox ⊓
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ⁻¹ᵁ Oy :=
      segreChart_preimage_ratio R n p i k j l
    change w ∈ φ_ij ⁻¹ᵁ O
    rw [hφij, Scheme.Hom.comp_preimage, hPreimage,
      Scheme.Hom.preimage_inf,
      ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
      Category.assoc, Category.assoc, ← hηx_fst, ← hηy_fst]
    exact ⟨(range_SpecMap_awayMap R n i k).le ⟨ηx' w, rfl⟩,
      (range_SpecMap_awayMap R p j l).le ⟨ηy' w, rfl⟩⟩
  let ηz' := IsOpenImmersion.lift _ _ hrange
  have hstar1 : ηz' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl)) = φ_ij :=
    IsOpenImmersion.lift_fac _ _ hrange
  let W := pullback (chartInclusion R n p i j)
    (chartInclusion R n p k l)
  let ξx : Away 𝒜ˣ (X i * X k) →+* Γ(W, ⊤) :=
    ((Scheme.ΓSpecIso (.of (Away 𝒜ˣ (X i * X k)))).inv ≫ ηx'.appTop).hom
  let ξy : Away 𝒜ʸ (X j * X l) →+* Γ(W, ⊤) :=
    ((Scheme.ΓSpecIso (.of (Away 𝒜ʸ (X j * X l)))).inv ≫ ηy'.appTop).hom
  let ξz : Away 𝒜ᶻ (X (idx n p (i, j)) * X (idx n p (k, l))) →+* Γ(W, ⊤) :=
    ((Scheme.ΓSpecIso (.of (Away 𝒜ᶻ
      (X (idx n p (i, j)) * X (idx n p (k, l)))))).inv ≫ ηz'.appTop).hom
  let τ : Tij R n p i j →+* Γ(W, ⊤) :=
    ((Scheme.ΓSpecIso (.of (Tij R n p i j))).inv ≫
      (fstW ≫ (chartIso R n p i j).hom).appTop).hom
  let ρ₁ : Tij R n p k l →+* Γ(W, ⊤) :=
    ((Scheme.ΓSpecIso (.of (Tij R n p k l))).inv ≫
      (sndW ≫ (chartIso R n p k l).hom).appTop).hom
  have hx_fst : ξx.comp (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n k) rfl)
      = τ.comp (Algebra.TensorProduct.includeLeftRingHom
        (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))) :=
    (comp_SpecMap_eq_iff ηx' (fstW ≫ (chartIso R n p i j).hom)
      (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n k) rfl)
      Algebra.TensorProduct.includeLeftRingHom).mp
        (hηx_fst.trans (Category.assoc _ _ _).symm)
  have hx_snd : ξx.comp (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n i) (mul_comm _ _))
      = ρ₁.comp (Algebra.TensorProduct.includeLeftRingHom
        (A := Away 𝒜ˣ (X k)) (B := Away 𝒜ʸ (X l))) :=
    (comp_SpecMap_eq_iff ηx' (sndW ≫ (chartIso R n p k l).hom)
      (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n i) (mul_comm _ _))
      Algebra.TensorProduct.includeLeftRingHom).mp
        (hηx_snd.trans (Category.assoc _ _ _).symm)
  have hy_fst : ξy.comp (HomogeneousLocalization.awayMap 𝒜ʸ
      (ProjSpace.X_mem_one R p l) rfl)
      = τ.comp (Algebra.TensorProduct.includeRight
        (R := R) (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))).toRingHom :=
    (comp_SpecMap_eq_iff ηy' (fstW ≫ (chartIso R n p i j).hom)
      (HomogeneousLocalization.awayMap 𝒜ʸ (ProjSpace.X_mem_one R p l) rfl)
      (Algebra.TensorProduct.includeRight (R := R)).toRingHom).mp
        (hηy_fst.trans (Category.assoc _ _ _).symm)
  have hy_snd : ξy.comp (HomogeneousLocalization.awayMap 𝒜ʸ
      (ProjSpace.X_mem_one R p j) (mul_comm _ _))
      = ρ₁.comp (Algebra.TensorProduct.includeRight
        (R := R) (A := Away 𝒜ˣ (X k)) (B := Away 𝒜ʸ (X l))).toRingHom :=
    (comp_SpecMap_eq_iff ηy' (sndW ≫ (chartIso R n p k l).hom)
      (HomogeneousLocalization.awayMap 𝒜ʸ (ProjSpace.X_mem_one R p j) (mul_comm _ _))
      (Algebra.TensorProduct.includeRight (R := R)).toRingHom).mp
        (hηy_snd.trans (Category.assoc _ _ _).symm)
  have hz_fst : ξz.comp (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl)
      = τ.comp (segreChart R n p i j) :=
    (comp_SpecMap_eq_iff ηz' (fstW ≫ (chartIso R n p i j).hom)
      (HomogeneousLocalization.awayMap 𝒜ᶻ
        (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl)
      (segreChart R n p i j)).mp hstar1
  have hX : ∀ a, ρ₁ (ProjSpace.ratio R n k a ⊗ₜ[R] (1 : Away 𝒜ʸ (X l)))
      * τ (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Away 𝒜ʸ (X j)))
      = τ (ProjSpace.ratio R n i a ⊗ₜ[R] (1 : Away 𝒜ʸ (X j))) := fun a => by
    have := congrArg ξx (awayMap_ratio_transition R n i k a)
    rw [map_mul] at this
    have h1 : ∀ r, ξx (HomogeneousLocalization.awayMap 𝒜ˣ
        (ProjSpace.X_mem_one R n k) rfl r) = τ (r ⊗ₜ[R] 1) := fun r =>
      RingHom.congr_fun hx_fst r
    have h2 : ∀ r, ξx (HomogeneousLocalization.awayMap 𝒜ˣ
        (ProjSpace.X_mem_one R n i) (mul_comm _ _) r) = ρ₁ (r ⊗ₜ[R] 1) := fun r =>
      RingHom.congr_fun hx_snd r
    rw [h2, h1, h1] at this; exact this
  have hY : ∀ b, ρ₁ ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] ProjSpace.ratio R p l b)
      * τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j l)
      = τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j b) := fun b => by
    have := congrArg ξy (awayMap_ratio_transition R p j l b)
    rw [map_mul] at this
    have h1 : ∀ r, ξy (HomogeneousLocalization.awayMap 𝒜ʸ
        (ProjSpace.X_mem_one R p l) rfl r) = τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] r) := fun r =>
      RingHom.congr_fun hy_fst r
    have h2 : ∀ r, ξy (HomogeneousLocalization.awayMap 𝒜ʸ
        (ProjSpace.X_mem_one R p j) (mul_comm _ _) r) = ρ₁ ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] r) :=
      fun r =>
        RingHom.congr_fun hy_snd r
    rw [h2, h1, h1] at this; exact this
  have hξ : ∀ r, ξz (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl r)
      = τ (segreChart R n p i j r) := fun r =>
    RingHom.congr_fun hz_fst r
  have hR : ∀ r : R,
      τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] algebraMap R (Away 𝒜ʸ (X j)) r)
        = ρ₁ ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] algebraMap R (Away 𝒜ʸ (X l)) r) := by
    intro r
    have hcoeff : HomogeneousLocalization.awayMap 𝒜ʸ
        (ProjSpace.X_mem_one R p l) rfl (algebraMap R (Away 𝒜ʸ (X j)) r)
        = HomogeneousLocalization.awayMap 𝒜ʸ
          (ProjSpace.X_mem_one R p j) (mul_comm _ _)
          (algebraMap R (Away 𝒜ʸ (X l)) r) := by
      change HomogeneousLocalization.awayMap 𝒜ʸ _ _
          (HomogeneousLocalization.fromZeroRingHom _ _ (ProjSpace.grad0Equiv R p r))
        = HomogeneousLocalization.awayMap 𝒜ʸ _ _
          (HomogeneousLocalization.fromZeroRingHom _ _ (ProjSpace.grad0Equiv R p r))
      rw [HomogeneousLocalization.awayMap_fromZeroRingHom,
        HomogeneousLocalization.awayMap_fromZeroRingHom]
    exact (RingHom.congr_fun hy_fst _).symm.trans
      ((congrArg ξy hcoeff).trans (RingHom.congr_fun hy_snd _))
  have hstar2 : ηz' ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (i, j)))
      (mul_comm _ _))) = φ_kl := by
    apply (comp_SpecMap_eq_iff ηz' (sndW ≫ (chartIso R n p k l).hom)
      (HomogeneousLocalization.awayMap 𝒜ᶻ
        (ProjSpace.X_mem_one R N (idx n p (i, j))) (mul_comm _ _))
      (segreChart R n p k l)).mpr
    exact RingHom.ext (fun z =>
      segreChart_transition R n p i k j l ξz τ ρ₁ hξ hX hY hR z)
  let ιij : Spec (.of (Away 𝒜ᶻ (X (idx n p (i, j))))) ⟶ Proj 𝒜ᶻ :=
    Proj.awayι 𝒜ᶻ (X (idx n p (i, j)))
      (ProjSpace.X_mem_one R N (idx n p (i, j))) one_pos
  let ιkl : Spec (.of (Away 𝒜ᶻ (X (idx n p (k, l))))) ⟶ Proj 𝒜ᶻ :=
    Proj.awayι 𝒜ᶻ (X (idx n p (k, l)))
      (ProjSpace.X_mem_one R N (idx n p (k, l))) one_pos
  let ιboth : Spec (.of (Away 𝒜ᶻ
      (X (idx n p (i, j)) * X (idx n p (k, l))))) ⟶ Proj 𝒜ᶻ :=
    Proj.awayι 𝒜ᶻ (X (idx n p (i, j)) * X (idx n p (k, l)))
      (SetLike.mul_mem_graded (ProjSpace.X_mem_one R N (idx n p (i, j)))
        (ProjSpace.X_mem_one R N (idx n p (k, l)))) (by decide)
  have hleft :
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
        (ProjSpace.X_mem_one R N (idx n p (k, l)))
        (rfl : (X (idx n p (i, j)) * X (idx n p (k, l))
          : MvPolynomial (Fin (N + 1)) R) = _))) ≫ ιij = ιboth :=
    Proj.SpecMap_awayMap_awayι (𝒜 := 𝒜ᶻ)
      (ProjSpace.X_mem_one R N (idx n p (i, j))) one_pos
      (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl
  have hright :
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
        (ProjSpace.X_mem_one R N (idx n p (i, j)))
        (mul_comm (X (idx n p (i, j))) (X (idx n p (k, l)))))) ≫ ιkl = ιboth :=
    Proj.SpecMap_awayMap_awayι (𝒜 := 𝒜ᶻ)
      (ProjSpace.X_mem_one R N (idx n p (k, l))) one_pos
      (ProjSpace.X_mem_one R N (idx n p (i, j)))
      (mul_comm (X (idx n p (i, j))) (X (idx n p (k, l))))
  have hleft' : φ_ij ≫ ιij = ηz' ≫ ιboth :=
    ((congrArg
      (fun f : W ⟶ Spec (.of (Away 𝒜ᶻ (X (idx n p (i, j))))) => f ≫ ιij)
      hstar1.symm).trans
      (Category.assoc ηz'
        (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
          (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl))) ιij)).trans
      (congrArg
        (fun f : Spec (.of (Away 𝒜ᶻ
            (X (idx n p (i, j)) * X (idx n p (k, l))))) ⟶ Proj 𝒜ᶻ => ηz' ≫ f)
        hleft)
  have hright' : φ_kl ≫ ιkl = ηz' ≫ ιboth :=
    ((congrArg
      (fun f : W ⟶ Spec (.of (Away 𝒜ᶻ (X (idx n p (k, l))))) => f ≫ ιkl)
      hstar2.symm).trans
      (Category.assoc ηz'
        (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
          (ProjSpace.X_mem_one R N (idx n p (i, j)))
          (mul_comm (X (idx n p (i, j))) (X (idx n p (k, l))))))) ιkl)).trans
      (congrArg
        (fun f : Spec (.of (Away 𝒜ᶻ
            (X (idx n p (i, j)) * X (idx n p (k, l))))) ⟶ Proj 𝒜ᶻ => ηz' ≫ f)
        hright)
  exact hleft'.trans hright'.symm

private def coverChartMap (ij : (prodCover R n p).I₀) :
    (prodCover R n p).X ij ⟶ Proj 𝒜ᶻ :=
  chartMap R n p ij.1 ij.2

private theorem coverChartMap_compat (ij kl : (prodCover R n p).I₀) :
    pullback.fst ((prodCover R n p).f ij) ((prodCover R n p).f kl) ≫
        coverChartMap R n p ij =
      pullback.snd _ _ ≫ coverChartMap R n p kl :=
  chartMap_compat R n p ij kl

/-- The Segre morphism obtained by gluing its affine-chart descriptions. -/
def segre2 :
    pullback (ProjSpace.π R n) (ProjSpace.π R p) ⟶ Proj 𝒜ᶻ :=
  (prodCover R n p).glueMorphisms (coverChartMap R n p) (coverChartMap_compat R n p)

private theorem chartInclusion_segre2 (i : Fin (n + 1)) (j : Fin (p + 1)) :
    chartInclusion R n p i j ≫ segre2 R n p = chartMap R n p i j :=
  (prodCover R n p).ι_glueMorphisms
    (coverChartMap R n p) (coverChartMap_compat R n p) (i, j)

theorem segre2_over :
    segre2 R n p ≫ ProjSpace.π R N
      = pullback.fst _ _ ≫ ProjSpace.π R n := by
  refine (prodCover R n p).hom_ext _ _ (fun ij => ?_)
  rw [segre2, ← Category.assoc, Scheme.Cover.ι_glueMorphisms]
  exact chartMap_over R n p ij


theorem segre2_preimage (i : Fin (n + 1)) (j : Fin (p + 1)) :
    segre2 R n p
        ⁻¹ᵁ (Proj.awayι 𝒜ᶻ (X (idx n p (i, j)))
          (ProjSpace.X_mem_one R N _) one_pos).opensRange
      = (chartInclusion R n p i j).opensRange := by
  rw [Proj.opensRange_awayι, opensRange_prodCover_f R n p (i, j),
    Proj.opensRange_awayι, Proj.opensRange_awayι]
  have hchart : ∀ (k : Fin (n + 1)) (l : Fin (p + 1)),
      chartInclusion R n p k l
        ⁻¹ᵁ (segre2 R n p
          ⁻¹ᵁ Proj.basicOpen 𝒜ᶻ (X (idx n p (i, j))))
      = chartInclusion R n p k l
        ⁻¹ᵁ (pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)
            ⁻¹ᵁ Proj.basicOpen 𝒜ˣ (X i)
          ⊓ pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)
            ⁻¹ᵁ Proj.basicOpen 𝒜ʸ (X j)) := fun k l => by
    rw [← Scheme.Hom.comp_preimage (chartInclusion R n p k l) (segre2 R n p),
      chartInclusion_segre2]
    rw [Scheme.Hom.preimage_inf,
      ← Scheme.Hom.comp_preimage (chartInclusion R n p k l)
        (pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)),
      ← Scheme.Hom.comp_preimage (chartInclusion R n p k l)
        (pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)),
      prodCover_fst R n p (k, l), prodCover_snd R n p (k, l)]
    erw [← chartIso_incL_assoc R n p k l, ← chartIso_incR_assoc R n p k l]
    simp only [chartMap, Scheme.Hom.comp_preimage,
      Proj.awayι_preimage_basicOpen 𝒜ᶻ
        (ProjSpace.X_mem_one R N (idx n p (k, l))) one_pos
        (ProjSpace.X_mem_one R N (idx n p (i, j))) one_pos,
      Proj.awayι_preimage_basicOpen 𝒜ˣ (ProjSpace.X_mem_one R n k) one_pos
        (ProjSpace.X_mem_one R n i) one_pos,
      Proj.awayι_preimage_basicOpen 𝒜ʸ (ProjSpace.X_mem_one R p l) one_pos
        (ProjSpace.X_mem_one R p j) one_pos,
      isLocElem_ratio]
    exact (congrArg
      (fun U : (Spec (.of (Tij R n p k l))).Opens =>
        (chartIso R n p k l).hom ⁻¹ᵁ U)
      (segreChart_preimage_ratio R n p k i l j)).trans
      (Scheme.Hom.preimage_inf (chartIso R n p k l).hom)
  have hcov := (prodCover R n p).iSup_opensRange
  refine le_antisymm (fun q hq => ?_) (fun q hq => ?_)
  all_goals
    obtain ⟨⟨k, l⟩, q', rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show q ∈ ⨆ α, ((prodCover R n p).f α).opensRange from hcov.ge trivial)
  · exact (hchart k l).le hq
  · exact (hchart k l).ge hq


theorem segre2_closedImm :
    IsClosedImmersion (segre2 R n p) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (𝒰 := (ProjSpace.affineOpenCover R N).openCover) (fun β => ?_)
  dsimp only [Scheme.Cover.pullbackHom]
  obtain ⟨⟨i, j⟩, hβ⟩ := (idx n p).surjective β
  subst hβ
  change IsClosedImmersion (pullback.snd (segre2 R n p)
    (Proj.awayι 𝒜ᶻ (X (idx n p (i, j))) (ProjSpace.X_mem_one R N _) one_pos))
  have hrange : Set.range (chartInclusion R n p i j).base
      = Set.range (pullback.fst (segre2 R n p)
        ((Proj.awayι 𝒜ᶻ (X (idx n p (i, j))) (ProjSpace.X_mem_one R N (idx n p (i, j)))
            one_pos))).base := by
    have := segre2_preimage R n p i j
    rw [← Scheme.Hom.opensRange_pullbackFst] at this
    exact congrArg SetLike.coe this.symm
  let e := IsOpenImmersion.isoOfRangeEq (chartInclusion R n p i j)
    (pullback.fst _ _) hrange
  have hθcond : chartInclusion R n p i j ≫ segre2 R n p
      = ((chartIso R n p i j).hom
          ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j)))
        ≫ (Proj.awayι 𝒜ᶻ (X (idx n p (i, j))) (ProjSpace.X_mem_one R N (idx n p (i, j)))
            one_pos) := by
    rw [chartInclusion_segre2]
    exact (Category.assoc _ _ _).symm
  let θ := pullback.lift (chartInclusion R n p i j)
    ((chartIso R n p i j).hom
      ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))) hθcond
  have hsnd : e.hom ≫ pullback.snd (segre2 R n p)
        ((Proj.awayι 𝒜ᶻ (X (idx n p (i, j))) (ProjSpace.X_mem_one R N (idx n p (i, j))) one_pos))
      = (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j)) := by
    rw [show e.hom = θ from (cancel_mono (pullback.fst _ _)).mp
      ((IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).trans (pullback.lift_fst _ _ _).symm)]
    exact pullback.lift_snd _ _ _
  have hci : IsClosedImmersion (e.hom ≫ pullback.snd (segre2 R n p)
      ((Proj.awayι 𝒜ᶻ (X (idx n p (i, j))) (ProjSpace.X_mem_one R N (idx n p (i, j))) one_pos)))
          := by
    rw [hsnd]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
      (chartIso R n p i j).hom _).mpr
      (IsClosedImmersion.spec_of_surjective _ (segreChart_surjective R n p i j))
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) e.hom _).mp hci

end ProductCover

section Recursive

variable (R : Type u) [CommRing R]

/-- A closed immersion of a finite product of projective spaces into projective space. -/
structure SegreDatum {m : ℕ} (e : Fin m → ℕ) where

  /-- The dimension of the target projective space. -/
  Nd : ℕ

  /-- The Segre immersion into the target projective space. -/
  segσ : ProjSpace.prodOver R e
    ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Nd + 1)) R)

  /-- The Segre morphism is a closed immersion. -/
  hσ_closed : IsClosedImmersion segσ

  /-- The Segre morphism commutes with the structure maps to the base. -/
  hσ_over : segσ ≫ ProjSpace.π R Nd = ProjSpace.prodOverπ R e

attribute [scoped instance] SegreDatum.hσ_closed

/-- Evaluate the sole homogeneous coordinate at one in the ring of global sections. -/
def eval0 : MvPolynomial (Fin (0 + 1)) R →+* Γ(Spec (.of R), ⊤) :=
  (Scheme.ΓSpecIso (.of R)).inv.hom.comp
    ((MvPolynomial.aeval (R := R) (fun _ => (1 : R))).toRingHom)

theorem eval0_irrelevant :
    (HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin (0 + 1)) R)).toIdeal.map (eval0 R) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hX0 : eval0 R (X 0) = 1 := by
    unfold eval0
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X]
    exact map_one _
  rw [← hX0]
  refine Ideal.mem_map_of_mem _ ?_
  exact (HomogeneousIdeal.mem_irrelevant_iff _ _).mpr
    (DirectSum.decompose_of_mem_ne _ (ProjSpace.X_mem_one R 0 0) one_ne_zero)

theorem eval0_grad0 :
    ((eval0 R).comp
        (algebraMap ((homogeneousSubmodule (Fin (0 + 1)) R) 0)
          (MvPolynomial (Fin (0 + 1)) R))).comp
      (ProjSpace.grad0Equiv R 0).toRingHom
      = (Scheme.ΓSpecIso (.of R)).inv.hom := by
  ext r
  change (eval0 R) (algebraMap _ _ ((ProjSpace.grad0Equiv R 0) r)) = _
  have hval : (algebraMap ((homogeneousSubmodule (Fin (0 + 1)) R) 0)
      (MvPolynomial (Fin (0 + 1)) R)) ((ProjSpace.grad0Equiv R 0) r) = MvPolynomial.C r := rfl
  rw [hval, eval0, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, MvPolynomial.aeval_C]
  rfl

theorem segreAux0_section :
    Proj.fromOfGlobalSections (homogeneousSubmodule (Fin (0 + 1)) R)
        (eval0 R) (eval0_irrelevant R)
      ≫ ProjSpace.π R 0 = 𝟙 (Spec (.of R)) := by
  rw [ProjSpace.π, ← Category.assoc, Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    eval0_grad0, CommRingCat.ofHom_hom]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv (.of R)

/-- Segre data for the empty product of projective spaces. -/
def segreAux0 : SegreDatum R (Fin.elim0 : Fin 0 → ℕ) where
  Nd := 0
  segσ := Proj.fromOfGlobalSections (homogeneousSubmodule (Fin (0 + 1)) R)
    (eval0 R) (eval0_irrelevant R)
  hσ_closed := by
    have hsep : IsSeparated (ProjSpace.π R 0) :=
      (ProjSpace.isProper_π R 0).toIsSeparated
    have hcomp : IsClosedImmersion (Proj.fromOfGlobalSections (homogeneousSubmodule (Fin (0 + 1)) R)
        (eval0 R) (eval0_irrelevant R)
        ≫ ProjSpace.π R 0) := by
      rw [segreAux0_section R]; infer_instance
    exact @IsClosedImmersion.of_comp _ _ _ _ (ProjSpace.π R 0) hcomp hsep
  hσ_over := by
    change _ = 𝟙 (Spec (.of R))
    exact segreAux0_section R

private def segreStep {m : ℕ} (e : Fin (m + 1) → ℕ)
    (ih : SegreDatum R (e ∘ Fin.succ)) :
    ProjSpace.prodOver R e ⟶ pullback (ProjSpace.π R (e 0)) (ProjSpace.π R ih.Nd) :=
  pullback.map (ProjSpace.π R (e 0)) (ProjSpace.prodOverπ R (e ∘ Fin.succ))
    (ProjSpace.π R (e 0)) (ProjSpace.π R ih.Nd)
    (𝟙 _) ih.segσ (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans ih.hσ_over.symm)

/-- Extend Segre data by one projective-space factor. -/
def segreAuxSucc {m : ℕ} (e : Fin (m + 1) → ℕ)
    (ih : SegreDatum R (e ∘ Fin.succ)) : SegreDatum R e where
  Nd := bigN (e 0) ih.Nd
  segσ := segreStep R e ih ≫ segre2 R (e 0) ih.Nd
  hσ_closed := by
    have : IsClosedImmersion (segreStep R e ih) := by
      change IsClosedImmersion (pullback.map (ProjSpace.π R (e 0))
        (ProjSpace.prodOverπ R (e ∘ Fin.succ)) (ProjSpace.π R (e 0))
        (ProjSpace.π R ih.Nd) (𝟙 _) ih.segσ (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.comp_id _).trans ih.hσ_over.symm))
      refine MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsClosedImmersion)
        (f := pullback.snd (ProjSpace.π R (e 0)) (ProjSpace.π R ih.Nd))
        (f' := pullback.snd _ _) ?_ ih.hσ_closed
      refine (IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback (ProjSpace.π R (e 0)) (ProjSpace.π R ih.Nd))).flip
      rw [pullback.lift_fst, Category.comp_id, ih.hσ_over]
      exact IsPullback.of_hasPullback _ _
    have : IsClosedImmersion (segre2 R (e 0) ih.Nd) := segre2_closedImm R (e 0) ih.Nd
    exact IsClosedImmersion.comp (segreStep R e ih) (segre2 R (e 0) ih.Nd)
  hσ_over := by
    rw [Category.assoc, segre2_over, ← Category.assoc]
    have hfst : segreStep R e ih ≫
        pullback.fst (ProjSpace.π R (e 0)) (ProjSpace.π R ih.Nd) =
        pullback.fst (ProjSpace.π R (e 0)) (ProjSpace.prodOverπ R (e ∘ Fin.succ)) :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    exact congrArg
      (fun f : ProjSpace.prodOver R e ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Fin (e 0 + 1)) R) =>
          f ≫ ProjSpace.π R (e 0)) hfst

/-- Construct Segre data recursively for a finite product of projective spaces. -/
def segreAux : ∀ {_m : ℕ} (e : Fin _m → ℕ), SegreDatum R e
  | 0, e => (funext (fun k => k.elim0) : e = Fin.elim0) ▸ segreAux0 R
  | _m + 1, e => segreAuxSucc R e (segreAux (e ∘ Fin.succ))

end Recursive

end ProjSpace.Segre

section Converter

open ProjSpace.Segre

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

namespace ChowDatum
open _root_.AlgebraicGeometry.ChowDatum
end ChowDatum
namespace ChowDatum
open scoped _root_.AlgebraicGeometry.ChowDatum in
private def _root_.AlgebraicGeometry.ChowDatum.toChowDatumProj (D : ChowDatum π) : ChowDatumProj
    π where
  Nd := (segreAux R D.e).Nd
  V' := D.V'
  p := D.p
  ιN := D.ι ≫ (segreAux R D.e).segσ
  hp_proper := D.hp_proper
  hιN_closed := by
    have := D.hι_closed
    have := (segreAux R D.e).hσ_closed
    exact IsClosedImmersion.comp D.ι (segreAux R D.e).segσ
  hoverN := by
    rw [Category.assoc, (segreAux R D.e).hσ_over, D.hover]
  U := D.U
  hU_dense := D.hU_dense
  hp_isoU := D.hp_isoU

end ChowDatum
open _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry.ChowDatum in
theorem ChowDatum.nonempty_chowDatumProj_of :
    Nonempty (ChowDatum π) → Nonempty (ChowDatumProj π) :=
  fun ⟨D⟩ => ⟨D.toChowDatumProj π⟩

open scoped _root_.AlgebraicGeometry.ChowDatum in
/-- The concrete Segre conversion preserves the integral source and the
surjective modification map of the constructed Chow datum. -/
theorem ChowDatum.exists_integral_chowDatumProj [IsProper π] [IsIntegral V] :
    ∃ D : ChowDatumProj π, IsIntegral D.V' ∧ Surjective D.p := by
  obtain ⟨D, hIntegral, hSurjective⟩ := _root_.AlgebraicGeometry.ChowDatum.exists_integral π
  exact ⟨D.toChowDatumProj π, hIntegral, hSurjective⟩

end Converter

end AlgebraicGeometry

/-- A proper integral scheme over any ring admits an integral projective
proper cover, with the actual surjective morphism retained. -/
theorem _root_.AlgebraicGeometry.ChowDatumProj.exists_integral {R : Type u} [CommRing R]
    {V : AlgebraicGeometry.Scheme.{u}}
    (π : V ⟶ AlgebraicGeometry.Spec (.of R)) [AlgebraicGeometry.IsProper π]
    [AlgebraicGeometry.IsIntegral V] :
    ∃ D : AlgebraicGeometry.ChowDatumProj π,
      AlgebraicGeometry.IsIntegral D.V' ∧ AlgebraicGeometry.Surjective D.p :=
  AlgebraicGeometry.ChowDatum.exists_integral_chowDatumProj π

theorem _root_.AlgebraicGeometry.ChowDatumProj.nonempty_of {R : Type u} [CommRing R]
    {V : AlgebraicGeometry.Scheme.{u}}
    (π : V ⟶ AlgebraicGeometry.Spec (.of R)) :
    Nonempty (AlgebraicGeometry.ChowDatum π) → Nonempty (AlgebraicGeometry.ChowDatumProj π) :=
  AlgebraicGeometry.ChowDatum.nonempty_chowDatumProj_of π

end
end AlgebraicCurves.Geometry.Schemes.Proofs.ChowDatumProj_nonempty_of
end ProofImplementation
