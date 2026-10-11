/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
Two affine charts with affine intersection, their section-ring cover and its scalar extension.
-/

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

/-- A cover of X by two affine open subschemes whose intersection is also affine. -/
structure Scheme.TwoAffineOpenCover (X : Scheme.{u}) where
  /-- The first open subset of the cover. -/
  U0 : X.Opens
  /-- The second open subset of the cover. -/
  U1 : X.Opens
  /-- The first open subset is affine. -/
  isAffineOpen_U0 : IsAffineOpen U0
  /-- The second open subset is affine. -/
  isAffineOpen_U1 : IsAffineOpen U1
  /-- The two open subsets cover the whole scheme. -/
  sup_eq_top : U0 ⊔ U1 = ⊤
  /-- The intersection of the two open subsets is affine. -/
  isAffineOpen_inf : IsAffineOpen (U0 ⊓ U1)

namespace Scheme.TwoAffineOpenCover

/-- The morphism of affine schemes induced by the R-algebra structure on A. -/
abbrev specMap (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Spec (.of A) ⟶ Spec (.of
    R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The R-algebra structure on sections over U induced by the morphism c. -/
@[reducible] def algebraOfHom (c : X ⟶ Spec (.of R)) (U : X.Opens) : Algebra R Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom.toAlgebra

theorem algebraMap_algebraOfHom (c : X ⟶ Spec (.of R)) (U : X.Opens) (r : R) :
    (algebraOfHom c U).algebraMap r = (c.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of
      R)).inv.hom r) :=
  rfl

/-- The restriction map on sections as an R-algebra homomorphism for the structures induced by c. -/
def restrictAlgHom (c : X ⟶ Spec (.of R)) {U V : X.Opens} (h : V ≤ U) :
    letI := algebraOfHom c U; letI := algebraOfHom c V
    Γ(X, U) →ₐ[R] Γ(X, V) :=
  letI := algebraOfHom c U; letI := algebraOfHom c V
  { (X.presheaf.map (homOfLE h).op).hom with
    commutes' := fun r => by
      change (c.appLE ⊤ U le_top ≫ X.presheaf.map (homOfLE h).op).hom _ = (c.appLE ⊤ V le_top).hom _
      exact congrArg
        (fun φ => φ.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))
        (Scheme.Hom.appLE_map c (by simp) (homOfLE h).op) }

variable (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

/-- The two-chart algebraic cover formed by the section rings of the affine opens and their
intersection. -/
def cover : TwoChartCech.Cover.{u, u} R :=
  letI := algebraOfHom c 𝒱.U0; letI := algebraOfHom c 𝒱.U1; letI := algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)
  { A0 := Γ(X, 𝒱.U0)
    A1 := Γ(X, 𝒱.U1)
    A01 := Γ(X, 𝒱.U0 ⊓ 𝒱.U1)
    ρ0 := restrictAlgHom c inf_le_left
    ρ1 := restrictAlgHom c inf_le_right }

theorem cover_A0 : (𝒱.cover c).A0 = Γ(X, 𝒱.U0) := rfl
theorem cover_A1 : (𝒱.cover c).A1 = Γ(X, 𝒱.U1) := rfl
theorem cover_A01 : (𝒱.cover c).A01 = Γ(X, 𝒱.U0 ⊓ 𝒱.U1) := rfl
theorem cover_ρ0_apply (x : (𝒱.cover c).A0) :
    (𝒱.cover c).ρ0 x = (X.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op).hom x := rfl
theorem cover_ρ1_apply (x : (𝒱.cover c).A1) :
    (𝒱.cover c).ρ1 x = (X.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op).hom x
      := rfl

/-- The two-chart section data of the structure sheaf. -/
abbrev structureSheafSections : TwoChartCech.Sections (𝒱.cover c) := (𝒱.cover c).structureSheaf

/-- The two-chart section data for the line bundle glued by the unit t on the intersection. -/
abbrev lineBundleSections (t : (𝒱.cover c).A01ˣ) : TwoChartCech.Sections (𝒱.cover c) :=
  (𝒱.cover c).lineBundle t

omit [CommRing R] in
theorem res_res {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (x : Γ(X, V₁)) :
    (X.presheaf.map (homOfLE h₃₂).op).hom ((X.presheaf.map (homOfLE h₂₁).op).hom x) =
      (X.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op).hom x := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem restrict_mem_H0 (s : Γ(X, ⊤)) :
    ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s,
      (X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s)
      ∈ (𝒱.structureSheafSections c).H0 := by
  refine (TwoChartCech.Sections.mem_H0_iff _ _).mpr ?_
  change (X.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op).hom
      ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s)
    = ((1 : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)ˣ) : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)) •
      (X.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op).hom
        ((X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s)
  rw [Units.val_one, one_smul, res_res, res_res]

/-- The map sending a global section to its compatible pair of restrictions in degree-zero Cech
cohomology. -/
def toH0 : letI := algebraOfHom c ⊤; Γ(X, ⊤) →ₗ[R] (𝒱.structureSheafSections c).H0 :=
  letI := algebraOfHom c ⊤; letI := algebraOfHom c 𝒱.U0; letI := algebraOfHom c 𝒱.U1
  LinearMap.codRestrict _
    (((restrictAlgHom c (le_top : 𝒱.U0 ≤ ⊤)).toLinearMap).prod
      ((restrictAlgHom c (le_top : 𝒱.U1 ≤ ⊤)).toLinearMap))
    (fun s => 𝒱.restrict_mem_H0 c s)

theorem toH0_apply_coe (s : Γ(X, ⊤)) :
    letI := algebraOfHom c ⊤
    ((𝒱.toH0 c s : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1)) =
      ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s,
        (X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s) := rfl

section Pullback

variable (A : Type u) [CommRing A] [Algebra R A]

theorem isAffineHom_fst : IsAffineHom (Limits.pullback.fst c (specMap R A)) :=
  letI : MorphismProperty.IsStableUnderBaseChange @IsAffineHom :=
    AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance

/-- The two-affine-open cover obtained by base change along the morphism from Spec A to Spec R. -/
def pullback : (Limits.pullback c (specMap R A)).TwoAffineOpenCover :=
  haveI := isAffineHom_fst c A
  { U0 := (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U0
    U1 := (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U1
    isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage _
    isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage _
    sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
    isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage _ }

@[simp] theorem pullback_U0 : (𝒱.pullback c A).U0 = (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ
    𝒱.U0 := rfl
@[simp] theorem pullback_U1 : (𝒱.pullback c A).U1 = (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ
    𝒱.U1 := rfl

end Pullback

end Scheme.TwoAffineOpenCover

end AlgebraicGeometry

end
