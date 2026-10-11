/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesProjPresentation.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Presentations by twists on projective space

A projective presentation describes a module as a quotient of a finite sum of twists
of the structure sheaf. Pullbacks and tensor powers of twists retain these presentations.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- A map to projective space with global sections of `M` that give frames on the standard
    charts and satisfy coordinate-ratio equations. -/
structure ProjPresentation (M : X.Modules) (f : X ⟶ Spec (.of R)) (N : ℕ) where
  /-- The chosen global sections whose restrictions give the coordinate frames. -/
  σ : Fin (N + 1) → Γ(M, ⊤)
  /-- The morphism to projective space presented by the sections `σ`. -/
  toProj : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
  /-- The projective-space morphism lies over the specified map `f`. -/
  toProj_π : toProj ≫ ProjSpace.π R N = f
  /-- Each `σ i` restricts to a frame on every open contained in the preimage of the `i`th
      standard chart. -/
  frame : ∀ (i : Fin (N + 1)) (V : X.Opens),
    V ≤ toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i) →
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ
        i) : Γ(M, V))
  /-- Pulling back a coordinate ratio on the `i`th chart expresses `σ j` as that ratio times `σ
      i`. -/
  app_ratio_smul : ∀ i j : Fin (N + 1),
    (toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i))
        (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) •
        M.presheaf.map (homOfLE (le_top : toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
              ≤ ⊤)).op (σ i)
      = M.presheaf.map (homOfLE (le_top : toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
              ≤ ⊤)).op (σ j)

/-- The module sheaf admits a presentation by global sections whose map to projective space is
    finite. -/
def FiniteBySections (M : X.Modules) (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (N : ℕ) (𝔓 : M.ProjPresentation f N), IsFinite 𝔓.toProj

/-- The module sheaf admits a presentation by global sections whose map to projective space is a
    closed immersion. -/
def ClosedImmersionBySections (M : X.Modules) (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (N : ℕ) (𝔓 : M.ProjPresentation f N), IsClosedImmersion 𝔓.toProj

end Scheme.Modules

namespace ProjSpace

variable (R : Type u) [CommRing R]

/-- The homomorphism from the standard chart ring of projective zero-space to `R` induced by
    sending its single variable to `1`. -/
def awayZeroEval :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0 :
        MvPolynomial (Fin 1) R) →+* R :=
  (IsLocalization.Away.lift (S := Localization.Away (X 0 : MvPolynomial (Fin 1) R))
      (X 0 : MvPolynomial (Fin 1) R)
      (g := (MvPolynomial.aeval (R := R) (fun _ : Fin 1 => (1 : R))).toRingHom)
      (by simp)).comp
    (algebraMap (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0
        : MvPolynomial (Fin 1) R))
      (Localization.Away (X 0 : MvPolynomial (Fin 1) R)))

/-- The `R`-point of projective zero-space obtained by evaluating its single homogeneous
    coordinate at `1`. -/
def pointOfProjZero : Spec (.of R) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 1) R) :=
  Spec.map (CommRingCat.ofHom (awayZeroEval R)) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R 0 0) one_pos

theorem pointOfProjZero_π : pointOfProjZero R ≫ π R 0 = 𝟙 _ := by
  rw [pointOfProjZero, Category.assoc, awayι_comp_π, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext r : 2
  change awayZeroEval R (algebraMap R _ r) = r
  simp only [awayZeroEval, RingHom.coe_comp, Function.comp_apply]
  rw [HomogeneousLocalization.algebraMap_apply, val_algebraMap, IsLocalization.Away.lift_eq]
  simp

theorem pointOfProjZero_preimage_basicOpen :
    pointOfProjZero R ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) = ⊤
        := by
  rw [pointOfProjZero, Scheme.Hom.comp_preimage]
  have : Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R 0 0)
      one_pos ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) = ⊤ := by
    rw [← Proj.opensRange_awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R
        0 0) one_pos]
    exact Scheme.Hom.preimage_opensRange _
  rw [this]
  rfl

end ProjSpace

variable (R : Type u) [CommRing R]

/-- The global section `1` of the unit module sheaf on `X`. -/
def Scheme.Modules.unitOne (X : Scheme.{u}) :
    Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), (⊤ : X.Opens)) :=
  (show Γ(X, ⊤) from 1)

/-- The presentation of the unit module sheaf on `Spec R` by its single global section `1` in
    projective zero-space. -/
def Scheme.Modules.ProjPresentation.unitSpec :
    Scheme.Modules.ProjPresentation (SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec
        (.of R)).Modules)
      (𝟙 (Spec (.of R))) 0 where
  σ := fun _ => Scheme.Modules.unitOne (Spec (.of R))
  toProj := ProjSpace.pointOfProjZero R
  toProj_π := ProjSpace.pointOfProjZero_π R
  frame := fun i V _ => by
    have h : (Scheme.Modules.presheaf (SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec
        (.of R)).Modules)).map
        (homOfLE (le_top : V ≤ ⊤)).op (Scheme.Modules.unitOne (Spec (.of R)))
        = (show Γ(Spec (.of R), V) from 1) := by
      change ((Spec (.of R)).ringCatSheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom 1 = 1
      exact map_one _
    rw [h]
    change Function.Bijective fun g : Γ(Spec (.of R), V) => g * 1
    simp only [mul_one]
    exact Function.bijective_id
  app_ratio_smul := fun i j => by
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst hi hj
    rw [ProjSpace.ratio_self, map_one, map_one, one_smul]

end AlgebraicGeometry

end
