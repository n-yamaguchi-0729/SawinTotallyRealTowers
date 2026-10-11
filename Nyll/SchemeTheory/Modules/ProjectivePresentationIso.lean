/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.Modules.ProjectivePresentation

/-!
# Scheme Modules Proj Presentation exists of iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_ProjPresentation_exists_of_iso

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

open Opposite

namespace PresIso

variable {X : Scheme.{u}} {M M' : X.Modules}

theorem map_app (φ : M ⟶ M') {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    M'.presheaf.map i.op (φ.app U s) = φ.app V (M.presheaf.map i.op s) := by
  have h := φ.mapPresheaf.naturality i.op
  have := congrArg (fun f => (ConcreteCategory.hom f) s) h
  simpa using this.symm

theorem app_bijective (e : M ≅ M') (U : X.Opens) : Function.Bijective (e.hom.app U) :=
  ConcreteCategory.bijective_of_isIso (e.hom.app U)

/-- Transport a projective presentation across `e`, retaining its projective-space morphism and
mapping its global sections by `e.hom`. -/
noncomputable def transport {R : Type u} [CommRing R] {f : X ⟶ Spec (.of R)} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (e : M ≅ M') : M'.ProjPresentation f N where
  σ := fun i => e.hom.app ⊤ (𝔓.σ i)
  toProj := 𝔓.toProj
  toProj_π := 𝔓.toProj_π
  frame := fun i V hV => by
    have key : (fun g : Γ(X, V) => g • M'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (e.hom.app ⊤
      (𝔓.σ i)))
        = (e.hom.app V) ∘ (fun g : Γ(X, V) => g • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ
          i)) := by
      funext g
      simp only [Function.comp_apply, map_app, Scheme.Modules.Hom.app_smul]
    rw [key]
    exact (app_bijective e V).comp (𝔓.frame i V hV)
  app_ratio_smul := fun i j => by
    rw [map_app, map_app, ← Scheme.Modules.Hom.app_smul, 𝔓.app_ratio_smul i j]

end PresIso

theorem _root_.AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M M' : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (e : M ≅ M') :
    ∃ 𝔓' : M'.ProjPresentation f N, 𝔓'.toProj = 𝔓.toProj ∧ ∀ i, 𝔓'.σ i = (e.hom.app ⊤) (𝔓.σ i) :=
  ⟨PresIso.transport 𝔓 e, rfl, fun _ => rfl⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_ProjPresentation_exists_of_iso
end ProofImplementation
