/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Affine epimorphisms from actual global sections

Surjectivity on global sections of a morphism into a quasicoherent module
over a spectrum implies that the actual sheaf morphism is epimorphic.
The proof uses the native tilde--Gamma counit and preservation of
epimorphisms by tilde; the source need not be quasicoherent.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Surjectivity on actual affine global sections detects an epimorphism
onto a quasicoherent module. -/
theorem epi_of_surjective_moduleSpecΓ {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [N.IsQuasicoherent] (φ : M ⟶ N)
    (hφ : Function.Surjective ((moduleSpecΓFunctor (R := R)).map φ)) : Epi φ := by
  let ΓM : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj M
  let ΓN : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj N
  let γ : ΓM ⟶ ΓN := (moduleSpecΓFunctor (R := R)).map φ
  let εM : (tilde.functor R).obj ΓM ⟶ M := fromTildeΓ (R := R) M
  let εN : (tilde.functor R).obj ΓN ⟶ N := fromTildeΓ (R := R) N
  have : Epi γ := (ModuleCat.epi_iff_surjective γ).mpr hφ
  have : Epi ((tilde.functor R).map γ) := Functor.map_epi (tilde.functor R) γ
  have : IsIso (C := (Spec R).Modules) εN :=
    isIso_fromTildeΓ_of_isQuasicoherent (R := R) N
  let e : (tilde.functor R).obj ΓN ≅ N := asIso (C := (Spec R).Modules) εN
  have : Epi (C := (Spec R).Modules) e.hom := IsIso.epi_of_iso e.hom
  have hnat : (tilde.functor R).map γ ≫ e.hom = εM ≫ φ :=
    (tilde.adjunction (R := R)).counit.naturality φ
  have hcomp : Epi (C := (Spec R).Modules)
      ((tilde.functor R).map γ ≫ e.hom) :=
    epi_comp (C := (Spec R).Modules) ((tilde.functor R).map γ) e.hom
  have : Epi (C := (Spec R).Modules) (εM ≫ φ) :=
    Eq.mp (congrArg (fun g => Epi (C := (Spec R).Modules) g) hnat) hcomp
  exact epi_of_epi εM φ

end AlgebraicGeometry.Scheme.Modules
