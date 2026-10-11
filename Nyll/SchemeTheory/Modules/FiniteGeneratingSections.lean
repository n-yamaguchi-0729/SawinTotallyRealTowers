/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.QuasicoherentLocal
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite generating sections on an affine scheme

The literal finite free sheaf epimorphism becomes a map from a finite free
module under the fully faithful tilde functor. The actual quasicoherent
counit isomorphism identifies its target with the original global sections.
Faithfulness reflects epimorphisms, so the resulting linear map is surjective.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite family generating a quasicoherent sheaf on `Spec R` makes its
actual global-section module finite over `R`. -/
theorem moduleFinite_moduleSpecΓ_of_generatingSections
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (G : M.GeneratingSections) [G.IsFiniteType] :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M) := by
  let ΓM : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj M
  let ε : (tilde.functor R).obj ΓM ⟶ M := fromTildeΓ (R := R) M
  have : IsIso (C := (Spec R).Modules) ε :=
    isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  let e : (tilde.functor R).obj ΓM ≅ M := asIso (C := (Spec R).Modules) ε
  let P : (Spec R).Modules := SheafOfModules.free G.I
  have : Epi (C := SheafOfModules.{u} (Spec R).ringCatSheaf) G.π := G.epi
  let q : P ⟶ M := (sheafOfModulesEquivalence (Spec R)).inverse.map G.π
  have hq : Epi q :=
    Functor.map_epi (sheafOfModulesEquivalence (Spec R)).inverse G.π
  let F : ModuleCat.{u} R := ModuleCat.of R (G.I →₀ R)
  have : Finite G.I := SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := G)
  have : Module.Finite R F := inferInstanceAs (Module.Finite R (G.I →₀ R))
  let a : (tilde.functor R).obj F ≅ P := tildeFinsupp G.I
  let k : F ⟶ ΓM := (tilde.functor R).preimage (a.hom ≫ q ≫ e.inv)
  have hk : (tilde.functor R).map k = a.hom ≫ q ≫ e.inv :=
    (tilde.functor R).map_preimage (a.hom ≫ q ≫ e.inv)
  have hmap : Epi ((tilde.functor R).map k) :=
    Eq.mp (congrArg Epi hk.symm) (inferInstanceAs (Epi (a.hom ≫ q ≫ e.inv)))
  have : Epi k := (tilde.functor R).epi_of_epi_map hmap
  exact Module.Finite.of_surjective k.hom ((ModuleCat.epi_iff_surjective k).mp inferInstance)

end AlgebraicGeometry.Scheme.Modules
