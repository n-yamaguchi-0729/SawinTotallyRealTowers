/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.EpiMono

/-!
# A finite open affine factor is a quotient

If an affine open subscheme is finite over a common base, its map into any
intermediate affine scheme is finite. An open immersion is a monomorphism,
so the corresponding finite ring epimorphism is surjective. Together with
the idempotent quotient decomposition this extracts an actual algebra factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgHom

/-- An algebra map inducing an open immersion on spectra is surjective if
its target is finite over the common base. The source need not be finite. -/
theorem surjective_of_finite_of_isOpenImmersion
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Finite R B] (f : A →ₐ[R] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))] :
    Function.Surjective f := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom f.toRingHom
  let ρ : CommRingCat.of R ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap R A)
  have hcomp : ρ ≫ φ = CommRingCat.ofHom (algebraMap R B) := by
    ext r
    exact f.commutes r
  have : IsFinite (Spec.map φ ≫ Spec.map ρ) := by
    rw [← Spec.map_comp, hcomp]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : IsFinite (Spec.map φ) := IsFinite.of_comp (Spec.map φ) (Spec.map ρ)
  have : Mono φ.op :=
    (Functor.mono_map_iff_mono Scheme.Spec φ.op).mp
      (inferInstance : Mono (Spec.map φ))
  have : Epi φ := inferInstanceAs (Epi φ.op.unop)
  exact (RingHom.surjective_iff_epi_and_finite (f := φ)).mpr
    ⟨inferInstance, (IsFinite.SpecMap_iff φ).mp inferInstance⟩

end AlgHom
