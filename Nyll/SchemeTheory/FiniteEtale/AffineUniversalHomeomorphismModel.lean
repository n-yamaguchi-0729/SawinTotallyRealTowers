/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.IntegralFiniteModel
public import Nyll.SchemeTheory.Morphisms.RadicialDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finite models retaining the universal-homeomorphism property

An actual finite subalgebra model for a finite étale algebra over an integral
extension also retains surjectivity and universal injectivity of the base map.
The larger integral algebra surjects onto this intermediate spectrum by lying
over, so both properties descend through that surjection.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.FiniteEtale

/-- A finite étale algebra over an affine universal homeomorphism has a
model over an actual finite intermediate universal homeomorphism. -/
theorem exists_finite_subalgebra_model_of_universalHomeomorphism
    (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra.IsIntegral R S] [Algebra S A]
    [Module.Finite S A] [Algebra.Etale S A]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    ∃ (S₀ : Subalgebra R S) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra S₀ A₀),
      Module.Finite R S₀ ∧
      UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S₀))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S₀))) ∧
      Module.Finite S₀ A₀ ∧ Algebra.Etale S₀ A₀ ∧
      Nonempty (A ≃ₐ[S] S ⊗[S₀] A₀) := by
  obtain ⟨S₀, A₀, hring, halgebra, hfin, hfin₀, hetale, e⟩ :=
    Algebra.FiniteEtale.exists_finite_subalgebra_model R S A
  let : CommRing A₀ := hring
  let : Algebra S₀ A₀ := halgebra
  let : Algebra.IsIntegral S₀ S := Algebra.IsIntegral.tower_top R
  let t := Spec.map (CommRingCat.ofHom (algebraMap S₀ S))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S₀))
  let : Surjective t := ⟨Algebra.IsIntegral.comap_surjective S₀ S⟩
  have htg : t ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    dsimp only [t, g]
    rw [← Spec.map_comp]
    congr 1
  let : UniversallyInjective (t ≫ g) :=
    htg.symm ▸ inferInstanceAs
      (UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  let : Surjective (t ≫ g) :=
    htg.symm ▸ inferInstanceAs
      (Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  exact ⟨S₀, A₀, hring, halgebra, hfin,
    UniversallyInjective.of_comp_surjective t g, Surjective.of_comp t g,
    hfin₀, hetale, e⟩

end AlgebraicGeometry.FiniteEtale
