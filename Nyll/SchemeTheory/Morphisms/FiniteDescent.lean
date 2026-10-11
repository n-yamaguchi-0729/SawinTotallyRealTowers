/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Finiteness after surjective descent of an integral composite

If a separated étale morphism becomes integral after precomposition with a
surjective morphism, it is universally closed. It is consequently proper and
locally quasi-finite, hence finite by Zariski's main theorem.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsFinite

/-- A separated étale morphism is finite if it is dominated surjectively by
a scheme whose composite map to the base is integral. -/
theorem of_surjective_of_comp_isIntegralHom
    {U V Y : Scheme.{u}} (h : U ⟶ V) (g : V ⟶ Y)
    [Surjective h] [IsIntegralHom (h ≫ g)] [Etale g] [IsSeparated g] :
    IsFinite g := by
  let : UniversallyClosed g := UniversallyClosed.of_comp_surjective h g
  let : IsProper g := {}
  let : LocallyQuasiFinite g := {
    quasiFinite_appLE := fun {W} hW {Z} hZ e ↦ by
      let φ : Γ(Y, W) →+* Γ(V, Z) := (g.appLE W Z e).hom
      let : Algebra Γ(Y, W) Γ(V, Z) := φ.toAlgebra
      let : Algebra.Etale Γ(Y, W) Γ(V, Z) := g.etale_appLE hW hZ e
      exact inferInstanceAs (Algebra.QuasiFinite Γ(Y, W) Γ(V, Z))
  }
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

end AlgebraicGeometry.IsFinite
