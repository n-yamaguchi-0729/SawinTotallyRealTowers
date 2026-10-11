/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Universally injective étale morphisms

The diagonal of an étale morphism is an open immersion. Universal injectivity
makes it surjective and hence an isomorphism. The morphism is therefore a
monomorphism, and the flat finite-presentation criterion makes it an open immersion.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Etale

/-- A universally injective étale morphism is an open immersion. -/
theorem isOpenImmersion_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [UniversallyInjective f] :
    IsOpenImmersion f := by
  let : Surjective (pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  let : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective (pullback.diagonal f)).mpr
      ⟨inferInstance, inferInstance⟩
  let : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono f

/-- A surjective universally injective étale morphism is an isomorphism. -/
theorem isIso_of_universallyInjective_of_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [UniversallyInjective f] [Surjective f] :
    IsIso f := by
  exact (isIso_iff_isOpenImmersion_and_surjective f).mpr
    ⟨isOpenImmersion_of_universallyInjective f, inferInstance⟩

end AlgebraicGeometry.Etale
