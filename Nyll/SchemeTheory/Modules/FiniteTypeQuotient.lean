/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Finite type passes to actual epimorphic quotients

The original local generating covers are retained. Restriction to a slice
is a left adjoint, so the actual restricted morphisms are epimorphisms;
their images of the original finite generators generate the quotient.
-/

noncomputable section

universe u v

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An epimorphic quotient of a finite-type sheaf of modules is finite type. -/
theorem isFiniteType_of_epi {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [Epi f] [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨p, hp⟩ := IsFiniteType.exists_localGeneratorsData M
  have hfOver : ∀ X : C, Epi (f.over X) := by
    intro X
    have : (overFunctor R X).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction (overPushforwardOverAdj (R := R) X)
    exact Functor.map_epi (overFunctor R X) f
  let q : N.LocalGeneratorsData :=
    { I := p.I
      X := p.X
      coversTop := p.coversTop
      generators i := (p.generators i).ofEpi (f.over (p.X i)) }
  have hq : q.IsFiniteType := by
    constructor
    intro i
    have : (p.generators i).IsFiniteType := hp.isFiniteType i
    exact inferInstanceAs ((p.generators i).ofEpi (f.over (p.X i))).IsFiniteType
  exact ⟨⟨q, hq⟩⟩

/-- Finite type is transported along an actual isomorphism. -/
theorem isFiniteType_of_iso {M N : SheafOfModules.{u} R}
    (e : M ≅ N) [M.IsFiniteType] : N.IsFiniteType :=
  isFiniteType_of_epi e.hom

end SheafOfModules
