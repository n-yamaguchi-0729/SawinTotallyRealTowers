/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteTypeQuotient
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.Basic.Finite.Sum

/-!
# Finite type of binary coproducts

The product of the two original local generating covers is again a cover.
On each product chart both finite generating families restrict, and their
disjoint union generates the actual categorical coproduct.
-/

noncomputable section

universe u v u₁

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Generators of both summands give generators indexed by their disjoint union. -/
def GeneratingSections.coprod {M N : SheafOfModules.{u} R}
    (p : M.GeneratingSections) (q : N.GeneratingSections) :
    (M ⨿ N).GeneratingSections where
  I := p.I ⊕ q.I
  s := (M ⨿ N).freeHomEquiv
    ((freeSumIso (R := R) p.I q.I).inv ≫ Limits.coprod.map p.π q.π)
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

instance {M N : SheafOfModules.{u} R}
    (p : M.GeneratingSections) (q : N.GeneratingSections)
    [p.IsFiniteType] [q.IsFiniteType] : (p.coprod q).IsFiniteType where
  finite := inferInstanceAs (Finite (p.I ⊕ q.I))

variable [HasBinaryProducts C] [HasPullbacks C]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restrict a generating family further along a map of charts. -/
def GeneratingSections.restrict {M : SheafOfModules.{u} R} {X Y : C}
    (p : (M.over Y).GeneratingSections) (f : X ⟶ Y) :
    (M.over X).GeneratingSections :=
  (p.map (overMap R f) (overMapUnitIso (R := R) f).symm).ofEpi
    ((overFunctorMap R f).app M).hom

instance {M : SheafOfModules.{u} R} {X Y : C}
    (p : (M.over Y).GeneratingSections) (f : X ⟶ Y) [p.IsFiniteType] :
    (p.restrict f).IsFiniteType :=
  inferInstanceAs
    ((p.map (overMap R f) (overMapUnitIso (R := R) f).symm).ofEpi
      ((overFunctorMap R f).app M).hom).IsFiniteType

private def coprodChartGenerators {M N : SheafOfModules.{u} R}
    (p : M.LocalGeneratorsData) (q : N.LocalGeneratorsData) (i : p.I) (j : q.I) :
    ((M ⨿ N).over (p.X i ⨯ q.X j)).GeneratingSections := by
  have : PreservesColimitsOfSize.{u, u} (overFunctor R (p.X i ⨯ q.X j)) :=
    (overPushforwardOverAdj (R := R) (p.X i ⨯ q.X j)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (overFunctor R (p.X i ⨯ q.X j)) :=
    PreservesColimitsOfSize.preservesFiniteColimits (overFunctor R (p.X i ⨯ q.X j))
  exact ((p.generators i).restrict (Limits.prod.fst : p.X i ⨯ q.X j ⟶ p.X i)).coprod
      ((q.generators j).restrict (Limits.prod.snd : p.X i ⨯ q.X j ⟶ q.X j)) |>.ofEpi
    (PreservesColimitPair.iso (overFunctor R (p.X i ⨯ q.X j)) M N).hom

/-- The actual binary coproduct of two finite-type sheaves is finite type. -/
theorem isFiniteType_coprod {M N : SheafOfModules.{u} R}
    [M.IsFiniteType] [N.IsFiniteType] : (M ⨿ N).IsFiniteType := by
  obtain ⟨p, hp⟩ := IsFiniteType.exists_localGeneratorsData M
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData N
  let r : (M ⨿ N).LocalGeneratorsData :=
    { I := p.I × q.I
      X := fun ij => p.X ij.1 ⨯ q.X ij.2
      coversTop := by
        intro Z
        apply J.superset_covering ?_
          (J.intersection_covering (p.coversTop Z) (q.coversTop Z))
        intro W f hf
        obtain ⟨⟨i, ⟨a⟩⟩, ⟨j, ⟨b⟩⟩⟩ := hf
        exact ⟨(i, j), ⟨Limits.prod.lift a b⟩⟩
      generators ij := coprodChartGenerators p q ij.1 ij.2 }
  have hr : r.IsFiniteType := by
    constructor
    intro ij
    have : (p.generators ij.1).IsFiniteType := hp.isFiniteType ij.1
    have : (q.generators ij.2).IsFiniteType := hq.isFiniteType ij.2
    constructor
    exact inferInstanceAs (Finite ((p.generators ij.1).I ⊕ (q.generators ij.2).I))
  exact ⟨⟨r, hr⟩⟩

end SheafOfModules
