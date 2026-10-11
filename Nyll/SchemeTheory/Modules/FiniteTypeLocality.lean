/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou; Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.CategoryTheory.Sites.CoversTop.Over

/-!
# Locality of finite type for sheaves of modules

The native finite-type condition is preserved under isomorphisms and can
be checked on a covering family. The proof composes the actual covers and
transports the actual finite families of generating sections through the
canonical equivalence between iterated slice sites.

The iterated-slice cover composition is adapted from the native
quasicoherent-data construction at Mathlib revision
065356127b1dc0016f66b7283ce0ce2c4055aa55:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean
-/

noncomputable section

universe w u v₁ u₁

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transport the actual local generating sections along an isomorphism. -/
def LocalGeneratorsData.ofIso {M N : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) (e : M ≅ N) : N.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi ((overFunctor R (q.X i)).mapIso e).hom

/-- Isomorphism transport keeps the same finite indexing family at each object. -/
lemma LocalGeneratorsData.isFiniteType_ofIso {M N : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) (e : M ≅ N) (hq : q.IsFiniteType) :
    (q.ofIso e).IsFiniteType := by
  constructor
  intro i
  exact ⟨(hq.isFiniteType i).finite⟩

/-- Shrinking the cover does not change any chosen finite generating family. -/
lemma LocalGeneratorsData.isFiniteType_shrink {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) (hq : q.IsFiniteType) : q.shrink.IsFiniteType := by
  constructor
  intro i
  exact hq.isFiniteType i.2.choose

/-- A finite family of actual local generators supplies the native finite-type predicate. -/
lemma LocalGeneratorsData.isFiniteType {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) (hq : q.IsFiniteType) : M.IsFiniteType :=
  ⟨q.shrink, q.isFiniteType_shrink hq⟩

/-- Finite type is preserved by an isomorphism of sheaves of modules. -/
lemma IsFiniteType.of_iso {M N : SheafOfModules.{u} R}
    (e : M ≅ N) (hM : M.IsFiniteType) : N.IsFiniteType := by
  have : M.IsFiniteType := hM
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  exact (q.ofIso e).isFiniteType (q.isFiniteType_ofIso e hq)

section Covers

variable [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Compose a cover and the actual local generating data on its slice sites. -/
def LocalGeneratorsData.bind (M : SheafOfModules.{u} R) {I : Type w}
    (X : I → C) (hX : J.CoversTop X)
    (q : ∀ i, (M.over (X i)).LocalGeneratorsData) : M.LocalGeneratorsData where
  I := (i : I) × (q i).I
  X ij := ((q ij.1).X ij.2).left
  coversTop := hX.over (fun i => (q i).coversTop)
  generators ij := by
    let e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv ((q ij.1).X ij.2))
      (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
    let t := ((q ij.1).generators ij.2).map e.inverse (Iso.refl _)
    exact t.ofEpi (e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over (X ij.1)).over ((q ij.1).X ij.2)))).hom

/-- Composition of covers retains finiteness of every generating family. -/
lemma LocalGeneratorsData.isFiniteType_bind (M : SheafOfModules.{u} R) {I : Type w}
    (X : I → C) (hX : J.CoversTop X)
    (q : ∀ i, (M.over (X i)).LocalGeneratorsData)
    (hq : ∀ i, (q i).IsFiniteType) : (LocalGeneratorsData.bind M X hX q).IsFiniteType := by
  constructor
  intro ij
  exact ⟨((hq ij.1).isFiniteType ij.2).finite⟩

/-- Finite type can be checked on any covering family of slice sites. -/
lemma IsFiniteType.of_coversTop (M : SheafOfModules.{u} R) {I : Type w}
    (X : I → C) (hX : J.CoversTop X)
    (hM : ∀ i, (M.over (X i)).IsFiniteType) : M.IsFiniteType := by
  have h : ∀ i, ∃ q : LocalGeneratorsData (M.over (X i)), q.IsFiniteType := by
    intro i
    have : (M.over (X i)).IsFiniteType := hM i
    exact IsFiniteType.exists_localGeneratorsData (M.over (X i))
  let q := fun i => (h i).choose
  have hq : ∀ i, (q i).IsFiniteType := fun i => (h i).choose_spec
  exact (LocalGeneratorsData.bind M X hX q).isFiniteType
    (LocalGeneratorsData.isFiniteType_bind M X hX q hq)

end Covers

end SheafOfModules
