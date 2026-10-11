/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Common.FiniteFamilyLinearMap
import Mathlib.Topology.Basic

/-!
# `ProCGroups.CrowellExactSequence.Basic`

Crowell exact sequences / Basic.

This module contains the common four-term linear-sequence interface, exactness transport
lemmas, and the finite Blanchfield--Lyndon coordinate map used by the discrete and profinite
theories.
-/

namespace CrowellExactSequence

noncomputable section

open scoped BigOperators
open FoxDifferential

section BlanchfieldLyndonFiniteFamilyMap

variable {R : Type*} [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The Blanchfield--Lyndon finite-family map associated to a chosen boundary-generating family. -/
abbrev blanchfieldLyndonFiniteFamilyMap (generators : X → M) :
    (X → R) →ₗ[R] M :=
  finiteFamilyLinearMap (R := R) generators

omit [DecidableEq X] in
/--
The Blanchfield--Lyndon finite-family boundary map is evaluated on the canonical generators and
then extended linearly to the coordinate module.
-/
theorem blanchfieldLyndonFiniteFamilyMap_apply (generators : X → M) (x : X → R) :
    blanchfieldLyndonFiniteFamilyMap (R := R) generators x = ∑ i, x i • generators i := rfl

/-- A Blanchfield--Lyndon finite-family map sends a coordinate basis vector to its generator. -/
@[simp]
theorem blanchfieldLyndonFiniteFamilyMap_single (generators : X → M) (i : X) :
    blanchfieldLyndonFiniteFamilyMap (R := R) generators (Pi.single i 1) = generators i :=
  finiteFamilyLinearMap_single (R := R) generators i

end BlanchfieldLyndonFiniteFamilyMap

/-- A bundled four-term sequence of linear maps.  It records the three morphisms and both
consecutive-composition equations together.
Exactness is imposed separately by `FourTermLinearSequence.IsExact`, so the same sequence can be
constructed before its exactness proof is available. -/
structure FourTermLinearSequence (R : Type*) [Semiring R]
    (A B C D : Type*)
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
    [Module R A] [Module R B] [Module R C] [Module R D] where
  /-- The first linear map, from \(A\) to \(B\). -/
  head : A →ₗ[R] B
  /-- The middle linear map, from \(B\) to \(C\). -/
  middle : B →ₗ[R] C
  /-- The final linear map, from \(C\) to \(D\). -/
  tail : C →ₗ[R] D
  /-- The middle map vanishes after the head map. -/
  middle_comp_head : middle.comp head = 0
  /-- The tail map vanishes after the middle map. -/
  tail_comp_middle : tail.comp middle = 0

namespace FourTermLinearSequence

variable {R A B C D : Type*} [Semiring R]
variable [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
variable [Module R A] [Module R B] [Module R C] [Module R D]

/--
A four-term exact sequence, formulated at the function level. This packages injectivity of
\(f\), exactness at the two middle terms, and surjectivity of the final map.
-/
def IsExact (S : FourTermLinearSequence R A B C D) : Prop :=
  Function.Injective S.head ∧ Function.Exact S.head S.middle ∧
    Function.Exact S.middle S.tail ∧ Function.Surjective S.tail


/-- Bundle three linear maps once their four exactness assertions are known. -/
def ofExact (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D)
    (hexact : Function.Injective f ∧ Function.Exact f g ∧
      Function.Exact g h ∧ Function.Surjective h) :
    FourTermLinearSequence R A B C D where
  head := f
  middle := g
  tail := h
  middle_comp_head := by
    ext x
    have hx : g (f x) = 0 := (hexact.2.1 (f x)).2 ⟨x, rfl⟩
    simpa using hx
  tail_comp_middle := by
    ext x
    have hx : h (g x) = 0 := (hexact.2.2.1 (g x)).2 ⟨x, rfl⟩
    simpa using hx

/-- The sequence assembled from exact maps retains the supplied injectivity,
exactness, and surjectivity witnesses. -/
@[simp]
theorem ofExact_isExact (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D)
    (hexact : Function.Injective f ∧ Function.Exact f g ∧
      Function.Exact g h ∧ Function.Surjective h) :
    (ofExact f g h hexact).IsExact :=
  hexact

end FourTermLinearSequence

section LinearEquivTransport

variable {R : Type*} [Semiring R]
variable {A B B' C D : Type*}
variable [AddCommMonoid B] [Module R B]
variable [AddCommMonoid B'] [Module R B']
variable [Zero C] [Zero D]

/-- Transport function exactness across a linear equivalence on the middle type. -/
theorem Function.Exact.linearEquiv_symm_comp_comp
    (e : B ≃ₗ[R] B') {f : A → B'} {g : B' → C}
    (hexact : Function.Exact f g) :
    Function.Exact (fun x : A => e.symm (f x)) (fun y : B => g (e y)) := by
  intro y
  constructor
  · intro hy
    rcases (hexact (e y)).1 hy with ⟨x, hx⟩
    exact ⟨x, by simp only [hx, LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨x, hx⟩
    have hxy : f x = e y := by
      have hcongr := congrArg e hx
      simpa using hcongr
    exact (hexact (e y)).2 ⟨x, hxy⟩

/--
Transporting exactness through a linear equivalence is equivalent to composing with the
equivalence and its inverse.
-/
theorem Function.Exact.linearEquiv_symm_comp_comp_iff
    (e : B ≃ₗ[R] B') {f : A → B'} {g : B' → C} :
    Function.Exact (fun x : A => e.symm (f x)) (fun y : B => g (e y)) ↔
      Function.Exact f g := by
  constructor
  · intro hexact
    simpa using
      (Function.Exact.linearEquiv_symm_comp_comp
        (e := e.symm)
        (f := fun x : A => e.symm (f x))
        (g := fun y : B => g (e y))
        hexact)
  · exact Function.Exact.linearEquiv_symm_comp_comp e

omit [Zero C] in
/--
Exactness is preserved when the tail map of an exact pair is composed with a linear equivalence
on the middle term.
-/
theorem Function.Exact.comp_linearEquiv
    (e : B ≃ₗ[R] B') {g : B' → C} {h : C → D}
    (hexact : Function.Exact g h) :
    Function.Exact (fun y : B => g (e y)) h := by
  intro z
  constructor
  · intro hz
    rcases (hexact z).1 hz with ⟨y', hy'⟩
    rcases e.surjective y' with ⟨y, rfl⟩
    exact ⟨y, hy'⟩
  · rintro ⟨y, hy⟩
    exact (hexact z).2 ⟨e y, hy⟩

end LinearEquivTransport

namespace FourTermLinearSequence

variable {R : Type*} [Semiring R]
variable {A B B' C D : Type*}
variable [AddCommMonoid A] [Module R A]
variable [AddCommMonoid B] [Module R B]
variable [AddCommMonoid B'] [Module R B']
variable [AddCommMonoid C] [Module R C]
variable [AddCommMonoid D] [Module R D]

/-- Reindex the first middle object of a bundled four-term sequence along a linear
equivalence.  Both adjacent maps are transported together, so their composition-zero
equations remain part of the resulting object. -/
def reindexMiddle (S : FourTermLinearSequence R A B' C D) (e : B ≃ₗ[R] B') :
    FourTermLinearSequence R A B C D where
  head := e.symm.toLinearMap.comp S.head
  middle := S.middle.comp e.toLinearMap
  tail := S.tail
  middle_comp_head := by
    ext x
    have hx := congrArg (fun f : A →ₗ[R] C => f x) S.middle_comp_head
    simpa using hx
  tail_comp_middle := by
    ext x
    have hx := congrArg (fun f : B' →ₗ[R] D => f (e x)) S.tail_comp_middle
    simpa using hx

/-- Exactness is preserved when the first middle object of a bundled sequence is
reindexed by a linear equivalence. -/
theorem reindexMiddle_isExact
    (S : FourTermLinearSequence R A B' C D) (e : B ≃ₗ[R] B')
    (hexact : S.IsExact) : (S.reindexMiddle e).IsExact := by
  refine ⟨?_, ?_, ?_, hexact.2.2.2⟩
  · intro x y hxy
    exact hexact.1 (e.symm.injective hxy)
  · exact Function.Exact.linearEquiv_symm_comp_comp e hexact.2.1
  · exact Function.Exact.comp_linearEquiv e hexact.2.2.1

/-- Reindexing a middle object does not change whether a bundled sequence is exact. -/
theorem reindexMiddle_isExact_iff
    (S : FourTermLinearSequence R A B' C D) (e : B ≃ₗ[R] B') :
    (S.reindexMiddle e).IsExact ↔ S.IsExact := by
  constructor
  · intro hexact
    refine ⟨?_, ?_, ?_, hexact.2.2.2⟩
    · intro x y hxy
      apply hexact.1
      change e.symm (S.head x) = e.symm (S.head y)
      exact congrArg e.symm hxy
    · intro y
      constructor
      · intro hy
        have hy' : (S.reindexMiddle e).middle (e.symm y) = 0 := by
          change S.middle (e (e.symm y)) = 0
          simpa using hy
        rcases (hexact.2.1 (e.symm y)).1 hy' with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        simpa [reindexMiddle] using congrArg (fun z : B => e z) hx
      · rintro ⟨x, rfl⟩
        have hx := congrArg (fun f : A →ₗ[R] C => f x) S.middle_comp_head
        simpa using hx
    · intro z
      constructor
      · intro hz
        rcases (hexact.2.2.1 z).1 hz with ⟨y, hy⟩
        exact ⟨e y, by simpa [reindexMiddle] using hy⟩
      · rintro ⟨y, rfl⟩
        have hy := congrArg (fun f : B' →ₗ[R] D => f y) S.tail_comp_middle
        simpa using hy
  · exact S.reindexMiddle_isExact e

end FourTermLinearSequence

end

end CrowellExactSequence
