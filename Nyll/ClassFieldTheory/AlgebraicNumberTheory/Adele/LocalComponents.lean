/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.JointComponents
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent

/-!
# Joint local components of relative adeles and ideles

The archimedean and finite tensor components jointly determine an element
of `𝔸_K ⊗[K] L`.  This file records the corresponding injective
homomorphism on relative ideles.  Surjectivity onto the restricted local
product is handled separately, once integral compatibility with the local
tensor decomposition has been established.
-/



@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The unrestricted family of every archimedean and finite local
tensor unit group. -/
abbrev RelativeLocalTensorFamily :=
  (∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ) ×
    (∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ)

/-- All local tensor components of a relative idele. -/
def relativeIdeleLocalComponents :
    RelativeIdeleGroup K L →*
      RelativeLocalTensorFamily (K := K) (L := L) where
  toFun z :=
    ⟨fun w =>
        RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w z,
      fun w =>
        RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z⟩
  map_one' := by
    apply Prod.ext
    · funext w
      exact map_one
        (RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w)
    · funext w
      exact map_one
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w)
  map_mul' x y := by
    apply Prod.ext
    · funext w
      exact map_mul
        (RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w) x y
    · funext w
      exact map_mul
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w) x y

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeIdeleLocalComponents_infinite
    (z : RelativeIdeleGroup K L)
    (w : InfinitePlace K) :
    (relativeIdeleLocalComponents
      (K := K) (L := L) z).1 w =
      RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w z :=
  rfl

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeIdeleLocalComponents_finite
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeIdeleLocalComponents
      (K := K) (L := L) z).2 w =
      RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z :=
  rfl

omit [NumberField L] in
/-- The complete local-component map is injective. -/
theorem relativeIdeleLocalComponents_injective :
    Function.Injective
      (relativeIdeleLocalComponents
        (K := K) (L := L)) := by
  intro x y hxy
  apply Units.ext
  apply relativeAdele_ext_of_components
  · intro w
    have h := congrArg (fun z => z.1 w) hxy
    exact congrArg Units.val h
  · intro w
    have h := congrArg (fun z => z.2 w) hxy
    exact congrArg Units.val h
