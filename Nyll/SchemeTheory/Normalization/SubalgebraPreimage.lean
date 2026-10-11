/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Native normalization preimages of subalgebras

The normalization objects and their preimage are constructed from the native
carriers and inherited actions. Their ring maps and coefficient equations
are established before any fraction-field, Galois, or inertia data appear.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- A subalgebra with its native ring and coefficient action. -/
def subalgebraCommAlgCat {A : Type u} {R : Type v}
    [CommRing A] [CommRing R] [Algebra A R]
    (S : Subalgebra A R) : CommAlgCat.{v} A :=
  CommAlgCat.of A S

/-- The native coefficient map, retained as a RingHom. -/
def subalgebraBaseMap {A : Type u} {R : Type v}
    [CommRing A] [CommRing R] [Algebra A R]
    (S : Subalgebra A R) : A →+* subalgebraCommAlgCat S :=
  algebraMap A S

/-- The base map uses exactly the action in the returned native object. -/
theorem subalgebraBaseMap_eq_algebraMap {A : Type u} {R : Type v}
    [CommRing A] [CommRing R] [Algebra A R]
    (S : Subalgebra A R) :
    subalgebraBaseMap S = algebraMap A (subalgebraCommAlgCat S) := rfl

/-- The literal subtype inclusion, without opening an algebra on its source. -/
def subalgebraRingMap {A : Type u} {R : Type v}
    [CommRing A] [CommRing R] [Algebra A R]
    (S : Subalgebra A R) : subalgebraCommAlgCat S →+* R :=
  SubsemiringClass.subtype S

/-- The native subtype inclusion is injective. -/
theorem subalgebraRingMap_injective {A : Type u} {R : Type v}
    [CommRing A] [CommRing R] [Algebra A R]
    (S : Subalgebra A R) : Function.Injective (subalgebraRingMap S).toFun :=
  Subtype.val_injective

/-- The subtype inclusion preserves the original coefficients. -/
theorem subalgebraRingMap_comp_base {A : Type u} {R : Type v}
    [CommRing A] [CommRing R] [Algebra A R]
    (S : Subalgebra A R) :
    (subalgebraRingMap S).comp (subalgebraBaseMap S) = algebraMap A R :=
  S.val.comp_algebraMap

section Preimage

variable {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C] [Algebra A R] [Algebra A C]

/-- The actual preimage subalgebra, with its native coefficient action. -/
def subalgebraPreimageCommAlgCat (f : R →ₐ[A] C) (T : Subalgebra A C) :
    CommAlgCat.{v} A :=
  subalgebraCommAlgCat (T.comap f)

/-- The actual restriction of the given map to its preimage. -/
def subalgebraPreimageRingMap (f : R →ₐ[A] C) (T : Subalgebra A C) :
    subalgebraPreimageCommAlgCat f T →+* subalgebraCommAlgCat T :=
  f.toRingHom.restrict (T.comap f) T (fun _ hx => hx)

/-- The original coefficients in the actual preimage algebra. -/
def subalgebraPreimageBaseMap (f : R →ₐ[A] C) (T : Subalgebra A C) :
    A →+* subalgebraPreimageCommAlgCat f T :=
  subalgebraBaseMap (T.comap f)

/-- The coefficient map is the native algebraMap of the constructed object. -/
theorem subalgebraPreimageBaseMap_eq_algebraMap
    (f : R →ₐ[A] C) (T : Subalgebra A C) :
    subalgebraPreimageBaseMap f T =
      algebraMap A (subalgebraPreimageCommAlgCat f T) :=
  subalgebraBaseMap_eq_algebraMap (T.comap f)

/-- The restriction square is supplied by the native RingHom restriction. -/
theorem subalgebraPreimageRingMap_comp_coefficient
    (f : R →ₐ[A] C) (T : Subalgebra A C) :
    (subalgebraRingMap T).comp (subalgebraPreimageRingMap f T) =
      f.toRingHom.comp (subalgebraRingMap (T.comap f)) :=
  RingHom.comp_restrict f.toRingHom (T.comap f) T (fun _ hx => hx)

/-- The preimage ring map preserves the original base map. All equations
used here are supplied by the native maps; no compatibility is assumed. -/
theorem subalgebraPreimageRingMap_comp_base
    (f : R →ₐ[A] C) (T : Subalgebra A C) :
    (subalgebraPreimageRingMap f T).comp (subalgebraPreimageBaseMap f T) =
      subalgebraBaseMap T := by
  apply (RingHom.cancel_left (g := subalgebraRingMap T)
    (subalgebraRingMap_injective T)).mp
  calc
    (subalgebraRingMap T).comp
        ((subalgebraPreimageRingMap f T).comp (subalgebraPreimageBaseMap f T)) =
        ((subalgebraRingMap T).comp (subalgebraPreimageRingMap f T)).comp
          (subalgebraPreimageBaseMap f T) :=
      (RingHom.comp_assoc (subalgebraPreimageBaseMap f T)
        (subalgebraPreimageRingMap f T) (subalgebraRingMap T)).symm
    _ = (f.toRingHom.comp (subalgebraRingMap (T.comap f))).comp
          (subalgebraPreimageBaseMap f T) :=
      congrArg (fun h : subalgebraPreimageCommAlgCat f T →+* C =>
        h.comp (subalgebraPreimageBaseMap f T))
        (subalgebraPreimageRingMap_comp_coefficient f T)
    _ = f.toRingHom.comp
          ((subalgebraRingMap (T.comap f)).comp (subalgebraPreimageBaseMap f T)) :=
      RingHom.comp_assoc (subalgebraPreimageBaseMap f T)
        (subalgebraRingMap (T.comap f)) f.toRingHom
    _ = f.toRingHom.comp (algebraMap A R) :=
      congrArg (fun h : A →+* R => f.toRingHom.comp h)
        (subalgebraRingMap_comp_base (T.comap f))
    _ = algebraMap A C := f.comp_algebraMap
    _ = (subalgebraRingMap T).comp (subalgebraBaseMap T) :=
      (subalgebraRingMap_comp_base T).symm

end Preimage

/-- The actual normalization in the ambient algebra. -/
def normalizationCommAlgCat (A : Type u) (L : Type v)
    [CommRing A] [CommRing L] [Algebra A L] : CommAlgCat.{v} A :=
  CommAlgCat.of A (integralClosure A L)

variable {A : Type u} {L : Type v}
    [CommRing A] [CommRing L] [Algebra A L]

/-- Construct the actual normalization inside the given subalgebra before
exposing it as an object to later preimage constructions. -/
def subalgebraNormalizationCommAlgCat (S : Subalgebra A L) : CommAlgCat.{v} A :=
  CommAlgCat.of A (integralClosure A S)

/-- The native normalization map induced by the literal subtype inclusion. -/
def subalgebraNormalizationMap (S : Subalgebra A L) :
    subalgebraNormalizationCommAlgCat S →ₐ[A] normalizationCommAlgCat A L :=
  S.val.mapIntegralClosure

/-- The same actual normalization inclusion, retained as a RingHom. -/
def subalgebraNormalizationRingMap (S : Subalgebra A L) :
    subalgebraNormalizationCommAlgCat S →+* normalizationCommAlgCat A L :=
  (subalgebraNormalizationMap S).toRingHom

/-- The normalization inclusion preserves the native coefficient maps. -/
theorem subalgebraNormalizationRingMap_comp_base (S : Subalgebra A L) :
    (subalgebraNormalizationRingMap S).comp
        (algebraMap A (subalgebraNormalizationCommAlgCat S)) =
      algebraMap A (normalizationCommAlgCat A L) :=
  (subalgebraNormalizationMap S).comp_algebraMap

/-- The actual preimage in the native subalgebra normalization. -/
def normalizationPreimageCommAlgCat (S : Subalgebra A L)
    (T : Subalgebra A (normalizationCommAlgCat A L)) : CommAlgCat.{v} A :=
  subalgebraPreimageCommAlgCat (subalgebraNormalizationMap S) T

/-- The literal inclusion of the normalization preimage into the given
upper subalgebra, exposed without opening the preimage coefficient action. -/
def normalizationPreimageRingMap (S : Subalgebra A L)
    (T : Subalgebra A (normalizationCommAlgCat A L)) :
    normalizationPreimageCommAlgCat S T →+* subalgebraCommAlgCat T :=
  subalgebraPreimageRingMap (subalgebraNormalizationMap S) T

/-- The original coefficient map in the actual normalization preimage. -/
def normalizationPreimageBaseMap (S : Subalgebra A L)
    (T : Subalgebra A (normalizationCommAlgCat A L)) :
    A →+* normalizationPreimageCommAlgCat S T :=
  subalgebraPreimageBaseMap (subalgebraNormalizationMap S) T

/-- The actual preimage RingHom satisfies its original coefficient square. -/
theorem normalizationPreimageRingMap_comp_base (S : Subalgebra A L)
    (T : Subalgebra A (normalizationCommAlgCat A L)) :
    (normalizationPreimageRingMap S T).comp (normalizationPreimageBaseMap S T) =
      subalgebraBaseMap T :=
  subalgebraPreimageRingMap_comp_base (subalgebraNormalizationMap S) T

/-- The preimage base map is the native algebraMap on the actual object. -/
theorem normalizationPreimageBaseMap_eq_algebraMap (S : Subalgebra A L)
    (T : Subalgebra A (normalizationCommAlgCat A L)) :
    normalizationPreimageBaseMap S T =
      algebraMap A (normalizationPreimageCommAlgCat S T) :=
  subalgebraPreimageBaseMap_eq_algebraMap (subalgebraNormalizationMap S) T

/-- The native subalgebra object retains the canonical domain property
of its ambient ring. Only the existing Prop instance is exposed. -/
theorem subalgebraCommAlgCat_isDomain {A : Type u} {R : Type v}
    [CommRing A] [CommRing R] [IsDomain R] [Algebra A R]
    (S : Subalgebra A R) : IsDomain (subalgebraCommAlgCat S) := by
  change IsDomain S
  infer_instance

/-- The actual preimage restriction retains injectivity of the given
coefficient map. The proof uses its already proved restriction square. -/
theorem subalgebraPreimageRingMap_injective
    {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C] [Algebra A R] [Algebra A C]
    (f : R →ₐ[A] C) (T : Subalgebra A C)
    (hf : Function.Injective f.toRingHom.toFun) :
    Function.Injective (subalgebraPreimageRingMap f T).toFun := by
  intro x y h
  apply subalgebraRingMap_injective (T.comap f)
  apply hf
  have hc := congrArg (subalgebraRingMap T).toFun h
  change ((subalgebraRingMap T).comp (subalgebraPreimageRingMap f T)).toFun x =
    ((subalgebraRingMap T).comp (subalgebraPreimageRingMap f T)).toFun y at hc
  rw [subalgebraPreimageRingMap_comp_coefficient f T] at hc
  exact hc

/-- The literal normalization inclusion is injective by its two subtype
projections. No field, fraction-ring, or Galois hypothesis is needed. -/
theorem subalgebraNormalizationRingMap_injective (S : Subalgebra A L) :
    Function.Injective (subalgebraNormalizationRingMap S).toFun := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (subalgebraRingMap (integralClosure A L)).toFun h

/-- The actual normalization preimage embeds into the given upper
subalgebra, using the native normalization injection just proved. -/
theorem normalizationPreimageRingMap_injective (S : Subalgebra A L)
    (T : Subalgebra A (normalizationCommAlgCat A L)) :
    Function.Injective (normalizationPreimageRingMap S T).toFun :=
  subalgebraPreimageRingMap_injective (subalgebraNormalizationMap S) T
    (subalgebraNormalizationRingMap_injective S)

end SchemeTheory
