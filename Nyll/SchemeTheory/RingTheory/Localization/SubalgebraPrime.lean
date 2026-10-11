/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Native subalgebra-prime localization maps with closed coefficient squares

The ring objects are the actual native prime localizations. Their coefficient
maps are the native algebra maps, retained as RingHoms. The localization map
is `Localization.localRingHom`; its native coefficient equation is proved in
the ring-only scope before specializing to a subalgebra.

The subalgebra base maps are the literal composites of these coefficient
maps with the original algebra maps. Their proved square mentions only the
computed RingHoms. No comparison, localization compatibility, alternate
algebra dictionary, or independent local model is assumed.
-/

noncomputable section

namespace SchemeTheory

universe u v

/-- The actual native prime localization, bundled with its native ring. -/
def primeLocalizationCommRingCat (C : Type v) [CommRing C]
    (Q : Ideal C) [Q.IsPrime] : CommRingCat.{v} :=
  CommRingCat.of (Localization.AtPrime Q)

/-- The actual native localization at the contracted prime. The comap-prime
proof is constructed here, rather than requested from a caller. -/
def primeLocalizationComapCommRingCat
    {R : Type u} {C : Type v} [CommRing R] [CommRing C]
    (f : R →+* C) (Q : Ideal C) [Q.IsPrime] : CommRingCat.{u} := by
  have : (Q.comap f).IsPrime := Ideal.IsPrime.comap f
  exact primeLocalizationCommRingCat R (Q.comap f)

/-- The native coefficient map into the actual prime localization. -/
def primeLocalizationCoefficientMap (C : Type v) [CommRing C]
    (Q : Ideal C) [Q.IsPrime] : C →+* primeLocalizationCommRingCat C Q :=
  algebraMap C (Localization.AtPrime Q)

/-- The native coefficient map into the actual contracted-prime localization. -/
def primeLocalizationComapCoefficientMap
    {R : Type u} {C : Type v} [CommRing R] [CommRing C]
    (f : R →+* C) (Q : Ideal C) [Q.IsPrime] :
    R →+* primeLocalizationComapCommRingCat f Q := by
  have : (Q.comap f).IsPrime := Ideal.IsPrime.comap f
  exact algebraMap R (Localization.AtPrime (Q.comap f))

/-- The actual map between the native prime localizations. -/
def primeLocalizationComapMap
    {R : Type u} {C : Type v} [CommRing R] [CommRing C]
    (f : R →+* C) (Q : Ideal C) [Q.IsPrime] :
    primeLocalizationComapCommRingCat f Q →+* primeLocalizationCommRingCat C Q := by
  have : (Q.comap f).IsPrime := Ideal.IsPrime.comap f
  exact Localization.localRingHom (Q.comap f) Q f rfl

/-- The native localization coefficient equation, with both coefficient
maps retained as the actual constructed RingHoms in its public statement. -/
theorem primeLocalizationComapMap_comp_coefficient
    {R : Type u} {C : Type v} [CommRing R] [CommRing C]
    (f : R →+* C) (Q : Ideal C) [Q.IsPrime] :
    (primeLocalizationComapMap f Q).comp (primeLocalizationComapCoefficientMap f Q) =
      (primeLocalizationCoefficientMap C Q).comp f := by
  have : (Q.comap f).IsPrime := Ideal.IsPrime.comap f
  apply RingHom.ext
  intro r
  exact Localization.localRingHom_to_map (Q.comap f) Q f rfl r

/-- The original base-ring map into the actual ambient prime localization. -/
def primeLocalizationBaseMap (A : Type u) (C : Type v)
    [CommRing A] [CommRing C] [Algebra A C]
    (Q : Ideal C) [Q.IsPrime] : A →+* primeLocalizationCommRingCat C Q :=
  (primeLocalizationCoefficientMap C Q).comp (algebraMap A C)

variable {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]

/-- The source is exactly the native localization of the actual subalgebra
at the contraction of the original prime. -/
def subalgebraPrimeLocalizationSource (S : Subalgebra A C)
    (Q : Ideal C) [Q.IsPrime] : CommRingCat.{v} :=
  primeLocalizationComapCommRingCat S.val.toRingHom Q

/-- The literal localized inclusion of the actual subalgebra. -/
def subalgebraPrimeLocalizationMap (S : Subalgebra A C)
    (Q : Ideal C) [Q.IsPrime] :
    subalgebraPrimeLocalizationSource S Q →+* primeLocalizationCommRingCat C Q :=
  primeLocalizationComapMap S.val.toRingHom Q

/-- The original base-ring map into the actual subalgebra localization. -/
def subalgebraPrimeLocalizationBaseMap (S : Subalgebra A C)
    (Q : Ideal C) [Q.IsPrime] : A →+* subalgebraPrimeLocalizationSource S Q :=
  (primeLocalizationComapCoefficientMap S.val.toRingHom Q).comp (algebraMap A S)

/-- The literal subalgebra localization map preserves the original base
map. Its public equation contains only the computed native RingHoms. -/
theorem subalgebraPrimeLocalizationMap_comp_base
    (S : Subalgebra A C) (Q : Ideal C) [Q.IsPrime] :
    (subalgebraPrimeLocalizationMap S Q).comp (subalgebraPrimeLocalizationBaseMap S Q) =
      primeLocalizationBaseMap A C Q := by
  let b : S →+* subalgebraPrimeLocalizationSource S Q :=
    primeLocalizationComapCoefficientMap S.val.toRingHom Q
  let c : C →+* primeLocalizationCommRingCat C Q :=
    primeLocalizationCoefficientMap C Q
  have hlocal : (subalgebraPrimeLocalizationMap S Q).comp b = c.comp S.val.toRingHom :=
    primeLocalizationComapMap_comp_coefficient S.val.toRingHom Q
  have hbase : S.val.toRingHom.comp (algebraMap A S) = algebraMap A C :=
    S.val.comp_algebraMap
  calc
    (subalgebraPrimeLocalizationMap S Q).comp (subalgebraPrimeLocalizationBaseMap S Q) =
        (subalgebraPrimeLocalizationMap S Q).comp (b.comp (algebraMap A S)) := rfl
    _ = ((subalgebraPrimeLocalizationMap S Q).comp b).comp (algebraMap A S) :=
      (RingHom.comp_assoc (algebraMap A S) b (subalgebraPrimeLocalizationMap S Q)).symm
    _ = (c.comp S.val.toRingHom).comp (algebraMap A S) :=
      congrArg (fun h : S →+* primeLocalizationCommRingCat C Q =>
        h.comp (algebraMap A S)) hlocal
    _ = c.comp (S.val.toRingHom.comp (algebraMap A S)) :=
      RingHom.comp_assoc (algebraMap A S) S.val.toRingHom c
    _ = c.comp (algebraMap A C) :=
      congrArg (fun h : A →+* C => c.comp h) hbase
    _ = primeLocalizationBaseMap A C Q := rfl

/-- The same actual source localization with its native coefficient algebra.
No alternate algebra action is installed. -/
def subalgebraPrimeLocalizationAlgebra (S : Subalgebra A C)
    (Q : Ideal C) [Q.IsPrime] : CommAlgCat.{v} A := by
  have : (Q.comap S.val.toRingHom).IsPrime := Ideal.IsPrime.comap S.val.toRingHom
  exact CommAlgCat.of A (Localization.AtPrime (Q.comap S.val.toRingHom))

/-- The computed coefficient composite is the native base-algebra map on
that exact localization, by the existing native scalar tower. -/
theorem subalgebraPrimeLocalizationBaseMap_eq_algebraMap
    (S : Subalgebra A C) (Q : Ideal C) [Q.IsPrime] :
    (subalgebraPrimeLocalizationBaseMap S Q :
        A →+* subalgebraPrimeLocalizationAlgebra S Q) =
      algebraMap A (subalgebraPrimeLocalizationAlgebra S Q) := by
  have : (Q.comap S.val.toRingHom).IsPrime := Ideal.IsPrime.comap S.val.toRingHom
  exact (IsScalarTower.algebraMap_eq A S
    (Localization.AtPrime (Q.comap S.val.toRingHom))).symm

end SchemeTheory
