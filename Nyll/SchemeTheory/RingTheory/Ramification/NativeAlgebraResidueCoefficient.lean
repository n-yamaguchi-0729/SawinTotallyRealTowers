/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueEpi
import Nyll.SchemeTheory.RingTheory.Ramification.NativeResidueAction
import Nyll.SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import Nyll.SchemeTheory.CategoryTheory.CommAlgRingMap
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Coefficient descriptions of algebra residue automorphisms

Defines ring equivalences and coefficient maps underlying algebra residue automorphisms. It
proves that these coefficient maps determine the automorphisms and computes the residue morphism
on coefficients.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

/-- Forget only coefficient-linearity in the actual native residue group. -/
def nativeAlgebraResidueAutomorphismRingEquiv
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A) (Q : Ideal R)
    (σ : nativeAlgebraResidueAutomorphisms R Q) : (R ⧸ Q) ≃+* (R ⧸ Q) :=
  nativeResidueAutomorphismRingEquiv A R (Q.under A) Q σ

/-- The actual residue automorphism evaluated on original coefficients. -/
def nativeAlgebraResidueCoefficientMap
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A) (Q : Ideal R)
    (σ : nativeAlgebraResidueAutomorphisms R Q) : R →+* (R ⧸ Q) :=
  (nativeAlgebraResidueAutomorphismRingEquiv R Q σ).toRingHom.comp (Ideal.Quotient.mk Q)

/-- Original coefficients determine the native residue automorphism. -/
theorem nativeAlgebraResidueCoefficientMap_injective
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A) (Q : Ideal R) :
    Function.Injective (nativeAlgebraResidueCoefficientMap R Q) := by
  intro σ τ h
  apply nativeResidueAutomorphismRingEquiv_injective A R (Q.under A) Q
  apply RingEquiv.ext
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (fun f : R →+* (R ⧸ Q) => f.toFun b) h

/-- The same native residue morphism has its original coefficient formula. -/
theorem nativeAlgebraResidueMorphism_coefficientMap
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (G : Type v) [Group G] [MulSemiringAction G R]
    (Q : Ideal R)
    (hbase : ∀ g : G, (MulSemiringAction.toRingHom G R g).comp
      (commAlgCoefficientMap R) = commAlgCoefficientMap R)
    (d : nativeResidueStabilizer R G Q) :
    nativeAlgebraResidueCoefficientMap R Q
        ((nativeAlgebraResidueMorphism R G Q hbase).hom'.toFun d) =
      (Ideal.Quotient.mk Q).comp (stabilizerCoefficientRingEquiv R G Q d).toRingHom := rfl

end EtaleFundamentalGroups.Inertia

end
