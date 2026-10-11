/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.NativeResidueAction
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Ring.Equiv

/-!
# Literal maximal-ideal residue identifications

The coefficient residue field is the native local-ring quotient. At a
maximal ideal, the canonical quotient-to-prime-residue map is bijective;
its actual map defines the equivalence below and preserves the original
quotient coefficient map.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The literal quotient automorphisms over the native residue field of the base. -/
def nativeResidueAutomorphismsOverResidueField
    (A : Type u) (B : Type v) [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] (p : Ideal A) (q : Ideal B)
    [q.LiesOver p] (h : p = IsLocalRing.maximalIdeal A) : GrpCat.{v} := by
  have : q.LiesOver (IsLocalRing.maximalIdeal A) :=
    h ▸ (inferInstance : q.LiesOver p)
  let : Algebra (IsLocalRing.ResidueField A) (B ⧸ q) :=
    inferInstanceAs (Algebra (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ q))
  exact GrpCat.of ((B ⧸ q) ≃ₐ[IsLocalRing.ResidueField A] (B ⧸ q))

/-- The computed quotient target is exactly the base-residue-field target
when its actual contracted prime is the closed point. -/
theorem nativeResidueAutomorphisms_eq_overResidueField
    (A : Type u) (B : Type v) [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] (p : Ideal A) (q : Ideal B)
    [q.LiesOver p] (h : p = IsLocalRing.maximalIdeal A) :
    nativeResidueAutomorphisms A B p q =
      nativeResidueAutomorphismsOverResidueField A B p q h := by
  subst p
  rfl

/-- Forget coefficient linearity only after the native closed-point
transport has installed its one residue algebra. -/
def nativeResidueAutomorphismOverResidueFieldRingEquiv
    (A : Type u) (B : Type v) [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] (p : Ideal A) (q : Ideal B)
    [q.LiesOver p] (h : p = IsLocalRing.maximalIdeal A)
    (σ : (nativeResidueAutomorphismsOverResidueField A B p q h).carrier) :
    (B ⧸ q) ≃+* (B ⧸ q) := by
  have : q.LiesOver (IsLocalRing.maximalIdeal A) :=
    h ▸ (inferInstance : q.LiesOver p)
  let : Algebra (IsLocalRing.ResidueField A) (B ⧸ q) :=
    inferInstanceAs (Algebra (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ q))
  exact (show (B ⧸ q) ≃ₐ[IsLocalRing.ResidueField A] (B ⧸ q) from σ).toRingEquiv

/-- The closed-point transport changes only the coefficient field label.
Its underlying automorphism of the literal quotient is unchanged. -/
theorem nativeResidueAutomorphisms_eq_overResidueField_ringEquiv
    (A : Type u) (B : Type v) [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] (p : Ideal A) (q : Ideal B)
    [q.LiesOver p] (h : p = IsLocalRing.maximalIdeal A)
    (σ : (nativeResidueAutomorphisms A B p q).carrier) :
    nativeResidueAutomorphismOverResidueFieldRingEquiv A B p q h
      ((CategoryTheory.eqToIso
        (nativeResidueAutomorphisms_eq_overResidueField A B p q h)).hom.hom'.toFun σ) =
      nativeResidueAutomorphismRingEquiv A B p q σ := by
  subst p
  rfl

/-- The equivalence supplied by the actual canonical maximal residue map. -/
def maximalQuotientResidueEquiv
    {B : Type v} [CommRing B] (q : Ideal B) [q.IsMaximal] :
    (B ⧸ q) ≃+* q.ResidueField :=
  RingEquiv.ofBijective (algebraMap (B ⧸ q) q.ResidueField)
    q.bijective_algebraMap_quotient_residueField

/-- The equivalence retains the original quotient-to-residue coefficient map. -/
theorem maximalQuotientResidueEquiv_comp_quotient
    {B : Type v} [CommRing B] (q : Ideal B) [q.IsMaximal] :
    (maximalQuotientResidueEquiv q).toRingHom.comp (Ideal.Quotient.mk q) =
      algebraMap B q.ResidueField := by
  apply RingHom.ext
  intro b
  exact q.algebraMap_quotient_residueField_mk b

end EtaleFundamentalGroups.Inertia
