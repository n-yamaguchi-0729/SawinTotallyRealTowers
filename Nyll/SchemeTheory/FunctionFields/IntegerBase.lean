/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Field.ULift
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The generic residue field of the integer base

The integer base of a scheme in universe `u` is represented by
`Spec (ULift.{u} ℤ)`.  This file identifies its generic residue field with
`ULift.{u} ℚ`, and hence with `ℚ`.  All auxiliary algebra structures are local
to the definitions below; importing this file does not install a new global
algebra instance.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

private theorem uliftIntegerBaseIsDomain : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

attribute [local instance] uliftIntegerBaseIsDomain

/-- The generic residue field of `Spec (ULift ℤ)` is the lifted rational
field. -/
noncomputable def specULiftZGenericResidueFieldEquivULiftQ :
    letI : IsDomain (ULift.{u} ℤ) :=
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ
    let R := CommRingCat.of (ULift.{u} ℤ)
    let X := Spec R
    let x := genericPoint X
    X.residueField x ≃+* ULift.{u} ℚ := by
  letI : Algebra (ULift.{u} ℤ) (ULift.{u} ℚ) :=
    ((algebraMap ℤ ℚ).ulift).toAlgebra
  letI : IsFractionRing (ULift.{u} ℤ) (ULift.{u} ℚ) := by
    let eQ : ℚ ≃ₐ[ℤ] ULift.{u} ℚ :=
      AlgEquiv.ofRingEquiv
        (f := (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ).symm) (by
          intro z
          simp)
    let : IsFractionRing ℤ (ULift.{u} ℚ) :=
      IsFractionRing.of_algEquiv eQ
    apply IsFractionRing.of_ringEquiv_left
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)
    intro z
    rw [RingHom.algebraMap_toAlgebra]
    rfl
  let R := CommRingCat.of (ULift.{u} ℤ)
  let X := Spec R
  let x : PrimeSpectrum (ULift.{u} ℤ) := genericPoint X
  let e : X.residueField x ≃+* x.asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso R x).commRingCatIsoToRingEquiv
  letI : Algebra (ULift.{u} ℤ) (X.residueField x) :=
    (e.symm.toRingHom.comp
      (algebraMap (ULift.{u} ℤ) x.asIdeal.ResidueField)).toAlgebra
  let eAlg : X.residueField x ≃ₐ[ULift.{u} ℤ]
      x.asIdeal.ResidueField :=
    AlgEquiv.ofRingEquiv (f := e) (by
      intro z
      rw [RingHom.algebraMap_toAlgebra]
      simp)
  have hx : x = (⊥ : PrimeSpectrum (ULift.{u} ℤ)) := by
    exact genericPoint_eq_bot_of_affine R
  letI : IsFractionRing (ULift.{u} ℤ) x.asIdeal.ResidueField := by
    rw [hx]
    change IsFractionRing (ULift.{u} ℤ)
      ((⊥ : Ideal (ULift.{u} ℤ)).ResidueField)
    infer_instance
  letI : IsFractionRing (ULift.{u} ℤ) (X.residueField x) :=
    IsFractionRing.of_algEquiv eAlg.symm
  exact IsFractionRing.ringEquivOfRingEquiv
    (K := X.residueField x) (L := ULift.{u} ℚ)
    (RingEquiv.refl (ULift.{u} ℤ))

/-- The generic residue field of `Spec (ULift ℤ)` is the rational field.

This is the form convenient for results stated over a field merely equipped
with a ring equivalence to `ℚ`. -/
noncomputable def specULiftZGenericResidueFieldEquivQ :
    letI : IsDomain (ULift.{u} ℤ) :=
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ
    let R := CommRingCat.of (ULift.{u} ℤ)
    let X := Spec R
    let x := genericPoint X
    X.residueField x ≃+* ℚ :=
  specULiftZGenericResidueFieldEquivULiftQ.trans ULift.ringEquiv

end AlgebraicGeometry
