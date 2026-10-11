/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.PurelyInseparable

/-!
# Residue maps of affine schemes

The canonical `Scheme.Spec.residueFieldIso` intertwines the scheme residue
map of `Spec.map f` with `Ideal.ResidueField.map`. This allows the purely
inseparable residue extensions constructed at tensor-product primes to be
used in the scheme-theoretic isomorphism-neighborhood construction for
Stacks Tag `0BQN`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Spec

/-- Under the canonical residue-field isomorphisms, the residue map of an
affine scheme morphism is the native map of prime-ideal residue fields. -/
@[reassoc]
theorem residueFieldIso_inv_residueFieldMap
    {R S : CommRingCat.{u}} (f : R ⟶ S) (x : Spec S) :
    letI : x.asIdeal.IsPrime := x.isPrime
    letI : (Spec.map f x).asIdeal.IsPrime := (Spec.map f x).isPrime
    (residueFieldIso R (Spec.map f x)).inv ≫
        (Spec.map f).residueFieldMap x ≫ (residueFieldIso S x).hom =
      CommRingCat.ofHom (Ideal.ResidueField.map
        (Spec.map f x).asIdeal x.asIdeal f.hom rfl) := by
  let : x.asIdeal.IsPrime := x.isPrime
  let : (Spec.map f x).asIdeal.IsPrime := (Spec.map f x).isPrime
  have heval :
      CommRingCat.ofHom (algebraMap R (Spec.map f x).asIdeal.ResidueField) ≫
          (residueFieldIso R (Spec.map f x)).inv ≫
          (Spec.map f).residueFieldMap x ≫ (residueFieldIso S x).hom =
        f ≫ CommRingCat.ofHom (algebraMap S x.asIdeal.ResidueField) := by
    rw [algebraMap_residueFieldIso_inv_assoc]
    change (Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation (Spec.map f x) ≫
        (Spec.map f).residueFieldMap x ≫ (residueFieldIso S x).hom = _
    rw [Scheme.Γevaluation_naturality_assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    change f ≫ (Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.germ ⊤ x trivial ≫
        (Spec S).residue x ≫ (residueFieldIso S x).hom = _
    rw [← algebraMap_residueFieldIso_inv_assoc, Iso.inv_hom_id, Category.comp_id]
  apply CommRingCat.hom_ext
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro r
  have h := congrArg (fun k : R ⟶ CommRingCat.of x.asIdeal.ResidueField ↦ k r) heval
  change (residueFieldIso S x).hom
      ((Spec.map f).residueFieldMap x
        ((residueFieldIso R (Spec.map f x)).inv
          (algebraMap R (Spec.map f x).asIdeal.ResidueField r))) =
    Ideal.ResidueField.map (Spec.map f x).asIdeal x.asIdeal f.hom rfl
      (algebraMap R (Spec.map f x).asIdeal.ResidueField r)
  exact h.trans
    (Ideal.ResidueField.map_algebraMap (Spec.map f x).asIdeal x.asIdeal f.hom rfl r).symm

private theorem ringEquiv_isPurelyInseparable
    {K L : Type u} [Field K] [Field L] (e : K ≃+* L) :
    e.toRingHom.IsPurelyInseparable := by
  let : Algebra K L := e.toRingHom.toAlgebra
  let eₐ : K ≃ₐ[K] L := { __ := e, commutes' k := rfl }
  exact eₐ.isPurelyInseparable

/-- Pure inseparability can be checked on the prime-ideal residue fields
of an affine map, with no additional algebra structure on scheme stalks. -/
theorem residueFieldMap_isPurelyInseparable_iff
    {R S : CommRingCat.{u}} (f : R ⟶ S) (x : Spec S) :
    letI : x.asIdeal.IsPrime := x.isPrime
    letI : (Spec.map f x).asIdeal.IsPrime := (Spec.map f x).isPrime
    ((Spec.map f).residueFieldMap x).hom.IsPurelyInseparable ↔
      (Ideal.ResidueField.map
        (Spec.map f x).asIdeal x.asIdeal f.hom rfl).IsPurelyInseparable := by
  let : x.asIdeal.IsPrime := x.isPrime
  let : (Spec.map f x).asIdeal.IsPrime := (Spec.map f x).isPrime
  let eR := residueFieldIso R (Spec.map f x)
  let eS := residueFieldIso S x
  have hR : eR.hom.hom.IsPurelyInseparable :=
    ringEquiv_isPurelyInseparable eR.commRingCatIsoToRingEquiv
  have hRinv : eR.inv.hom.IsPurelyInseparable :=
    ringEquiv_isPurelyInseparable eR.symm.commRingCatIsoToRingEquiv
  have hS : eS.hom.hom.IsPurelyInseparable :=
    ringEquiv_isPurelyInseparable eS.commRingCatIsoToRingEquiv
  have hSinv : eS.inv.hom.IsPurelyInseparable :=
    ringEquiv_isPurelyInseparable eS.symm.commRingCatIsoToRingEquiv
  constructor
  · intro h
    have hcomp := hRinv.comp (h.comp hS)
    change (eR.inv ≫ (Spec.map f).residueFieldMap x ≫ eS.hom).hom.IsPurelyInseparable
      at hcomp
    rw [residueFieldIso_inv_residueFieldMap] at hcomp
    exact hcomp
  · intro h
    have hcomp := hR.comp (h.comp hSinv)
    change (eR.hom ≫ CommRingCat.ofHom (Ideal.ResidueField.map
        (Spec.map f x).asIdeal x.asIdeal f.hom rfl) ≫ eS.inv).hom.IsPurelyInseparable
      at hcomp
    rw [← residueFieldIso_inv_residueFieldMap] at hcomp
    change (eR.hom ≫ (eR.inv ≫ (Spec.map f).residueFieldMap x ≫ eS.hom) ≫
      eS.inv).hom.IsPurelyInseparable at hcomp
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] at hcomp
    exact hcomp

end AlgebraicGeometry.Scheme.Spec
