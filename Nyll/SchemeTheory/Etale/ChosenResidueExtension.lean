/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.ResidueFieldExtension
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.TensorProduct.Maps


/-!
# An étale base extension adapted to one quasi-finite point

Realize the separable closure of the base residue field inside the selected
residue field in an étale neighborhood. Evaluation into the selected residue
field defines a prime of the tensor product. The induced residue map is an
isomorphism, while the extension from the new base residue field is purely
inseparable.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.Etale

private theorem ringEquiv_isPurelyInseparable
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    e.toRingHom.IsPurelyInseparable := by
  let : Algebra K L := e.toRingHom.toAlgebra
  let eₐ : K ≃ₐ[K] L := { __ := e, commutes' _ := rfl }
  exact eₐ.isPurelyInseparable

/-- After an actual étale base extension, a chosen point of a quasi-finite algebra
has the same residue field as before and is purely inseparable over the new
base residue field. The tensor-product prime is constructed as an evaluation
kernel, and the residue-field isomorphism is compatible with the old point. -/
theorem exists_chosen_residue_extension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p)
      (Q : Ideal (R' ⊗[R] S)) (_ : Q.IsPrime) (_ : Q.LiesOver P)
      (hq : q = Q.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom)
      (e : Q.ResidueField ≃+* q.ResidueField),
      e.toRingHom.comp (Ideal.ResidueField.map q Q
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom hq) =
          RingHom.id q.ResidueField ∧
      (Ideal.ResidueField.map P Q (algebraMap R' (R' ⊗[R] S))
        (Q.over_def P)).IsPurelyInseparable := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let L := separableClosure p.ResidueField q.ResidueField
  obtain ⟨R', hring, halgebra, hetale, P, hP, hPp, eP, heP⟩ :=
    exists_residueField_extension p L
  let : CommRing R' := hring
  let : Algebra R R' := halgebra
  let : Algebra.Etale R R' := hetale
  let : P.IsPrime := hP
  let : P.LiesOver p := hPp
  let φ : R' →ₐ[R] q.ResidueField := {
    __ := (algebraMap L q.ResidueField).comp
      (eP.toRingHom.comp (algebraMap R' P.ResidueField))
    commutes' r := by
      have h := RingHom.congr_fun heP (algebraMap R p.ResidueField r)
      change eP (Ideal.ResidueField.map p P (algebraMap R R') (P.over_def p)
        (algebraMap R p.ResidueField r)) =
          algebraMap p.ResidueField L (algebraMap R p.ResidueField r) at h
      rw [Ideal.ResidueField.map_algebraMap] at h
      change algebraMap L q.ResidueField
        (eP (algebraMap R' P.ResidueField (algebraMap R R' r))) =
          algebraMap R q.ResidueField r
      rw [h, ← IsScalarTower.algebraMap_apply p.ResidueField L q.ResidueField,
        ← IsScalarTower.algebraMap_apply R p.ResidueField q.ResidueField]
  }
  have hφker : RingHom.ker φ.toRingHom = P := by
    apply Ideal.ext
    intro r
    change algebraMap L q.ResidueField (eP (algebraMap R' P.ResidueField r)) = 0 ↔ r ∈ P
    rw [← map_zero (algebraMap L q.ResidueField),
      (algebraMap L q.ResidueField).injective.eq_iff,
      ← map_zero eP, eP.injective.eq_iff, Ideal.algebraMap_residueField_eq_zero]
  let Φ : R' ⊗[R] S →ₐ[R] q.ResidueField :=
    Algebra.TensorProduct.lift φ (IsScalarTower.toAlgHom R S q.ResidueField)
      (fun _ _ ↦ Commute.all _ _)
  have hΦleft : Φ.comp (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] S) = φ :=
    Algebra.TensorProduct.lift_comp_includeLeft _ _ _
  have hΦright : Φ.comp (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S) =
      IsScalarTower.toAlgHom R S q.ResidueField :=
    Algebra.TensorProduct.lift_comp_includeRight' _ _ _
  let Q : Ideal (R' ⊗[R] S) := RingHom.ker Φ.toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime _
  have hQP : Q.comap (algebraMap R' (R' ⊗[R] S)) = P := by
    dsimp only [Q]
    rw [RingHom.comap_ker]
    change RingHom.ker
      ((Φ.comp (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] S)).toRingHom) = P
    rw [hΦleft, hφker]
  let : Q.LiesOver P := ⟨hQP.symm⟩
  have hQq : Q.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom = q := by
    dsimp only [Q]
    rw [RingHom.comap_ker]
    change RingHom.ker
      ((Φ.comp (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S)).toRingHom) = q
    rw [hΦright]
    change RingHom.ker (algebraMap S q.ResidueField) = q
    exact q.ker_algebraMap_residueField
  have hunit : Q.primeCompl ≤ (IsUnit.submonoid q.ResidueField).comap Φ.toRingHom := by
    intro x hx
    change IsUnit (Φ x)
    exact isUnit_iff_ne_zero.mpr hx
  let Ψ : Q.ResidueField →+* q.ResidueField :=
    Ideal.ResidueField.lift Q Φ.toRingHom le_rfl hunit
  let ιq : q.ResidueField →+* Q.ResidueField :=
    Ideal.ResidueField.map q Q
      (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom hQq.symm
  have hΨιq : Ψ.comp ιq = RingHom.id q.ResidueField := by
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro s
    change Ψ (ιq (algebraMap S q.ResidueField s)) = algebraMap S q.ResidueField s
    rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.lift_algebraMap]
    exact AlgHom.congr_fun hΦright s
  have hΨsurj : Function.Surjective Ψ := by
    intro x
    exact ⟨ιq x, RingHom.congr_fun hΨιq x⟩
  let e : Q.ResidueField ≃+* q.ResidueField :=
    RingEquiv.ofBijective Ψ ⟨Ψ.injective, hΨsurj⟩
  let ιP : P.ResidueField →+* Q.ResidueField :=
    Ideal.ResidueField.map P Q (algebraMap R' (R' ⊗[R] S)) (Q.over_def P)
  let δ : P.ResidueField →+* q.ResidueField :=
    (algebraMap L q.ResidueField).comp eP.toRingHom
  have hΨιP : Ψ.comp ιP = δ := by
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro r
    change Ψ (ιP (algebraMap R' P.ResidueField r)) =
      algebraMap L q.ResidueField (eP (algebraMap R' P.ResidueField r))
    rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.lift_algebraMap]
    exact AlgHom.congr_fun hΦleft r
  have hδ : δ.IsPurelyInseparable :=
    (ringEquiv_isPurelyInseparable eP).comp
      (RingHom.isPurelyInseparable_algebraMap_iff.mpr
        (inferInstance : IsPurelyInseparable L q.ResidueField))
  have hpure : (e.symm.toRingHom.comp δ).IsPurelyInseparable :=
    hδ.comp (ringEquiv_isPurelyInseparable e.symm)
  have heq : e.symm.toRingHom.comp δ = ιP := by
    apply RingHom.ext
    intro x
    change e.symm (δ x) = ιP x
    rw [← RingHom.congr_fun hΨιP x]
    exact e.symm_apply_apply (ιP x)
  have hpure' : ιP.IsPurelyInseparable := by
    rw [← heq]
    exact hpure
  exact ⟨R', hring, halgebra, hetale, P, hP, hPp,
    Q, inferInstance, inferInstance, hQq.symm, e, hΨιq, by
      change ιP.IsPurelyInseparable
      exact hpure'⟩

end Algebra.Etale
