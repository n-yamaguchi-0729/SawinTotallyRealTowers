/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.AffineResidueField
public import Nyll.SchemeTheory.Etale.FiniteNeighborhoodSection
public import Nyll.SchemeTheory.Etale.ResidueBaseChange
public import Mathlib.RingTheory.SurjectiveOnStalks

/-!
# The residue extension of an actual finite local factor

The finite factor is constructed by the quasi-finite local structure theorem.
Its selected tensor prime inherits pure inseparability under base change, and
localization induces an isomorphism on the selected residue field.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

private theorem purelyInseparable_of_bijective
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (hf : Function.Bijective f) : f.IsPurelyInseparable := by
  let : Algebra K L := f.toAlgebra
  let e : K ≃ₐ[K] L := {
    __ := RingEquiv.ofBijective f hf
    commutes' _ := rfl
  }
  exact e.isPurelyInseparable

/-- A selected purely inseparable residue extension stays purely inseparable
in the actual finite open factor supplied by the quasi-finite local structure
theorem. The conclusion records the actual finite map and its singleton fiber. -/
theorem exists_purelyInseparable_etale_finite_factor
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (p : Ideal R) [p.IsPrime]
    (q : Ideal A) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q]
    (hκ : (Ideal.ResidueField.map p q (algebraMap R A)
      (q.over_def p)).IsPurelyInseparable) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p)
      (e : R' ⊗[R] A) (_ : IsIdempotentElem e),
      Module.Finite R' (Localization.Away e) ∧
      IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away e)))) ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (algebraMap (R' ⊗[R] A) (Localization.Away e)))) ∧
      ∃ z : Spec (CommRingCat.of (Localization.Away e)),
        Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away e))) z =
          ⟨P, inferInstance⟩ ∧
        (Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[R] A) (Localization.Away e))) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom)) z =
          (⟨q, inferInstance⟩ : Spec (CommRingCat.of A)) ∧
        (∀ z' : Spec (CommRingCat.of (Localization.Away e)),
          Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away e))) z' =
            ⟨P, inferInstance⟩ → z' = z) ∧
        ((Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away e)))).residueFieldMap
          z).hom.IsPurelyInseparable := by
  obtain ⟨R', hR', hRR', hEtale, P, hP, hPp, e, he, _, hfinite, hfiniteSpec,
      hopen, z, hzP, hzq, huniq⟩ :=
    exists_etale_finite_factor_of_quasiFiniteAt p q
  let : CommRing R' := hR'
  let : Algebra R R' := hRR'
  let : Algebra.Etale R R' := hEtale
  let : P.IsPrime := hP
  let : P.LiesOver p := hPp
  let : z.asIdeal.IsPrime := z.isPrime
  let Q : Ideal (R' ⊗[R] A) :=
    z.asIdeal.comap (algebraMap (R' ⊗[R] A) (Localization.Away e))
  let : Q.IsPrime := Ideal.comap_isPrime _ _
  have hPz : P = z.asIdeal.comap (algebraMap R' (Localization.Away e)) :=
    (congrArg PrimeSpectrum.asIdeal hzP).symm
  let : Q.LiesOver P := ⟨by
    change P = Ideal.comap (algebraMap R' (R' ⊗[R] A))
      (Ideal.comap (algebraMap (R' ⊗[R] A) (Localization.Away e)) z.asIdeal)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact hPz⟩
  have hqQ : q = Q.comap
      (Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom :=
    (congrArg PrimeSpectrum.asIdeal hzq).symm
  have hκQ := Algebra.isPurelyInseparable_residueFieldMap_tensorProduct
    p q P Q hqQ hκ
  let a : P.ResidueField →+* Q.ResidueField :=
    Ideal.ResidueField.map P Q (algebraMap R' (R' ⊗[R] A)) (Q.over_def P)
  let b : Q.ResidueField →+* z.asIdeal.ResidueField :=
    Ideal.ResidueField.map Q z.asIdeal
      (algebraMap (R' ⊗[R] A) (Localization.Away e)) rfl
  have hb : b.IsPurelyInseparable := purelyInseparable_of_bijective b
    ((RingHom.surjectiveOnStalks_of_isLocalization (Submonoid.powers e)
      (Localization.Away e)).residueFieldMap_bijective Q z.asIdeal rfl)
  have hba : b.comp a = Ideal.ResidueField.map P z.asIdeal
      (algebraMap R' (Localization.Away e)) hPz := by
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro r
    simp only [a, b, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    rw [← IsScalarTower.algebraMap_apply R' (R' ⊗[R] A) (Localization.Away e)]
  have hκz : (Ideal.ResidueField.map P z.asIdeal
      (algebraMap R' (Localization.Away e)) hPz).IsPurelyInseparable := by
    rw [← hba]
    exact hκQ.comp hb
  refine ⟨R', hR', hRR', hEtale, P, hP, hPp, e, he, hfinite,
    hfiniteSpec, hopen, z, hzP, hzq, huniq, ?_⟩
  apply (Scheme.Spec.residueFieldMap_isPurelyInseparable_iff
    (CommRingCat.ofHom (algebraMap R' (Localization.Away e))) z).mpr
  cases hPz
  exact hκz

end AlgebraicGeometry
