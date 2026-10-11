/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Basic

/-!
# Transport of prime divisors across function-field equivalences

A `K`-algebra equivalence of function fields transports valuation subrings,
discrete `K`-valuations, residue fields, and hence Fried--Jarden prime
divisors.  This is the model-independent bridge needed to replace a plane
equation by an isomorphic monic representative.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06

open IsLocalRing

universe uK uF uG

variable {K : Type uK} {F : Type uF} {G : Type uG}
  [Field K] [Field F] [Field G]
  [Algebra K F] [Algebra K G]

namespace ValuationSubring

/-- The image of a valuation subring under a field isomorphism. -/
def mapEquiv (e : F ≃+* G) (V : ValuationSubring F) :
    ValuationSubring G where
  toSubring := V.toSubring.map e.toRingHom
  mem_or_inv_mem' x := by
    rcases V.mem_or_inv_mem (e.symm x) with hx | hx
    · left
      exact Subring.mem_map_equiv.mpr hx
    · right
      change x⁻¹ ∈ V.toSubring.map e.toRingHom
      apply
        (Subring.mem_map_equiv
          (f := e) (K := V.toSubring) (x := x⁻¹)).mpr
      simpa using hx

@[simp]
theorem mem_mapEquiv_iff
    (e : F ≃+* G) (V : ValuationSubring F) (x : G) :
    x ∈ mapEquiv e V ↔ e.symm x ∈ V :=
  Subring.mem_map_equiv

/-- The source valuation ring is ring-isomorphic to its transported image. -/
def equivMapEquiv (e : F ≃+* G) (V : ValuationSubring F) :
    V ≃+* mapEquiv e V :=
  V.toSubring.equivMapOfInjective e.toRingHom e.injective

@[simp]
theorem coe_equivMapEquiv
    (e : F ≃+* G) (V : ValuationSubring F) (x : V) :
    ((equivMapEquiv e V x : mapEquiv e V) : G) = e x :=
  rfl

@[simp]
theorem mapEquiv_symm_mapEquiv
    (e : F ≃+* G) (V : ValuationSubring F) :
    mapEquiv e.symm (mapEquiv e V) = V := by
  ext x
  simp

end ValuationSubring

namespace DiscreteKValuation

@[ext]
theorem ext
    {v w : DiscreteKValuation K F}
    (h : v.valuationSubring = w.valuationSubring) :
    v = w := by
  cases v
  cases w
  cases h
  rfl

/-- Transport a discrete `K`-valuation across a `K`-field equivalence. -/
def map (e : F ≃ₐ[K] G) (v : DiscreteKValuation K F) :
    DiscreteKValuation K G where
  valuationSubring := ValuationSubring.mapEquiv e.toRingEquiv v.valuationSubring
  isDiscreteValuationRing := by
    let : IsDiscreteValuationRing v.valuationSubring :=
      v.isDiscreteValuationRing
    exact
      IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
        (ValuationSubring.equivMapEquiv
          e.toRingEquiv v.valuationSubring)
  algebraMap_mem x := by
    rw [ValuationSubring.mem_mapEquiv_iff]
    simpa using v.algebraMap_mem x

/-- The valuation rings before and after transport are `K`-algebra equivalent. -/
def valuationSubringAlgEquiv
    (e : F ≃ₐ[K] G) (v : DiscreteKValuation K F) :
    v.valuationSubring ≃ₐ[K] (map e v).valuationSubring where
  __ :=
    ValuationSubring.equivMapEquiv e.toRingEquiv v.valuationSubring
  commutes' x := by
    apply Subtype.ext
    exact e.commutes x

/-- Transport induces a `K`-algebra equivalence of residue fields. -/
def residueFieldAlgEquiv
    (e : F ≃ₐ[K] G) (v : DiscreteKValuation K F) :
    v.ResidueField ≃ₐ[K] (map e v).ResidueField :=
  IsLocalRing.ResidueField.mapAlgEquiv
    (valuationSubringAlgEquiv e v)

@[simp]
theorem map_symm_map
    (e : F ≃ₐ[K] G) (v : DiscreteKValuation K F) :
    map e.symm (map e v) = v := by
  apply ext
  exact
    ValuationSubring.mapEquiv_symm_mapEquiv
      e.toRingEquiv v.valuationSubring

end DiscreteKValuation

namespace FunctionFieldPrimeDivisor

@[ext]
theorem ext
    {v w : FunctionFieldPrimeDivisor K F}
    (h : v.toDiscreteKValuation = w.toDiscreteKValuation) :
    v = w := by
  cases v
  cases w
  cases h
  rfl

/-- Transport a Fried--Jarden prime divisor across a `K`-field equivalence. -/
def map (e : F ≃ₐ[K] G) (v : FunctionFieldPrimeDivisor K F) :
    FunctionFieldPrimeDivisor K G where
  toDiscreteKValuation := v.toDiscreteKValuation.map e
  residueFinite := by
    exact
      Module.Finite.of_surjective
        (DiscreteKValuation.residueFieldAlgEquiv
          e v.toDiscreteKValuation).toLinearMap
        (DiscreteKValuation.residueFieldAlgEquiv
          e v.toDiscreteKValuation).surjective

/-- The valuation-ring equivalence underlying transport of a prime divisor. -/
def valuationSubringAlgEquiv
    (e : F ≃ₐ[K] G) (v : FunctionFieldPrimeDivisor K F) :
    v.valuationSubring ≃ₐ[K] (map e v).valuationSubring :=
  DiscreteKValuation.valuationSubringAlgEquiv
    e v.toDiscreteKValuation

theorem degree_map
    (e : F ≃ₐ[K] G) (v : FunctionFieldPrimeDivisor K F) :
    (map e v).degree = v.degree := by
  exact
    (DiscreteKValuation.residueFieldAlgEquiv
      e v.toDiscreteKValuation).toLinearEquiv.finrank_eq.symm

@[simp]
theorem map_symm_map
    (e : F ≃ₐ[K] G) (v : FunctionFieldPrimeDivisor K F) :
    map e.symm (map e v) = v := by
  apply ext
  exact DiscreteKValuation.map_symm_map e v.toDiscreteKValuation

/-- Prime divisors are invariant under `K`-equivalence of function fields. -/
def equivOfAlgEquiv (e : F ≃ₐ[K] G) :
    FunctionFieldPrimeDivisor K F ≃ FunctionFieldPrimeDivisor K G where
  toFun := map e
  invFun := map e.symm
  left_inv := map_symm_map e
  right_inv v := by
    simpa using map_symm_map e.symm v

theorem finiteAlong_map
    {A : Type*} [CommRing A] [Algebra K A]
    (e : F ≃ₐ[K] G) (v : FunctionFieldPrimeDivisor K F)
    (ι : A →ₐ[K] F) (h : v.FiniteAlong ι) :
    (map e v).FiniteAlong (e.toAlgHom.comp ι) := by
  intro a
  change
    e (ι a) ∈
      ValuationSubring.mapEquiv e.toRingEquiv v.valuationSubring
  rw [ValuationSubring.mem_mapEquiv_iff]
  simpa using h a

theorem finiteAlong_map_iff
    {A : Type*} [CommRing A] [Algebra K A]
    (e : F ≃ₐ[K] G) (v : FunctionFieldPrimeDivisor K F)
    (ι : A →ₐ[K] F) :
    (map e v).FiniteAlong (e.toAlgHom.comp ι) ↔
      v.FiniteAlong ι := by
  constructor
  · intro h a
    have ha := h a
    change
      e (ι a) ∈
        ValuationSubring.mapEquiv e.toRingEquiv v.valuationSubring at ha
    rw [ValuationSubring.mem_mapEquiv_iff] at ha
    simpa using ha
  · exact finiteAlong_map e v ι

/-- Centers are preserved by simultaneous transport of the field and model map. -/
theorem centerAlong_map
    {A : Type*} [CommRing A] [Algebra K A]
    (e : F ≃ₐ[K] G) (v : FunctionFieldPrimeDivisor K F)
    (ι : A →ₐ[K] F) (h : v.FiniteAlong ι) :
    (map e v).centerAlong (e.toAlgHom.comp ι)
        (finiteAlong_map e v ι h) =
      v.centerAlong ι h := by
  let :
      IsLocalHom
        (valuationSubringAlgEquiv e v).toRingEquiv.toRingHom :=
    IsLocalHom.of_surjective _
      (valuationSubringAlgEquiv e v).surjective
  have hhom :
      (map e v).finiteAlongRingHom
          (e.toAlgHom.comp ι) (finiteAlong_map e v ι h) =
        (valuationSubringAlgEquiv
          e v).toRingEquiv.toRingHom.comp
          (v.finiteAlongRingHom ι h) := by
    ext a
    rfl
  unfold centerAlong
  rw [hhom, ← Ideal.comap_comap,
    IsLocalRing.maximalIdeal_comap]

end FunctionFieldPrimeDivisor

end Chapter06
end FieldArithmetic
