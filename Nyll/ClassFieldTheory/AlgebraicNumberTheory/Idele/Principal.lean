/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisDescent

/-!
# Principal ideles and their Galois module structure

This module exposes the diagonal embedding and idele class group, identifies
field units with principal relative ideles, and transports low-degree Tate
cohomology across that identification.
-/



@[expose] public section

noncomputable section

universe u v

open RelativeIdeleGroup.Cohomology


open LocalClassFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The field-unit group is multiplicatively equivalent to the actual
subgroup of principal relative ideles. -/
noncomputable def fieldUnitsEquivPrincipalIdeles :
    Lˣ ≃*
      RelativeIdeleGroup.principalSubgroup K L :=
  MulEquiv.ofBijective
    (RelativeIdeleGroup.principalIdele K L).rangeRestrict
    ⟨fun _ _ h ↦
        RelativeIdeleGroup.principalIdele_injective K L
          (congrArg Subtype.val h),
      (RelativeIdeleGroup.principalIdele K L).rangeRestrict_surjective⟩

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem fieldUnitsEquivPrincipalIdeles_coe
    (x : Lˣ) :
    ((fieldUnitsEquivPrincipalIdeles K L x :
        RelativeIdeleGroup.principalSubgroup K L) :
      RelativeIdeleGroup K L) =
        RelativeIdeleGroup.principalIdele K L x :=
  rfl

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The identification of field units with principal ideles is equivariant
for the genuine Galois actions. -/
theorem fieldUnitsEquivPrincipalIdeles_smul
    (σ : L ≃ₐ[K] L) (x : Lˣ) :
    let :=
      galoisGroupFieldUnitsMulDistribMulAction K L
    let :=
      relativeIdeleMulDistribMulAction K L
    let :=
      principalIdeleMulDistribMulAction K L
    fieldUnitsEquivPrincipalIdeles K L (σ • x) =
      σ • fieldUnitsEquivPrincipalIdeles K L x := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
  apply Subtype.ext
  change
    RelativeIdeleGroup.principalIdele K L
        (Units.mapEquiv σ.toMulEquiv x) =
      σ • RelativeIdeleGroup.principalIdele K L x
  exact
    (RelativeIdeleGroup.smul_principalIdele
      K L σ x).symm

/-- Degree-zero Tate cohomology of principal ideles is the actual
degree-zero cohomology of `Lˣ`. -/
noncomputable def fieldUnitsHerbrandH0EquivPrincipalIdeles :
    let :=
      galoisGroupFieldUnitsMulDistribMulAction K L
    let :=
      relativeIdeleMulDistribMulAction K L
    let :=
      principalIdeleMulDistribMulAction K L
    HerbrandH0 (L ≃ₐ[K] L) Lˣ ≃*
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
  exact
    herbrandH0EquivariantMulEquiv
      (fieldUnitsEquivPrincipalIdeles K L)
      (fieldUnitsEquivPrincipalIdeles_smul K L)

/-- Degree-minus-one Tate cohomology of principal ideles is the actual
degree-minus-one cohomology of `Lˣ`. -/
noncomputable def fieldUnitsHerbrandHMinusOneEquivPrincipalIdeles
    (σ : L ≃ₐ[K] L) :
    let :=
      galoisGroupFieldUnitsMulDistribMulAction K L
    let :=
      relativeIdeleMulDistribMulAction K L
    let :=
      principalIdeleMulDistribMulAction K L
    HerbrandHMinusOne (L ≃ₐ[K] L) Lˣ σ ≃*
      HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) σ := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
  exact
    herbrandHMinusOneEquivariantMulEquiv
      (fieldUnitsEquivPrincipalIdeles K L)
      (fieldUnitsEquivPrincipalIdeles_smul K L) σ
omit [NumberField L] [IsGalois K L] in
/-- A defined Herbrand quotient for field units supplies the corresponding
defined quotient for the actual principal-idele subgroup. -/
theorem principalIdelesHerbrandQuotientDefined
    (σ : L ≃ₐ[K] L)
    (h :
      letI :=
        galoisGroupFieldUnitsMulDistribMulAction K L
      HerbrandQuotientDefined
        (L ≃ₐ[K] L) Lˣ σ) :
    letI :=
      relativeIdeleMulDistribMulAction K L
    letI :=
      principalIdeleMulDistribMulAction K L
    HerbrandQuotientDefined
      (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) σ := by
  let _ :=
    galoisGroupFieldUnitsMulDistribMulAction K L
  let _ :=
    relativeIdeleMulDistribMulAction K L
  let _ :=
    principalIdeleMulDistribMulAction K L
  let _ : Finite
      (HerbrandH0 (L ≃ₐ[K] L) Lˣ) :=
    h.1
  let _ : Finite
      (HerbrandHMinusOne
        (L ≃ₐ[K] L) Lˣ σ) :=
    h.2
  exact
    ⟨herbrandH0Finite_of_equivariantMulEquiv
        (fieldUnitsEquivPrincipalIdeles K L)
        (fieldUnitsEquivPrincipalIdeles_smul K L),
      herbrandHMinusOneFinite_of_equivariantMulEquiv
        (fieldUnitsEquivPrincipalIdeles K L)
        (fieldUnitsEquivPrincipalIdeles_smul K L) σ⟩

omit [NumberField L] [IsGalois K L] in
/-- The field-unit and principal-idele Herbrand quotients agree. -/
theorem fieldUnits_herbrandQuotient_eq_principalIdeles
    (σ : L ≃ₐ[K] L)
    (h :
      letI :=
        galoisGroupFieldUnitsMulDistribMulAction K L
      HerbrandQuotientDefined
        (L ≃ₐ[K] L) Lˣ σ) :
    letI _fieldAction :=
      galoisGroupFieldUnitsMulDistribMulAction K L
    letI _relativeAction :=
      relativeIdeleMulDistribMulAction K L
    letI _principalAction :=
      principalIdeleMulDistribMulAction K L
    let hP :=
      principalIdelesHerbrandQuotientDefined
        K L σ h
    @herbrandQuotient
        (L ≃ₐ[K] L) Lˣ _ _ _
        (galoisGroupFieldUnitsMulDistribMulAction K L)
        σ h.1 h.2 =
      @herbrandQuotient
        (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L)
        _ _ _
        (principalIdeleMulDistribMulAction K L)
        σ hP.1 hP.2 := by
  let _ :=
    galoisGroupFieldUnitsMulDistribMulAction K L
  let _ :=
    relativeIdeleMulDistribMulAction K L
  let _ :=
    principalIdeleMulDistribMulAction K L
  let _ : Finite
      (HerbrandH0 (L ≃ₐ[K] L) Lˣ) :=
    h.1
  let _ : Finite
      (HerbrandHMinusOne
        (L ≃ₐ[K] L) Lˣ σ) :=
    h.2
  exact
    herbrandQuotient_eq_of_equivariantMulEquiv
      (fieldUnitsEquivPrincipalIdeles K L)
      (fieldUnitsEquivPrincipalIdeles_smul K L) σ
