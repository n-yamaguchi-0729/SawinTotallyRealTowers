/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.FamilyCardinality
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv

/-!
# Transport from local blocks to unrestricted factors

This leaf transports the finite-family Herbrand calculation to the actual
unrestricted relative S-idele factors.
-/



@[expose] public section

open scoped NumberField BigOperators ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] in
/-- The equivariant realization by local blocks identifies degree-zero
Herbrand cohomology of the actual unrestricted factors with that of the
local-block family. -/
noncomputable def
    relativeUnrestrictedSPlaceFactorsHerbrandH0EquivLocalBlockFamily
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let d := relativeUnrestrictedSPlaceDatum (K := K) (L := L) S
    let A := RelativeUnrestrictedSPlaceFactors (K := K) (L := L) S
    let B := LocalBlockFamily d
    let aGroup : CommGroup A := Pi.commGroup
    let bGroup : CommGroup B := Pi.commGroup
    let aAction := relativeUnrestrictedSPlaceFactorsAction (K := K) (L := L) S
    let bAction := localBlockFamilyAction d
    @HerbrandH0 (L ≃ₐ[K] L) A AlgEquiv.aut (AlgEquiv.fintype K L) aGroup aAction ≃*
      @HerbrandH0 (L ≃ₐ[K] L) B AlgEquiv.aut (AlgEquiv.fintype K L) bGroup bAction := by
  intro d A B aGroup bGroup aAction bAction
  let e :
      @MulEquiv A B aGroup.toMulOneClass.toMulOne.toMul bGroup.toMulOneClass.toMulOne.toMul := by
    dsimp (config := { instances := true, zetaDelta := true }) only
      [A, B, d, aGroup, bGroup, Pi.commGroup, Pi.group, Pi.divInvMonoid, Pi.commMonoid,
        Pi.monoid, Pi.mulOneClass, Pi.semigroup, Monoid.toMulOneClass, MulOneClass.toMulOne,
        MulOne.toMul]
    with_reducible exact relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily (K := K) (L := L) S
  have he (g : L ≃ₐ[K] L) (x : A) :
      e (aAction.smul g x) = bAction.smul g (e x) := by
    dsimp (config := { instances := true, zetaDelta := true }) only
      [e, id, A, B, d, aGroup, bGroup, Pi.commGroup, Pi.group,
        Pi.divInvMonoid, Pi.commMonoid, Pi.monoid, Pi.mulOneClass, Pi.semigroup,
        Monoid.toMulOneClass, MulOneClass.toMulOne, MulOne.toMul]
    with_reducible exact
      relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily_smul (K := K) (L := L) S g x
  exact @herbrandH0EquivariantMulEquiv (L ≃ₐ[K] L) A B
    AlgEquiv.aut (AlgEquiv.fintype K L) aGroup bGroup aAction bAction e he

omit [NumberField L] in
/-- The equivariant realization by local blocks identifies degree-minus-one
Herbrand cohomology of the actual unrestricted factors with that of the
local-block family. -/
noncomputable def
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneEquivLocalBlockFamily
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) :
    let d := relativeUnrestrictedSPlaceDatum (K := K) (L := L) S
    let A := RelativeUnrestrictedSPlaceFactors (K := K) (L := L) S
    let B := LocalBlockFamily d
    let aGroup : CommGroup A := Pi.commGroup
    let bGroup : CommGroup B := Pi.commGroup
    let aAction := relativeUnrestrictedSPlaceFactorsAction (K := K) (L := L) S
    let bAction := localBlockFamilyAction d
    @HerbrandHMinusOne (L ≃ₐ[K] L) A AlgEquiv.aut (AlgEquiv.fintype K L) aGroup aAction σ ≃*
      @HerbrandHMinusOne (L ≃ₐ[K] L) B AlgEquiv.aut (AlgEquiv.fintype K L) bGroup bAction σ := by
  intro d A B aGroup bGroup aAction bAction
  let e :
      @MulEquiv A B aGroup.toMulOneClass.toMulOne.toMul bGroup.toMulOneClass.toMulOne.toMul := by
    dsimp (config := { instances := true, zetaDelta := true }) only
      [A, B, d, aGroup, bGroup, Pi.commGroup, Pi.group, Pi.divInvMonoid, Pi.commMonoid,
        Pi.monoid, Pi.mulOneClass, Pi.semigroup, Monoid.toMulOneClass, MulOneClass.toMulOne,
        MulOne.toMul]
    with_reducible exact relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily (K := K) (L := L) S
  have he (g : L ≃ₐ[K] L) (x : A) :
      e (aAction.smul g x) = bAction.smul g (e x) := by
    dsimp (config := { instances := true, zetaDelta := true }) only
      [e, id, A, B, d, aGroup, bGroup, Pi.commGroup, Pi.group,
        Pi.divInvMonoid, Pi.commMonoid, Pi.monoid, Pi.mulOneClass, Pi.semigroup,
        Monoid.toMulOneClass, MulOneClass.toMulOne, MulOne.toMul]
    with_reducible exact
      relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily_smul (K := K) (L := L) S g x
  exact @herbrandHMinusOneEquivariantMulEquiv (L ≃ₐ[K] L) A B
    AlgEquiv.aut (AlgEquiv.fintype K L) aGroup bGroup aAction bAction e he σ

omit [NumberField L] in
/-- Degree-zero cohomology of the actual unrestricted tensor factors is
finite. -/
theorem relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let : MulDistribMulAction (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors (K := K) (L := L) S) :=
      relativeUnrestrictedSPlaceFactorsAction (K := K) (L := L) S
    Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S)) := by
  intro sourceAction
  let := relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite (K := K) (L := L) S σ hgen
  let equiv := relativeUnrestrictedSPlaceFactorsHerbrandH0EquivLocalBlockFamily
    (K := K) (L := L) S
  exact Finite.of_equiv _ equiv.symm.toEquiv

omit [NumberField L] in
/-- Degree-minus-one cohomology of the actual unrestricted tensor
factors is finite. -/
theorem relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let : MulDistribMulAction (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors (K := K) (L := L) S) :=
      relativeUnrestrictedSPlaceFactorsAction (K := K) (L := L) S
    Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ) := by
  intro sourceAction
  let := relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite (K := K) (L := L) S σ hgen
  let equiv := relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneEquivLocalBlockFamily
    (K := K) (L := L) S σ
  exact Finite.of_equiv _ equiv.symm.toEquiv

omit [NumberField L] in
/-- Degree zero for the actual unrestricted factors: its
cardinality is the product of the local degrees. -/
theorem
    relativeUnrestrictedSPlaceFactorsHerbrandH0_card_eq_product
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    let : Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S)) :=
      relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
        S σ hgen
    Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S)) =
      ∏ i,
        relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i := by
  intro sourceAction sourceFinite
  let equiv := relativeUnrestrictedSPlaceFactorsHerbrandH0EquivLocalBlockFamily
    (K := K) (L := L) S
  have localCardinality :=
    relativeUnrestrictedLocalBlockFamilyHerbrandH0_card_eq_product (K := K) (L := L) S σ hgen
  exact (Nat.card_congr equiv.toEquiv).trans localCardinality

omit [NumberField L] in
/-- Degree minus one for the actual unrestricted factors:
the group has one element. -/
theorem
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOne_card_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    let : Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S) σ) :=
      relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
        S σ hgen
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S) σ) = 1 := by
  intro sourceAction sourceFinite
  let equiv := relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneEquivLocalBlockFamily
    (K := K) (L := L) S σ
  have localCardinality :=
    relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOne_card_eq_one (K := K) (L := L) S σ hgen
  exact (Nat.card_congr equiv.toEquiv).trans localCardinality

omit [NumberField L] in
/-- The Herbrand quotient formula for the actual unrestricted tensor factors. -/
theorem relativeUnrestrictedSPlaceFactors_herbrandQuotient
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    let : Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S)) :=
      relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
        S σ hgen
    let : Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S) σ) :=
      relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
        S σ hgen
    herbrandQuotient
        (G := L ≃ₐ[K] L)
        (A := RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ =
      ∏ i,
        (relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i : ℚ) := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
  rw [herbrandQuotient_eq_card_ratio,
    relativeUnrestrictedSPlaceFactorsHerbrandH0_card_eq_product
      S σ hgen,
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOne_card_eq_one
      S σ hgen]
  simp only [Nat.cast_prod, Nat.cast_one, div_one]
