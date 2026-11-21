/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.SetTheory.Cardinal.Finite
public import Nyll.GaloisCohomology.Cyclic.GaloisCohomology
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing
public import Nyll.GaloisCohomology.Cyclic.TateH0.Main
public import Nyll.GaloisCohomology.Cyclic.TateH0.NormImage
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.FixedCycles
public import Nyll.GaloisCohomology.Cyclic.Herbrand.FieldUnits
public import Nyll.GaloisCohomology.Cyclic.TateComparison
public import Nyll.GaloisCohomology.Cyclic.TateFixedCycles

/-!
# The actual low-degree Tate quotients as Herbrand quotients

This file compares the concrete multiplicative Herbrand quotients from
low-degree cyclic cohomology with the Tate objects built from mathlib's actual
Galois representation on `Lˣ`.  The comparison uses the standard Galois action
on units; it does not introduce a replacement coefficient object.
-/

@[expose] public section

namespace LocalClassFieldTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CategoryTheory

universe u v

section Quotient

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/-- The norm in the actual unit representation is the multiplicative Herbrand
norm after passing from `Additive Lˣ` back to `Lˣ`. -/
theorem unitsNormLinearMap_toMul_eq_tateNorm
    [Fintype (Gal(L/K))] (x : Lˣ) :
    Additive.toMul (unitsNormLinearMap K L (Additive.ofMul x)) =
      tateNorm (Gal(L / K)) Lˣ x := by
  have hnorm :
      unitsNormLinearMap K L (Additive.ofMul x) =
        ∑ σ : Gal(L / K), (Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x) := by
    exact LinearMap.sum_apply Finset.univ
      (fun σ : Gal(L / K) => (Rep.ofAlgebraAutOnUnits K L).ρ σ)
      (Additive.ofMul x : Additive Lˣ)
  rw [hnorm]
  calc
    (Additive.toMul
        ((∑ σ : Gal(L / K), (Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x)) :
          Additive Lˣ) : Lˣ) =
        ∏ σ : Gal(L / K),
          (Additive.toMul
            ((Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x) : Additive Lˣ) : Lˣ) := by
      simpa only using additive_toMul_finset_sum_units L Finset.univ
        (fun σ : Gal(L / K) => (Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x))
    _ = tateNorm (Gal(L / K)) Lˣ x := by
      rfl

/-- Compose an additive equivalence with a submodule quotient map.

Keeping this construction polymorphic prevents typeclass search from unfolding
the concrete Galois representation while it looks for the quotient's additive
structure. -/
def additiveEquivToQuotientHom
    {A M : Type*} [AddCommGroup A] [AddCommGroup M]
    (e : A ≃+ M) (N : Submodule ℤ M) : A →+ M ⧸ N :=
  N.mkQ.toAddMonoidHom.comp e.toAddMonoidHom

/-- Multiplicative form of an additive homomorphism, kept polymorphic for the
same elaboration reason as `additiveEquivToQuotientHom`. -/
def additiveHomToMultiplicativeHom
    {G B : Type*} [Group G] [AddCommGroup B]
    (f : Additive G →+ B) : G →* Multiplicative B :=
  AddMonoidHom.toMultiplicativeRight f

/-- The multiplicative group structure on an additive submodule quotient.
This is passed explicitly at concrete call sites to avoid rediscovering it by
unfolding the coefficient representation. -/
@[implicit_reducible]
def multiplicativeQuotientGroup
    {M : Type*} [AddCommGroup M] (N : Submodule ℤ M) :
    Group (Multiplicative (M ⧸ N)) :=
  Multiplicative.group

/-- Kernel of a homomorphism into a multiplicative additive quotient, with the
codomain structure supplied directly. -/
def kernelOfAdditiveQuotientHom
    {G M : Type*} [Group G] [AddCommGroup M]
    (N : Submodule ℤ M) (f : G →* Multiplicative (M ⧸ N)) : Subgroup G :=
  @MonoidHom.ker G inferInstance (Multiplicative (M ⧸ N))
    (multiplicativeQuotientGroup N).toMulOneClass f

/-- First-isomorphism-theorem comparison for a surjection onto a
multiplicative additive quotient. -/
def quotientMulEquivOfSurjectiveAdditiveQuotient
    {G M : Type*} [CommGroup G] [AddCommGroup M]
    (N : Submodule ℤ M) (S : Subgroup G)
    (f : G →* Multiplicative (M ⧸ N))
    (hker : kernelOfAdditiveQuotientHom N f = S)
    (hsurj : Function.Surjective f) :
    G ⧸ S ≃* Multiplicative (M ⧸ N) := by
  letI : Group (Multiplicative (M ⧸ N)) := multiplicativeQuotientGroup N
  exact
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)

/-- Additive quotient map from fixed units to invariant units modulo norms. -/
def additiveFixedUnitToInvariantsNormQuotientHom
    [Fintype (Gal(L/K))] :
    Additive (fixedSubgroup (Gal(L / K)) Lˣ) →+
      (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
  additiveEquivToQuotientHom (additiveFixedUnitsEquivInvariants K L)
    (unitsTateH0NormSubmodule K L)

/-- Send a fixed unit to its invariant-unit class modulo norms. -/
def fixedUnitToInvariantsNormQuotientMonoidHom
    [Fintype (Gal(L/K))] :
    fixedSubgroup (Gal(L / K)) Lˣ →*
      Multiplicative
        (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
  additiveHomToMultiplicativeHom
    (additiveFixedUnitToInvariantsNormQuotientHom K L)

/-- A fixed unit maps to its canonical invariant-unit class modulo norms. -/
@[simp]
theorem fixedUnitToInvariantsNormQuotientMonoidHom_apply
    [Fintype (Gal(L/K))] (x : fixedSubgroup (Gal(L/K)) Lˣ) :
    Multiplicative.toAdd
        (fixedUnitToInvariantsNormQuotientMonoidHom K L x) =
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) :=
  rfl

/-- The kernel of the fixed-unit quotient map is exactly
the Herbrand norm subgroup inside the fixed subgroup. -/
theorem fixedUnitToInvariantsNormQuotientMonoidHom_ker
    [Fintype (Gal(L/K))] :
    kernelOfAdditiveQuotientHom (unitsTateH0NormSubmodule K L)
        (fixedUnitToInvariantsNormQuotientMonoidHom K L) =
      (tateNormSubgroup (Gal(L / K)) Lˣ).subgroupOf
        (fixedSubgroup (Gal(L / K)) Lˣ) := by
  ext x
  constructor
  · intro hx
    have hx0 := congrArg Multiplicative.toAdd hx
    change
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) = 0 at hx0
    have hxmem :
        additiveFixedUnitsEquivInvariants K L (Additive.ofMul x) ∈
          unitsTateH0NormSubmodule K L :=
      (Submodule.Quotient.mk_eq_zero (unitsTateH0NormSubmodule K L)).1 hx0
    rcases hxmem with ⟨y, hy⟩
    change (x : Lˣ) ∈ tateNormSubgroup (Gal(L / K)) Lˣ
    refine ⟨Additive.toMul y, ?_⟩
    have hy' := congrArg
      (fun z : unitsInvariantSubmodule K L =>
        Additive.toMul (z : Additive Lˣ)) hy
    change Additive.toMul (unitsNormLinearMap K L y) = (x : Lˣ) at hy'
    rw [tateNormHom_apply,
      ← unitsNormLinearMap_toMul_eq_tateNorm K L (Additive.toMul y)]
    simpa using hy'
  · intro hx
    change (x : Lˣ) ∈ tateNormSubgroup (Gal(L / K)) Lˣ at hx
    rcases hx with ⟨y, hy⟩
    apply Multiplicative.toAdd.injective
    change
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) = 0
    apply (Submodule.Quotient.mk_eq_zero (unitsTateH0NormSubmodule K L)).2
    change additiveFixedUnitsEquivInvariants K L (Additive.ofMul x) ∈
      LinearMap.range (unitsNormToInvariantsLinearMap K L)
    refine ⟨Additive.ofMul y, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    change Additive.toMul
      (unitsNormLinearMap K L (Additive.ofMul y)) = (x : Lˣ)
    rw [unitsNormLinearMap_toMul_eq_tateNorm K L y]
    exact hy

/-- Every invariant-unit class modulo norms has a multiplicatively fixed representative. -/
theorem fixedUnitToInvariantsNormQuotientMonoidHom_surjective
    [Fintype (Gal(L/K))] :
    Function.Surjective (fixedUnitToInvariantsNormQuotientMonoidHom K L) := by
  intro q
  rcases Submodule.mkQ_surjective (unitsTateH0NormSubmodule K L)
      (Multiplicative.toAdd q) with ⟨z, hz⟩
  let x : fixedSubgroup (Gal(L / K)) Lˣ :=
    Additive.toMul ((additiveFixedUnitsEquivInvariants K L).symm z)
  refine ⟨x, ?_⟩
  apply Multiplicative.toAdd.injective
  change
    (unitsTateH0NormSubmodule K L).mkQ
      (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) =
        Multiplicative.toAdd q
  calc
    _ = (unitsTateH0NormSubmodule K L).mkQ z := by
      apply congrArg (unitsTateH0NormSubmodule K L).mkQ
      change additiveFixedUnitsEquivInvariants K L
        ((additiveFixedUnitsEquivInvariants K L).symm z) = z
      exact (additiveFixedUnitsEquivInvariants K L).apply_symm_apply z
    _ = Multiplicative.toAdd q := hz

/-- The multiplicative Herbrand quotient is the invariant-unit quotient by norms. -/
def herbrandH0MulEquivInvariantsNormQuotient
    [Fintype (Gal(L/K))] :=
  quotientMulEquivOfSurjectiveAdditiveQuotient
    (unitsTateH0NormSubmodule K L)
    ((tateNormSubgroup (Gal(L / K)) Lˣ).subgroupOf
      (fixedSubgroup (Gal(L / K)) Lˣ))
    (fixedUnitToInvariantsNormQuotientMonoidHom K L)
    (fixedUnitToInvariantsNormQuotientMonoidHom_ker K L)
    (fixedUnitToInvariantsNormQuotientMonoidHom_surjective K L)

end Quotient

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The multiplicative Herbrand quotient of field units is mathlib's
degree-zero Tate cohomology. -/
def herbrandH0EquivTateCohomologyZero [Fintype (Gal(L/K))] :
    HerbrandH0 (Gal(L / K)) Lˣ ≃
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0 :=
  Additive.ofMul.trans
    (tateH0IsoHerbrandH0 (G := Gal(L / K)) (A := Lˣ)).symm.toLinearEquiv.toEquiv

/-- The generic comparison preserves the actual fixed-unit representative. -/
theorem herbrandH0EquivTateCohomologyZero_mk [Fintype (Gal(L/K))]
    (a : fixedSubgroup Gal(L/K) Lˣ) :
    herbrandH0EquivTateCohomologyZero K L (HerbrandH0.mk a) =
      (tateComplex (Rep.ofAlgebraAutOnUnits K L)).homologyπ 0
        (tateH0FixedCycle a) := by
  let e := tateH0IsoHerbrandH0 (G := Gal(L / K)) (A := Lˣ)
  let t := (tateComplex (Rep.ofAlgebraAutOnUnits K L)).homologyπ 0 (tateH0FixedCycle a)
  have he : e.hom t = Additive.ofMul (HerbrandH0.mk a) := tateH0IsoHerbrandH0_fixedCycle a
  exact (congrArg (fun z => e.inv z) he.symm).trans (Iso.hom_inv_id_apply e t)

/-- The direct Herbrand norm comparison used at completions and globally is
the original Tate route on every fixed unit and hence on the whole quotient. -/
theorem herbrandH0UnitsEquivNormQuotient_tate [FiniteDimensional K L] [IsGalois K L] :
    let := AlgEquiv.fintype K L
    ∀ a : HerbrandH0 (Gal(L / K)) Lˣ,
      Additive.toMul ((H0TateUnitsIsoNormQuotient K L).hom
        (herbrandH0EquivTateCohomologyZero K L a)) = herbrandH0UnitsEquivNormQuotient K L a := by
  intro hFintype a
  obtain ⟨b, rfl⟩ := HerbrandH0.mk_surjective a
  let x := additiveFixedUnitsEquivInvariants K L (Additive.ofMul b)
  have hx : herbrandH0EquivTateCohomologyZero K L (HerbrandH0.mk b) =
      TateCohomology.fixedClass (Rep.ofAlgebraAutOnUnits K L) x :=
    herbrandH0EquivTateCohomologyZero_mk K L b
  rw [hx]
  exact (congrArg Additive.toMul (H0TateUnitsIsoNormQuotient_fixedClass K L x)).trans
      (herbrandH0UnitsEquivNormQuotient_mk K L b).symm

/-- Cardinality transport from the concrete Herbrand quotient to mathlib's
degree-zero Tate cohomology. -/
theorem cardinalMk_herbrandH0_fieldUnits_eq_tateCohomology_zero
    [Fintype (Gal(L/K))] :
    Cardinal.mk (HerbrandH0 (Gal(L / K)) Lˣ) =
      Cardinal.mk (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) :=
  Cardinal.mk_congr (herbrandH0EquivTateCohomologyZero K L)

/-- Genuine comparison of the multiplicative `H⁻¹` quotient
for field units with Mathlib's actual Tate `H⁻¹` object. -/
noncomputable def herbrandHminusOneEquivUnitsTateHminusOne
    [FiniteDimensional K L] (g : Gal(L/K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) :
    HerbrandHMinusOne (Gal(L / K)) Lˣ g ≃
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1) :=
  Additive.ofMul.trans
    (tateHMinusOneIsoHerbrandHMinusOne (G := Gal(L / K)) (A := Lˣ)
      g hg).symm.toLinearEquiv.toEquiv

/-- The field-unit comparison retains the class of the original norm-kernel
unit and uses the given generator for the augmentation boundary. -/
theorem herbrandHminusOneEquivUnitsTateHminusOne_mk
    [FiniteDimensional K L] (g : Gal(L/K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g)
    (a : normKernelSubgroup (Gal(L / K)) Lˣ) :
    let M := Rep.ofAlgebraAutOnUnits K L
    let z : LinearMap.ker M.ρ.norm :=
      (normKernelCyclesAddEquiv (G := Gal(L / K)) (A := Lˣ)).symm (Additive.ofMul a)
    herbrandHminusOneEquivUnitsTateHminusOne K L g hg (HerbrandHMinusOne.mk g a) =
      TateCohomology.normKernelClass M z := by
  intro M z
  let e := tateHMinusOneIsoHerbrandHMinusOne (G := Gal(L / K)) (A := Lˣ) g hg
  let t := TateCohomology.normKernelClass M z
  have he : e.hom t = Additive.ofMul (HerbrandHMinusOne.mk g a) :=
    tateHMinusOneIsoHerbrandHMinusOne_normKernelClass g hg a
  exact (congrArg (fun w => e.inv w) he.symm).trans (Iso.hom_inv_id_apply e t)

/-- Cardinality transport from the concrete Herbrand `H⁻¹` quotient to
the actual Tate `H⁻¹` object.  The statement is valid without introducing an
extraneous finiteness hypothesis. -/
theorem cardinalMk_herbrandHminusOne_fieldUnits_eq_unitsTateHminusOne
    [FiniteDimensional K L] (g : Gal(L/K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) :
    Cardinal.mk (HerbrandHMinusOne (Gal(L / K)) Lˣ g) =
      Cardinal.mk (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) :=
  Cardinal.mk_congr (herbrandHminusOneEquivUnitsTateHminusOne K L g hg)

end
end LocalClassFieldTheory
