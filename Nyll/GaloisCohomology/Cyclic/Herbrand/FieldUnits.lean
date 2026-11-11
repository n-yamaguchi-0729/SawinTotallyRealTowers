/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.Norm.Transitivity
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
public import Nyll.GaloisCohomology.Cyclic.TateH0.Invariants
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient

/-!
# Fixed field units and their actual norm quotient

The existing descent of invariant units identifies the multiplicative fixed subgroup with
the units of the base field. The norm is the product of the original Galois conjugates, so
this same descent identifies the Herbrand norm subgroup with the actual field norm image.
The construction permits independent universes for the two original fields.
-/

@[expose] public section

noncomputable section

universe u v

namespace LocalClassFieldTheory

open CyclicCohomology CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/-- Multiplicative fixed units and the invariant submodule of the actual unit
representation are the same additive group. -/
def additiveFixedUnitsEquivInvariants :
    Additive (fixedSubgroup (Gal(L / K)) Lˣ) ≃+
      unitsInvariantSubmodule K L where
  toFun x := ⟨Additive.ofMul ((Additive.toMul x : fixedSubgroup (Gal(L / K)) Lˣ) : Lˣ), by
    intro σ
    exact congrArg Additive.ofMul ((Additive.toMul x).property σ)⟩
  invFun x := Additive.ofMul ⟨Additive.toMul (x : Additive Lˣ), by
    intro σ
    exact Additive.ofMul.injective (x.property σ)⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl

end LocalClassFieldTheory

namespace CyclicCohomology

open LocalFieldTheory ProfiniteCohomology.Herbrand
open scoped BigOperators

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The original invariant-unit descent, written multiplicatively. -/
def fixedUnitsEquivBaseUnits : fixedSubgroup Gal(L/K) Lˣ ≃* Kˣ :=
  MulEquiv.toAdditive.symm
    ((LocalClassFieldTheory.additiveFixedUnitsEquivInvariants K L).trans
      (invariantsUnitsAddEquivBaseUnits K L))

/-- Re-embedding a descended fixed unit recovers its original value. -/
theorem fixedUnitsEquivBaseUnits_spec (x : fixedSubgroup Gal(L/K) Lˣ) :
    algebraMap K L (fixedUnitsEquivBaseUnits K L x : K) = ((x : Lˣ) : L) :=
  invariantsUnitsAddEquivBaseUnits_spec K L
    (LocalClassFieldTheory.additiveFixedUnitsEquivInvariants K L (Additive.ofMul x))

/-- The multiplicative Herbrand norm is the original field norm after embedding the base. -/
theorem tateNorm_units_val (a : Lˣ) :
    ((tateNorm Gal(L/K) Lˣ a : Lˣ) : L) =
      algebraMap K L (Algebra.norm K (a : L)) := by
  change ((∏ σ : Gal(L/K), Units.map σ.toMonoidHom a : Lˣ) : L) = _
  rw [Units.coe_prod]
  exact (Algebra.norm_eq_prod_automorphisms (K := K) (a : L)).symm

/-- The same descent sends precisely the original Herbrand norms to field-unit norms. -/
theorem fixedUnitsEquivBaseUnits_map_normSubgroup :
    ((tateNormSubgroup Gal(L/K) Lˣ).subgroupOf (fixedSubgroup Gal(L/K) Lˣ)).map
        (fixedUnitsEquivBaseUnits K L).toMonoidHom = localNormSubgroup K L := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ∃ a : Lˣ, tateNorm Gal(L/K) Lˣ a = (x : Lˣ) at hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    apply Units.ext
    apply (algebraMap K L).injective
    calc
      algebraMap K L (normUnits K L a : K) =
          ((tateNorm Gal(L/K) Lˣ a : Lˣ) : L) := (tateNorm_units_val K L a).symm
      _ = ((x : Lˣ) : L) := congrArg (fun z : Lˣ => (z : L)) ha
      _ = algebraMap K L (fixedUnitsEquivBaseUnits K L x : K) :=
        (fixedUnitsEquivBaseUnits_spec K L x).symm
  · rintro ⟨a, rfl⟩
    let x : fixedSubgroup Gal(L/K) Lˣ :=
      ⟨tateNorm Gal(L/K) Lˣ a, tateNormSubgroup_le_fixedSubgroup ⟨a, rfl⟩⟩
    refine ⟨x, ⟨a, rfl⟩, ?_⟩
    apply Units.ext
    apply (algebraMap K L).injective
    exact (fixedUnitsEquivBaseUnits_spec K L x).trans (tateNorm_units_val K L a)

/-- The actual fixed-unit Herbrand quotient is the original field norm quotient. -/
def herbrandH0UnitsEquivNormQuotient : HerbrandH0 Gal(L/K) Lˣ ≃* NormQuotient K L :=
  (HerbrandH0.equiv (G := Gal(L/K)) (A := Lˣ)).trans
    ((QuotientGroup.congr _ _ (fixedUnitsEquivBaseUnits K L)
      (fixedUnitsEquivBaseUnits_map_normSubgroup K L)).trans
        (normQuotientConcreteEquiv K L).symm)

/-- On a fixed unit, the quotient comparison is the class of its actual descended value. -/
theorem herbrandH0UnitsEquivNormQuotient_mk (x : fixedSubgroup Gal(L/K) Lˣ) :
    herbrandH0UnitsEquivNormQuotient K L (HerbrandH0.mk x) =
      normClass K L (fixedUnitsEquivBaseUnits K L x) := rfl

end CyclicCohomology
