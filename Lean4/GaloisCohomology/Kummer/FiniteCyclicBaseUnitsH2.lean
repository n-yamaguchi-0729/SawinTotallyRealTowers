/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.FiniteCyclicH2CoefficientNorm
import GaloisCohomology.ProP.FiniteCyclicCarryCocycle
import GaloisCohomology.ProP.FiniteCyclicBarPeriodicH2Comparison
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

set_option autoImplicit false

/-!
# Base-unit representatives for cyclic field-unit H²

The inclusion of base-field units is equivariant for the trivial action.
In a finite cyclic Galois extension, every H² class has a carry representative
with invariant coefficient; Galois fixed-value descent makes that coefficient
an actual base-field unit.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K M : Type) [Field K] [Field M] [Algebra K M]

/-- Inclusion of base units, from the trivial action to the actual Galois action. -/
def finiteGaloisBaseUnitsRepHom :
    Rep.trivial ℤ Gal(M/K) (Additive Kˣ) ⟶ Rep.ofAlgebraAutOnUnits K M := by
  apply Rep.ofHom
  refine ⟨(Units.map (algebraMap K M).toMonoidHom).toAdditive.toIntLinearMap, ?_⟩
  intro σ
  apply LinearMap.ext
  intro a
  apply Units.ext
  exact (σ.commutes ((show Additive Kˣ from a).toMul : K)).symm

/-- The actual coefficient map on H² induced by including base-field units. -/
def finiteGaloisBaseUnitsH2Map :
    groupCohomology (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits K M) 2 :=
  groupCohomology.map (MonoidHom.id Gal(M/K)) (finiteGaloisBaseUnitsRepHom K M) 2

variable [FiniteDimensional K M] [IsGalois K M]

private theorem exists_baseUnit_of_fixed (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ σ : Gal(M/K), (Rep.ofAlgebraAutOnUnits K M).ρ σ a = a) :
    ∃ b : Rep.trivial ℤ Gal(M/K) (Additive Kˣ),
      (finiteGaloisBaseUnitsRepHom K M).hom b = a := by
  have hfix (σ : Gal(M/K)) :
      σ ((show Additive Mˣ from a).toMul : M) = ((show Additive Mˣ from a).toMul : M) :=
    congrArg Units.val (ha σ)
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := K) (E := M) ((show Additive Mˣ from a).toMul : M)).mpr hfix
  have hb0 : b ≠ 0 := by
    intro h
    apply Units.ne_zero (show Additive Mˣ from a).toMul
    rw [← hb, h, map_zero]
  refine ⟨Additive.ofMul (Units.mk0 b hb0), ?_⟩
  apply Units.ext
  exact hb

/-- Every actual unit-coefficient H² class in a finite cyclic Galois extension
is supplied by a class with trivial base-unit coefficients. -/
theorem finiteCyclicBaseUnitsH2Map_surjective [IsCyclic Gal(M/K)] :
    Function.Surjective (finiteGaloisBaseUnitsH2Map K M).hom := by
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(M/K))
  intro x
  obtain ⟨a, ha⟩ := finiteCyclicGroupH2_piEven_surjective
    (Rep.ofAlgebraAutOnUnits K M) g hg x
  have hag : (Rep.ofAlgebraAutOnUnits K M).ρ g a.val = a.val := by
    have hzero := a.property
    change (Rep.ofAlgebraAutOnUnits K M).ρ g a.val - a.val = 0 at hzero
    exact sub_eq_zero.mp hzero
  have hfixed : ∀ σ : Gal(M/K), (Rep.ofAlgebraAutOnUnits K M).ρ σ a.val = a.val :=
    (Representation.mem_invariants_iff_of_forall_mem_zpowers
      (Rep.ofAlgebraAutOnUnits K M).ρ g hg a.val).mpr hag
  obtain ⟨b, hb⟩ := exists_baseUnit_of_fixed K M a.val hfixed
  let a₀ : LinearMap.ker
      (Rep.applyAsHom (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) g - 𝟙 _).hom.toLinearMap :=
    ⟨b, by
      change b - b = 0
      exact sub_self b⟩
  have hcarry : groupCohomology.mapCocycles₂ (MonoidHom.id Gal(M/K))
      (finiteGaloisBaseUnitsRepHom K M)
      (finiteCyclicCarryTwoCocycle (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) g hg a₀) =
      finiteCyclicCarryTwoCocycle (Rep.ofAlgebraAutOnUnits K M) g hg a := by
    apply Subtype.ext
    funext st
    change (finiteGaloisBaseUnitsRepHom K M).hom (finiteCyclicCarry g hg st.1 st.2 • b) =
      finiteCyclicCarry g hg st.1 st.2 • a.val
    rw [map_nsmul, hb]
  refine ⟨groupCohomology.H2π (Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
    (finiteCyclicCarryTwoCocycle (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) g hg a₀), ?_⟩
  change groupCohomology.map (MonoidHom.id Gal(M/K)) (finiteGaloisBaseUnitsRepHom K M) 2
    (groupCohomology.H2π (Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
      (finiteCyclicCarryTwoCocycle (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) g hg a₀)) = x
  rw [groupCohomology.H2π_comp_map_apply, hcarry, H2π_finiteCyclicCarryTwoCocycle]
  exact ha

end
end ClassFieldTower.Cohomology
