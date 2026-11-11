/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.UnitsPrimitiveDescent
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Abel

/-!
# Injectivity of field-unit H² inflation

The map is induced by actual restriction to a normal intermediate field
and inclusion of its units. For a finite Galois upper field, Hilbert 90
corrects an upper primitive by an actual principal one-coboundary. The
corrected primitive is constant on restriction fibres and its values are
fixed by all relative automorphisms, so it descends to the lower field.
-/

@[expose] public section

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable (E : IntermediateField K L) [Normal K E]

/-- The actual inclusion of lower-field units, equivariant for restriction
of the upper Galois group to the normal intermediate field. -/
def finiteGaloisUnitsInflationRepHom :
    Rep.res (AlgEquiv.restrictNormalHom E)
      (Rep.ofAlgebraAutOnUnits K E) ⟶ Rep.ofAlgebraAutOnUnits K L := by
  apply Rep.ofHom
  refine ⟨(unitsInclusion K L E).toIntLinearMap, ?_⟩
  intro σ
  apply LinearMap.ext
  intro a
  exact unitsInclusion_equivariant K L E σ a

/-- Inflation with the actual field-unit coefficient inclusion in a finite
Galois tower. -/
def finiteGaloisUnitsH2Inflation :
    groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 :=
  groupCohomology.map (AlgEquiv.restrictNormalHom E)
    (finiteGaloisUnitsInflationRepHom K L E) 2

/-- Inflation sends an actual two-cocycle class to the class obtained by
restricting its arguments and including its field-unit values. -/
theorem finiteGaloisUnitsH2Inflation_H2π
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K E)) :
    (finiteGaloisUnitsH2Inflation K L E).hom
        (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K E) c) =
      groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
        (groupCohomology.mapCocycles₂ (AlgEquiv.restrictNormalHom E)
          (finiteGaloisUnitsInflationRepHom K L E) c) := by
  exact congrArg (fun f ↦ f c)
    (groupCohomology.H2π_comp_map (AlgEquiv.restrictNormalHom E)
      (finiteGaloisUnitsInflationRepHom K L E))

variable [FiniteDimensional K L] [IsGalois K L]

/-- Inflation on actual field-unit H² is injective in a finite Galois
tower. Noether–Hilbert90 corrects any upper primitive so that it descends
to a lower-field primitive. -/
theorem finiteGaloisUnitsH2Inflation_injective :
    Function.Injective (finiteGaloisUnitsH2Inflation K L E).hom := by
  have hzero : ∀ x : groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2,
      (finiteGaloisUnitsH2Inflation K L E).hom x = 0 → x = 0 := by
    intro x
    induction x using groupCohomology.H2_induction_on with
    | h c =>
      intro hx
      rw [finiteGaloisUnitsH2Inflation_H2π] at hx
      obtain ⟨b, hb⟩ := (groupCohomology.H2π_eq_zero_iff _).mp hx
      have hb' (σ τ : Gal(L/K)) :
          (Rep.ofAlgebraAutOnUnits K L).ρ σ (b τ) - b (σ * τ) + b σ =
            unitsInclusion K L E
              (c (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ)) :=
        congrFun hb (σ, τ)
      obtain ⟨a, ha⟩ := unitsPrimitiveDescends K L E c
        (groupCohomology.cocycles₂_map_one_snd c)
        (groupCohomology.cocycles₂_map_one_fst c) b hb'
      exact (groupCohomology.H2π_eq_zero_iff c).mpr
        ⟨a, funext (fun στ => ha στ.1 στ.2)⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  rw [map_sub, hxy, sub_self]

end
end ClassFieldTower.Cohomology
