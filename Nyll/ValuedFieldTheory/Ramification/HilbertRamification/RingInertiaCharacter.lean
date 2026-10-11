/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Action.End
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Group.Units.Hom

/-!
# The inertia character directly on a DVR

This owner starts from the actual ideal inertia of a group acting on a DVR.
It constructs the uniformizer-ratio unit inside the ring and then reduces it.
No ambient fraction field, scalar tower, chosen value group, or supplied
character is used.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (G : Type v) [Group G] [MulSemiringAction G R]

/-- The actual quotient unit `g(π)/π`, constructed using associated uniformizers. -/
def uniformizerRatioUnit (π : R) (hπ : Irreducible π) (g : G) : Rˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible R hπ
    (hπ.map (MulDistribMulAction.toMulEquiv R g))).choose

theorem uniformizerRatioUnit_spec (π : R) (hπ : Irreducible π) (g : G) :
    π * (uniformizerRatioUnit R G π hπ g : R) = g • π :=
  (IsDiscreteValuationRing.associated_of_irreducible R hπ
    (hπ.map (MulDistribMulAction.toMulEquiv R g))).choose_spec

theorem uniformizerRatioUnit_one (π : R) (hπ : Irreducible π) :
    uniformizerRatioUnit R G π hπ (1 : G) = 1 := by
  apply Units.ext
  apply mul_left_cancel₀ hπ.ne_zero
  rw [uniformizerRatioUnit_spec]
  exact (one_smul G π).trans (mul_one π).symm

/-- The ratio is a cocycle before restriction to inertia. -/
theorem uniformizerRatioUnit_mul (π : R) (hπ : Irreducible π) (g h : G) :
    uniformizerRatioUnit R G π hπ (g * h) =
      uniformizerRatioUnit R G π hπ g *
        Units.map (MulSemiringAction.toRingHom G R g).toMonoidHom
          (uniformizerRatioUnit R G π hπ h) := by
  apply Units.ext
  apply mul_left_cancel₀ hπ.ne_zero
  change π * (uniformizerRatioUnit R G π hπ (g * h) : R) =
    π * ((uniformizerRatioUnit R G π hπ g : R) *
      (g • (uniformizerRatioUnit R G π hπ h : R)))
  rw [uniformizerRatioUnit_spec, mul_smul,
    ← uniformizerRatioUnit_spec R G π hπ h, smul_mul',
    ← uniformizerRatioUnit_spec R G π hπ g, mul_assoc]

/-- A change of uniformizer changes the unit cocycle by the unit coboundary. -/
theorem uniformizerRatioUnit_change (π π' : R)
    (hπ : Irreducible π) (hπ' : Irreducible π')
    (a : Rˣ) (ha : π' = π * (a : R)) (g : G) :
    uniformizerRatioUnit R G π' hπ' g * a =
      uniformizerRatioUnit R G π hπ g *
        Units.map (MulSemiringAction.toRingHom G R g).toMonoidHom a := by
  apply Units.ext
  apply mul_left_cancel₀ hπ.ne_zero
  change π * ((uniformizerRatioUnit R G π' hπ' g : R) * (a : R)) =
    π * ((uniformizerRatioUnit R G π hπ g : R) * (g • (a : R)))
  calc
    _ = (π * (a : R)) * (uniformizerRatioUnit R G π' hπ' g : R) := by
      rw [mul_assoc, mul_comm (a : R)]
    _ = g • π' := by rw [← ha, uniformizerRatioUnit_spec]
    _ = (g • π) * (g • (a : R)) := by rw [ha, smul_mul']
    _ = _ := by rw [← uniformizerRatioUnit_spec R G π hπ g, mul_assoc]

/-- Actual ideal inertia fixes every residue class. -/
theorem inertia_residue_fixed
    (σ : (maximalIdeal R).inertia G) (x : R) :
    residue R ((σ : G) • x) = residue R x := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (residue_eq_zero_iff _).mpr (σ.property x)

/-- The same fixedness on the units of the residue field. -/
theorem inertia_residueUnits_fixed
    (σ : (maximalIdeal R).inertia G) (a : Rˣ) :
    Units.map (residue R).toMonoidHom
        (Units.map (MulSemiringAction.toRingHom G R (σ : G)).toMonoidHom a) =
      Units.map (residue R).toMonoidHom a := by
  apply Units.ext
  exact inertia_residue_fixed R G σ (a : R)

/-- The actual uniformizer character on ideal inertia. -/
def inertiaUniformizerCharacter (π : R) (hπ : Irreducible π) :
    (maximalIdeal R).inertia G →* (ResidueField R)ˣ where
  toFun σ := Units.map (residue R).toMonoidHom
    (uniformizerRatioUnit R G π hπ (σ : G))
  map_one' := by
    rw [Subgroup.coe_one, uniformizerRatioUnit_one, map_one]
  map_mul' σ τ := by
    rw [Subgroup.coe_mul, uniformizerRatioUnit_mul, map_mul,
      inertia_residueUnits_fixed]

/-- The ideal-inertia character is independent of the uniformizer. -/
theorem inertiaUniformizerCharacter_eq
    (π π' : R) (hπ : Irreducible π) (hπ' : Irreducible π') :
    inertiaUniformizerCharacter R G π hπ = inertiaUniformizerCharacter R G π' hπ' := by
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.associated_of_irreducible R hπ hπ'
  apply MonoidHom.ext
  intro σ
  have hc := uniformizerRatioUnit_change R G π π' hπ hπ' a ha.symm (σ : G)
  have hr := congrArg (Units.map (residue R).toMonoidHom) hc
  rw [map_mul, map_mul, inertia_residueUnits_fixed] at hr
  exact (mul_right_cancel hr).symm

/-- The actual uniformizer-independent inertia character of a DVR action. -/
def inertiaResidueCharacter :
    (maximalIdeal R).inertia G →* (ResidueField R)ˣ :=
  inertiaUniformizerCharacter R G
    (IsDiscreteValuationRing.exists_irreducible R).choose
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec

theorem inertiaResidueCharacter_eq_uniformizer (π : R) (hπ : Irreducible π) :
    inertiaResidueCharacter R G = inertiaUniformizerCharacter R G π hπ :=
  inertiaUniformizerCharacter_eq R G
    (IsDiscreteValuationRing.exists_irreducible R).choose π
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec hπ

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end
