/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.FiniteTransgressionLinear
import Nyll.GaloisCohomology.ProP.FreeProPH2Cocycle

/-!
# Exactness of finite transgression

Restriction of an ambient mod-`p` character to a normal subgroup is conjugation invariant.
This file proves the missing converse to the finite transgression kernel theorem: an invariant
character has zero factor-set class exactly when it is such a restriction.
-/

open CategoryTheory TopRep ContRepresentation
open scoped Topology

namespace ClassFieldTower.Cohomology

open ClassFieldTower.ProP.FreeProPH2Cocycle

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {P : Type u} [Group P]

local instance exactQuotientTopology (N : Subgroup P) : TopologicalSpace (P ⧸ N) := ⊥
local instance exactQuotientDiscrete (N : Subgroup P) : DiscreteTopology (P ⧸ N) :=
  discreteTopology_bot _

/-- Restriction of finite ambient characters to invariant subgroup characters. -/
def finiteCharacterRestrictionAddHom (N : Subgroup P) [N.Normal] :
    FiniteCharacter p P →+ InvariantFiniteCharacter (p := p) N where
  toFun ψ := ⟨Additive.ofMul (ψ.toMul.comp N.subtype), by
    intro g n
    change ψ.toMul (g * n.1 * g⁻¹) = ψ.toMul n.1
    simp only [map_mul, map_inv]
    calc
      ψ.toMul g * ψ.toMul n.1 * (ψ.toMul g)⁻¹ =
          ψ.toMul n.1 * (ψ.toMul g * (ψ.toMul g)⁻¹) := by ac_rfl
      _ = ψ.toMul n.1 := by simp⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' ψ φ := by
    apply Subtype.ext
    rfl

/-- Linear restriction from ambient characters to invariant subgroup characters. -/
noncomputable def finiteCharacterRestrictionLinearMap
    (N : Subgroup P) [N.Normal] :
    FiniteCharacter p P →ₗ[ZMod p] InvariantFiniteCharacter (p := p) N :=
  (finiteCharacterRestrictionAddHom N).toZModLinearMap p

omit [Fact p.Prime] in
theorem transgressionFactor_eq_extension_coboundary
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (ψ : MonoidHom P (Multiplicative (ZMod p)))
    (hψ : ψ.comp N.subtype = χ)
    (q r : P ⧸ N) :
    transgressionFactor N χ q r =
      (ψ (Quotient.out q)).toAdd + (ψ (Quotient.out r)).toAdd -
        (ψ (Quotient.out (q * r))).toAdd := by
  have hfactor := DFunLike.congr_fun hψ (quotientSectionFactor N q r)
  change
    ψ ((quotientSectionFactor N q r : N) : P) =
      χ (quotientSectionFactor N q r) at hfactor
  rw [quotientSectionFactor_apply, map_mul, map_mul, map_inv] at hfactor
  have hfactorAdd := congrArg Multiplicative.toAdd hfactor
  change
    (ψ (Quotient.out q) * ψ (Quotient.out r) *
      (ψ (Quotient.out (q * r)))⁻¹).toAdd =
        transgressionFactor N χ q r at hfactorAdd
  simpa only [toAdd_mul, toAdd_inv, sub_eq_add_neg] using hfactorAdd.symm

omit [Fact p.Prime] in
theorem transgressionFactor_one_one_eq_extension_value
    (N : Subgroup P) [N.Normal]
    (χ : MonoidHom N (Multiplicative (ZMod p)))
    (ψ : MonoidHom P (Multiplicative (ZMod p)))
    (hψ : ψ.comp N.subtype = χ) :
    transgressionFactor N χ 1 1 = (ψ (Quotient.out (1 : P ⧸ N))).toAdd := by
  rw [transgressionFactor_eq_extension_coboundary N χ ψ hψ]
  simp

omit [Fact p.Prime] in
/-- An invariant character extending to the ambient group has zero finite transgression. -/
theorem finiteTransgressionLinearMap_eq_zero_of_extendsToAmbient
    (N : Subgroup P) [N.Normal] [Finite (P ⧸ N)]
    (χ : InvariantFiniteCharacter (p := p) N)
    (hχ : InvariantFiniteCharacter.ExtendsToAmbient N χ) :
    finiteTransgressionLinearMap N χ = 0 := by
  obtain ⟨ψ, hψ⟩ := hχ
  let z := transgressionHomogeneousCocycle N
    (InvariantFiniteCharacter.toMonoidHom N χ)
    (InvariantFiniteCharacter.isInvariant N χ)
  let s : P ⧸ N → ZMod p := fun q ↦ (ψ (Quotient.out q)).toAdd
  let b : C(P ⧸ N, ULift.{u} (ZMod p)) :=
    ⟨fun q ↦ ULift.up (-s q + s 1), continuous_of_discreteTopology⟩
  have hnormalized (q r : P ⧸ N) :
      normalizedCocycle z q r = ULift.up
        (transgressionFactor N
          (InvariantFiniteCharacter.toMonoidHom N χ) q r -
            transgressionFactor N
              (InvariantFiniteCharacter.toMonoidHom N χ) 1 1) := by
    unfold normalizedCocycle
    change
      (((trivialZModPCochainsLifted p (P ⧸ N)).iCycles 2).hom z).1
          1 q (q * r) -
        (((trivialZModPCochainsLifted p (P ⧸ N)).iCycles 2).hom z).1
          1 1 1 = _
    rw [show ((trivialZModPCochainsLifted p (P ⧸ N)).iCycles 2).hom z =
        transgressionHomogeneousCochain N
          (InvariantFiniteCharacter.toMonoidHom N χ) by
      exact iCycles_transgressionHomogeneousCocycle N
        (InvariantFiniteCharacter.toMonoidHom N χ)
        (InvariantFiniteCharacter.isInvariant N χ)]
    change ULift.up (transgressionFactor N
        (InvariantFiniteCharacter.toMonoidHom N χ) (1⁻¹ * q) (q⁻¹ * (q * r))) -
      ULift.up (transgressionFactor N
        (InvariantFiniteCharacter.toMonoidHom N χ) (1⁻¹ * 1) (1⁻¹ * 1)) = _
    simp only [inv_one, one_mul, inv_mul_cancel_left]
    rfl
  have hb : ∀ q r : P ⧸ N,
      b (q * r) = b q + b r + normalizedCocycle z q r := by
    intro q r
    rw [hnormalized]
    apply ULift.ext
    change -s (q * r) + s 1 =
      (-s q + s 1) + (-s r + s 1) +
        (transgressionFactor N
          (InvariantFiniteCharacter.toMonoidHom N χ) q r -
            transgressionFactor N
              (InvariantFiniteCharacter.toMonoidHom N χ) 1 1)
    rw [transgressionFactor_eq_extension_coboundary N
        (InvariantFiniteCharacter.toMonoidHom N χ) ψ hψ,
      transgressionFactor_one_one_eq_extension_value N
        (InvariantFiniteCharacter.toMonoidHom N χ) ψ hψ]
    dsimp only [s]
    abel
  let K := trivialZModPCochainsLifted p (P ⧸ N)
  let c : K.X 1 := homogeneousPrimitive z b
  have hc : (K.d 1 2).hom c = (K.iCycles 2).hom z :=
    homogeneousPrimitive_boundary z b hb
  have hzc : (K.toCycles 1 2).hom c = z := by
    apply topModule_mono_injective_lifted (K.iCycles 2)
    calc
      (K.iCycles 2).hom ((K.toCycles 1 2).hom c) = (K.d 1 2).hom c := by
        exact ConcreteCategory.congr_hom (K.toCycles_i 1 2) c
      _ = (K.iCycles 2).hom z := hc
  change ContinuousCohomology.π (trivialZModPLifted p (P ⧸ N)) 2 z = 0
  rw [← hzc]
  exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ 1 2) c

omit [Fact p.Prime] in
/-- Exact kernel statement for finite transgression. -/
theorem finiteCharacterRestriction_range_eq_transgression_ker
    (N : Subgroup P) [N.Normal] [Finite (P ⧸ N)] :
    LinearMap.range (finiteCharacterRestrictionLinearMap (p := p) N) =
      LinearMap.ker (finiteTransgressionLinearMap (p := p) N) := by
  ext χ
  constructor
  · rintro ⟨ψ, rfl⟩
    rw [LinearMap.mem_ker]
    apply finiteTransgressionLinearMap_eq_zero_of_extendsToAmbient N
    exact ⟨ψ.toMul, rfl⟩
  · intro hχ
    rw [LinearMap.mem_ker] at hχ
    obtain ⟨ψ, hψ⟩ :=
      InvariantFiniteCharacter.extendsToAmbient_of_transgression_eq_zero N χ hχ
    refine ⟨Additive.ofMul ψ, ?_⟩
    apply Subtype.ext
    exact hψ

end

end ClassFieldTower.Cohomology
