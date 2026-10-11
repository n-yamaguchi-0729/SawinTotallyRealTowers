/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.ContinuousH1CupProduct

/-!
# Restriction naturality of the continuous H¹ cup product

The canonical character representatives commute with pullback along a
continuous group homomorphism.  Consequently their degree-two cup cocycle
and cohomology class commute with continuous-cohomology restriction.
-/

open CategoryTheory TopRep
open ClassFieldTower.ProP

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ}
variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

local instance continuousH1CupRestrictionModule
    {J : Type u} [Group J] [TopologicalSpace J] [IsTopologicalGroup J] :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := J)) :=
  continuousH1ZModModule

/-- Pullback of continuous additive mod-`p` characters along a continuous
group homomorphism. -/
noncomputable def continuousH1ZModRestriction (f : H →ₜ* G) :
    ContinuousH1ZMod (p := p) (G := G) →ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := H) := by
  let r : ContinuousH1ZMod (p := p) (G := G) →+
      ContinuousH1ZMod (p := p) (G := H) :=
    { toFun := fun χ ↦
        { toFun := fun h ↦ χ (Additive.ofMul (f (Additive.toMul h)))
          map_zero' := by
            change χ (Additive.ofMul (f 1)) = 0
            rw [map_one]
            exact χ.map_zero
          map_add' := by
            intro h k
            change χ (Additive.ofMul (f (Additive.toMul h * Additive.toMul k))) =
              χ (Additive.ofMul (f (Additive.toMul h))) +
                χ (Additive.ofMul (f (Additive.toMul k)))
            rw [map_mul]
            exact χ.map_add _ _
          continuous_toFun := χ.continuous_toFun.comp f.continuous_toFun }
      map_zero' := by ext h; rfl
      map_add' := by intro χ ψ; ext h; rfl }
  exact { r with map_smul' := ZMod.map_smul r }

@[simp]
theorem continuousH1ZModRestriction_apply
    (f : H →ₜ* G) (χ : ContinuousH1ZMod (p := p) (G := G)) (h : Additive H) :
    continuousH1ZModRestriction f χ h =
      χ (Additive.ofMul (f (Additive.toMul h))) :=
  rfl

/-- Pullback of the explicit cup cochain is the cup cochain of the pulled-back
characters. -/
theorem trivialZModPCochainsMapLifted_continuousH1Cup
    (f : H →ₜ* G)
    (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    (((trivialZModPCochainsMapLifted p f).f 2).hom
        (continuousH1CupHomogeneousTwoCochainLifted χ ψ)) =
      continuousH1CupHomogeneousTwoCochainLifted
        (continuousH1ZModRestriction f χ)
        (continuousH1ZModRestriction f ψ) := by
  apply Subtype.ext
  ext g h k
  change
    ULift.up
        (χ (Additive.ofMul ((f g)⁻¹ * f h)) *
          ψ (Additive.ofMul ((f h)⁻¹ * f k))) =
      ULift.up
        (χ (Additive.ofMul (f (g⁻¹ * h))) *
          ψ (Additive.ofMul (f (h⁻¹ * k))))
  have hgh : (f g)⁻¹ * f h = f (g⁻¹ * h) := by
    rw [map_mul, map_inv]
  have hhk : (f h)⁻¹ * f k = f (h⁻¹ * k) := by
    rw [map_mul, map_inv]
  rw [hgh, hhk]

/-- Restriction of the explicit cup cocycle is the cup cocycle of the
restricted characters. -/
theorem trivialZModPCocyclesMapLifted_continuousH1Cup
    (f : H →ₜ* G)
    (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    trivialZModPCocyclesMapLifted p f 2
        (continuousH1CupHomogeneousTwoCocycleLifted χ ψ) =
      continuousH1CupHomogeneousTwoCocycleLifted
        (continuousH1ZModRestriction f χ)
        (continuousH1ZModRestriction f ψ) := by
  apply topModule_mono_injective_lifted
    ((trivialZModPCochainsLifted p H).iCycles 2)
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
  rw [ConcreteCategory.comp_apply]
  rw [iCycles_continuousH1CupHomogeneousTwoCocycleLifted]
  change
    (((trivialZModPCochainsMapLifted p f).f 2).hom
        (continuousH1CupHomogeneousTwoCochainLifted χ ψ)) =
      (trivialZModPCochainsLifted p H).iCycles 2
        (continuousH1CupHomogeneousTwoCocycleLifted
          (continuousH1ZModRestriction f χ)
          (continuousH1ZModRestriction f ψ))
  rw [trivialZModPCochainsMapLifted_continuousH1Cup,
    iCycles_continuousH1CupHomogeneousTwoCocycleLifted]

/-- The continuous `H¹ × H¹ → H²` cup product commutes with restriction. -/
theorem continuousCohomologyZModPMapLifted_continuousH1Cup
    (f : H →ₜ* G)
    (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    (continuousCohomologyZModPMapLifted p f 2).hom
        (continuousH1CupProductLifted χ ψ) =
      continuousH1CupProductLifted
        (continuousH1ZModRestriction f χ)
        (continuousH1ZModRestriction f ψ) := by
  change
    (continuousCohomologyZModPMapLifted p f 2).hom
        (ContinuousCohomology.π (trivialZModPLifted p G) 2
          (continuousH1CupHomogeneousTwoCocycleLifted χ ψ)) =
      ContinuousCohomology.π (trivialZModPLifted p H) 2
        (continuousH1CupHomogeneousTwoCocycleLifted
          (continuousH1ZModRestriction f χ)
          (continuousH1ZModRestriction f ψ))
  rw [← ConcreteCategory.comp_apply, trivialZModPLifted_π_naturality,
    ConcreteCategory.comp_apply,
    trivialZModPCocyclesMapLifted_continuousH1Cup]

end

end ClassFieldTower.Cohomology
