import GaloisCohomology.ProP.ContinuousH1Bridge
import Mathlib.Tactic.Ring

set_option autoImplicit false
/-!
# The continuous cup product of two trivial mod-p characters

For continuous additive `ZMod p`-characters, the canonical homogeneous
representatives give the degree-two cochain

`(g, h, k) ↦ χ(g⁻¹h) * ψ(h⁻¹k)`.

This file constructs that cochain directly and proves its cocycle equation.
No choice of cocycle representatives is involved.
-/

open CategoryTheory TopRep ContRepresentation
open ClassFieldTower.ProP
open scoped Topology

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance continuousH1CupContinuousSMulULiftZMod :
    ContinuousSMul (ZMod p) (ULift.{u} (ZMod p)) :=
  ContinuousSMul.induced ULift.moduleEquiv.toLinearMap

local instance continuousH1CupModule :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) :=
  continuousH1ZModModule

/-- The homogeneous degree-two cochain underlying the cup of two canonical
continuous degree-one character cocycles. -/
def continuousH1CupHomogeneousTwoCochainLifted
    (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    (trivialZModPCochainsLifted p G).X 2 := by
  let σ0 : C((G × G) × G, ULift.{u} (ZMod p)) :=
    ⟨fun x ↦ ULift.up
        (χ (Additive.ofMul (x.1.1⁻¹ * x.1.2)) *
          ψ (Additive.ofMul (x.1.2⁻¹ * x.2))),
      ((ContinuousLinearEquiv.ulift :
        ULift.{u} (ZMod p) ≃L[ZMod p] ZMod p).symm.continuous).comp <|
        (χ.continuous_toFun.comp (by
          change Continuous (fun x : (G × G) × G ↦ x.1.1⁻¹ * x.1.2)
          fun_prop)).mul
          (ψ.continuous_toFun.comp (by
            change Continuous (fun x : (G × G) × G ↦ x.1.2⁻¹ * x.2)
            fun_prop))⟩
  let σ : C(G, C(G, C(G, ULift.{u} (ZMod p)))) :=
    ContinuousMap.curry (ContinuousMap.curry σ0)
  exact ⟨σ, by
    intro a
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro h
    apply ContinuousMap.ext
    intro k
    apply ULift.ext
    change
      χ (Additive.ofMul ((a⁻¹ * g)⁻¹ * (a⁻¹ * h))) *
          ψ (Additive.ofMul ((a⁻¹ * h)⁻¹ * (a⁻¹ * k))) =
        χ (Additive.ofMul (g⁻¹ * h)) *
          ψ (Additive.ofMul (h⁻¹ * k))
    congr 1 <;> congr 2 <;> group⟩

@[simp]
theorem continuousH1CupHomogeneousTwoCochainLifted_apply
    (χ ψ : ContinuousH1ZMod (p := p) (G := G)) (g h k : G) :
    (continuousH1CupHomogeneousTwoCochainLifted χ ψ).1 g h k =
      ULift.up
        (χ (Additive.ofMul (g⁻¹ * h)) *
          ψ (Additive.ofMul (h⁻¹ * k))) :=
  rfl

/-- The canonical degree-two cup cochain satisfies the homogeneous cocycle
equation. -/
theorem continuousH1CupHomogeneousTwoCochainLifted_mem_cycles
    (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    ((trivialZModPCochainsLifted p G).d 2 3).hom
        (continuousH1CupHomogeneousTwoCochainLifted χ ψ) = 0 := by
  change _ =
    (0 : (TopRep.resolutionX (trivialZModPLifted p G) 4).ρ.invariants)
  apply Subtype.ext
  ext g h k l
  have hd := TopRep.homogeneousCochains.d_apply
    (trivialZModPLifted p G) 2
      (continuousH1CupHomogeneousTwoCochainLifted χ ψ)
  have hdh := congrArg (fun τ ↦ τ g h k l) hd
  rw [hdh]
  simp [TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun]
  change
    ULift.up
          (χ (Additive.ofMul (h⁻¹ * k)) *
            ψ (Additive.ofMul (k⁻¹ * l))) -
        (ULift.up
            (χ (Additive.ofMul (g⁻¹ * k)) *
              ψ (Additive.ofMul (k⁻¹ * l))) -
          (ULift.up
              (χ (Additive.ofMul (g⁻¹ * h)) *
                ψ (Additive.ofMul (h⁻¹ * l))) -
            ULift.up
              (χ (Additive.ofMul (g⁻¹ * h)) *
                ψ (Additive.ofMul (h⁻¹ * k))))) = 0
  apply ULift.ext
  change
    χ (Additive.ofMul (h⁻¹ * k)) * ψ (Additive.ofMul (k⁻¹ * l)) -
        (χ (Additive.ofMul (g⁻¹ * k)) * ψ (Additive.ofMul (k⁻¹ * l)) -
          (χ (Additive.ofMul (g⁻¹ * h)) * ψ (Additive.ofMul (h⁻¹ * l)) -
            χ (Additive.ofMul (g⁻¹ * h)) *
              ψ (Additive.ofMul (h⁻¹ * k)))) = 0
  have hχ := χ.map_add
    (Additive.ofMul (g⁻¹ * h)) (Additive.ofMul (h⁻¹ * k))
  change χ (Additive.ofMul ((g⁻¹ * h) * (h⁻¹ * k))) =
    χ (Additive.ofMul (g⁻¹ * h)) +
      χ (Additive.ofMul (h⁻¹ * k)) at hχ
  rw [show (g⁻¹ * h) * (h⁻¹ * k) = g⁻¹ * k by group] at hχ
  have hψ := ψ.map_add
    (Additive.ofMul (h⁻¹ * k)) (Additive.ofMul (k⁻¹ * l))
  change ψ (Additive.ofMul ((h⁻¹ * k) * (k⁻¹ * l))) =
    ψ (Additive.ofMul (h⁻¹ * k)) +
      ψ (Additive.ofMul (k⁻¹ * l)) at hψ
  rw [show (h⁻¹ * k) * (k⁻¹ * l) = h⁻¹ * l by group] at hψ
  rw [hχ, hψ]
  ring

theorem continuousH1CupHomogeneousTwoCochainLifted_add_left
    (χ χ' ψ : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupHomogeneousTwoCochainLifted (χ + χ') ψ =
      continuousH1CupHomogeneousTwoCochainLifted χ ψ +
        continuousH1CupHomogeneousTwoCochainLifted χ' ψ := by
  apply Subtype.ext
  ext g h k
  change
    ULift.up
        ((χ (Additive.ofMul (g⁻¹ * h)) + χ' (Additive.ofMul (g⁻¹ * h))) *
          ψ (Additive.ofMul (h⁻¹ * k))) =
      ULift.up
          (χ (Additive.ofMul (g⁻¹ * h)) *
            ψ (Additive.ofMul (h⁻¹ * k))) +
        ULift.up
          (χ' (Additive.ofMul (g⁻¹ * h)) *
            ψ (Additive.ofMul (h⁻¹ * k)))
  apply ULift.ext
  change
    (χ (Additive.ofMul (g⁻¹ * h)) + χ' (Additive.ofMul (g⁻¹ * h))) *
        ψ (Additive.ofMul (h⁻¹ * k)) =
      χ (Additive.ofMul (g⁻¹ * h)) * ψ (Additive.ofMul (h⁻¹ * k)) +
        χ' (Additive.ofMul (g⁻¹ * h)) * ψ (Additive.ofMul (h⁻¹ * k))
  ring

theorem continuousH1CupHomogeneousTwoCochainLifted_add_right
    (χ ψ ψ' : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupHomogeneousTwoCochainLifted χ (ψ + ψ') =
      continuousH1CupHomogeneousTwoCochainLifted χ ψ +
        continuousH1CupHomogeneousTwoCochainLifted χ ψ' := by
  apply Subtype.ext
  ext g h k
  change
    ULift.up
        (χ (Additive.ofMul (g⁻¹ * h)) *
          (ψ (Additive.ofMul (h⁻¹ * k)) + ψ' (Additive.ofMul (h⁻¹ * k)))) =
      ULift.up
          (χ (Additive.ofMul (g⁻¹ * h)) *
            ψ (Additive.ofMul (h⁻¹ * k))) +
        ULift.up
          (χ (Additive.ofMul (g⁻¹ * h)) *
            ψ' (Additive.ofMul (h⁻¹ * k)))
  apply ULift.ext
  change
    χ (Additive.ofMul (g⁻¹ * h)) *
        (ψ (Additive.ofMul (h⁻¹ * k)) + ψ' (Additive.ofMul (h⁻¹ * k))) =
      χ (Additive.ofMul (g⁻¹ * h)) * ψ (Additive.ofMul (h⁻¹ * k)) +
        χ (Additive.ofMul (g⁻¹ * h)) * ψ' (Additive.ofMul (h⁻¹ * k))
  ring

theorem continuousH1CupHomogeneousTwoCochainLifted_smul_left
    (a : ZMod p) (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupHomogeneousTwoCochainLifted (a • χ) ψ =
      a • continuousH1CupHomogeneousTwoCochainLifted χ ψ := by
  apply Subtype.ext
  ext g h k
  change
    ULift.up
        ((a • χ) (Additive.ofMul (g⁻¹ * h)) *
          ψ (Additive.ofMul (h⁻¹ * k))) =
      a • ULift.up
        (χ (Additive.ofMul (g⁻¹ * h)) *
          ψ (Additive.ofMul (h⁻¹ * k)))
  apply ULift.ext
  change
    (a • χ) (Additive.ofMul (g⁻¹ * h)) * ψ (Additive.ofMul (h⁻¹ * k)) =
      a * (χ (Additive.ofMul (g⁻¹ * h)) * ψ (Additive.ofMul (h⁻¹ * k)))
  let ev : ContinuousH1ZMod (p := p) (G := G) →+ ZMod p :=
    { toFun := fun η ↦ η (Additive.ofMul (g⁻¹ * h))
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hev := ZMod.map_smul ev a χ
  change (a • χ) (Additive.ofMul (g⁻¹ * h)) =
    a * χ (Additive.ofMul (g⁻¹ * h)) at hev
  rw [hev]
  ring

theorem continuousH1CupHomogeneousTwoCochainLifted_smul_right
    (a : ZMod p) (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupHomogeneousTwoCochainLifted χ (a • ψ) =
      a • continuousH1CupHomogeneousTwoCochainLifted χ ψ := by
  apply Subtype.ext
  ext g h k
  change
    ULift.up
        (χ (Additive.ofMul (g⁻¹ * h)) *
          (a • ψ) (Additive.ofMul (h⁻¹ * k))) =
      a • ULift.up
        (χ (Additive.ofMul (g⁻¹ * h)) *
          ψ (Additive.ofMul (h⁻¹ * k)))
  apply ULift.ext
  change
    χ (Additive.ofMul (g⁻¹ * h)) * (a • ψ) (Additive.ofMul (h⁻¹ * k)) =
      a * (χ (Additive.ofMul (g⁻¹ * h)) * ψ (Additive.ofMul (h⁻¹ * k)))
  let ev : ContinuousH1ZMod (p := p) (G := G) →+ ZMod p :=
    { toFun := fun η ↦ η (Additive.ofMul (h⁻¹ * k))
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hev := ZMod.map_smul ev a ψ
  change (a • ψ) (Additive.ofMul (h⁻¹ * k)) =
    a * ψ (Additive.ofMul (h⁻¹ * k)) at hev
  rw [hev]
  ring

end

end ClassFieldTower.Cohomology
