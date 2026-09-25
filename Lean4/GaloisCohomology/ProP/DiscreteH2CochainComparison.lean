/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.TrivialZModP
import Mathlib.Tactic.Group

set_option autoImplicit false
/-!
# Homogeneous and inhomogeneous cochains for a discrete group

For a discrete group in the base universe, continuous homogeneous cochains
with lifted trivial mod-`p` coefficients are additively equivalent to the
usual inhomogeneous function cochains.  This file records the equivalences
in degrees one through three.
-/

open CategoryTheory TopRep ContRepresentation

namespace ClassFieldTower.Cohomology

noncomputable section

variable {p : ℕ}
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [DiscreteTopology Q]

omit [DiscreteTopology Q] in
theorem homogeneousOneCochainLifted_leftInvariant
    (c : (trivialZModPCochainsLifted p Q).X 1)
    (a x₀ x₁ : Q) :
    c.1 (a * x₀) (a * x₁) = c.1 x₀ x₁ := by
  have h := congrArg (fun τ ↦ τ (a * x₀) (a * x₁)) (c.2 a)
  have h' : ((TopRep.resolutionX (trivialZModPLifted p Q) 0).ρ a)
      (c.1 x₀ x₁) = c.1 (a * x₀) (a * x₁) := by
    simpa only [ContRepresentation.coind₁_apply_apply, ← mul_assoc, inv_mul_cancel,
      one_mul] using h
  have htriv : ((TopRep.resolutionX (trivialZModPLifted p Q) 0).ρ a)
      (c.1 x₀ x₁) = c.1 x₀ x₁ := by
    change (trivialZModPLifted p Q).ρ a (c.1 x₀ x₁) = c.1 x₀ x₁
    exact trivialZModPLifted_action p Q a _
  exact h'.symm.trans htriv

omit [DiscreteTopology Q] in
theorem homogeneousTwoCochainLifted_leftInvariant
    (c : (trivialZModPCochainsLifted p Q).X 2)
    (a x₀ x₁ x₂ : Q) :
    c.1 (a * x₀) (a * x₁) (a * x₂) = c.1 x₀ x₁ x₂ := by
  have h := congrArg (fun τ ↦ τ (a * x₀) (a * x₁) (a * x₂)) (c.2 a)
  have h' : ((TopRep.resolutionX (trivialZModPLifted p Q) 0).ρ a)
      (c.1 x₀ x₁ x₂) = c.1 (a * x₀) (a * x₁) (a * x₂) := by
    simpa only [ContRepresentation.coind₁_apply_apply, ← mul_assoc, inv_mul_cancel,
      one_mul] using h
  have htriv : ((TopRep.resolutionX (trivialZModPLifted p Q) 0).ρ a)
      (c.1 x₀ x₁ x₂) = c.1 x₀ x₁ x₂ := by
    change (trivialZModPLifted p Q).ρ a (c.1 x₀ x₁ x₂) = c.1 x₀ x₁ x₂
    exact trivialZModPLifted_action p Q a _
  exact h'.symm.trans htriv

omit [DiscreteTopology Q] in
theorem homogeneousThreeCochainLifted_leftInvariant
    (c : (trivialZModPCochainsLifted p Q).X 3)
    (a x₀ x₁ x₂ x₃ : Q) :
    c.1 (a * x₀) (a * x₁) (a * x₂) (a * x₃) =
      c.1 x₀ x₁ x₂ x₃ := by
  have h :=
    congrArg (fun τ ↦ τ (a * x₀) (a * x₁) (a * x₂) (a * x₃)) (c.2 a)
  have h' : ((TopRep.resolutionX (trivialZModPLifted p Q) 0).ρ a)
      (c.1 x₀ x₁ x₂ x₃) =
        c.1 (a * x₀) (a * x₁) (a * x₂) (a * x₃) := by
    simpa only [ContRepresentation.coind₁_apply_apply, ← mul_assoc, inv_mul_cancel,
      one_mul] using h
  have htriv : ((TopRep.resolutionX (trivialZModPLifted p Q) 0).ρ a)
      (c.1 x₀ x₁ x₂ x₃) = c.1 x₀ x₁ x₂ x₃ := by
    change (trivialZModPLifted p Q).ρ a (c.1 x₀ x₁ x₂ x₃) =
      c.1 x₀ x₁ x₂ x₃
    exact trivialZModPLifted_action p Q a _
  exact h'.symm.trans htriv

/-- Dehomogenize a homogeneous degree-one cochain. -/
def dehomogenizeOne
    (c : (trivialZModPCochainsLifted p Q).X 1) (g : Q) : ULift (ZMod p) :=
  c.1 1 g

/-- Homogenize an inhomogeneous degree-one cochain. -/
def homogenizeOne (f : Q → ULift (ZMod p)) :
    (trivialZModPCochainsLifted p Q).X 1 := by
  let σ₀ : C(Q × Q, ULift.{0} (ZMod p)) :=
    ⟨fun x ↦ f (x.1⁻¹ * x.2),
      continuous_of_discreteTopology⟩
  let σ : C(Q, C(Q, ULift.{0} (ZMod p))) := ContinuousMap.curry σ₀
  exact ⟨σ, by
    intro a
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro h
    change f ((a⁻¹ * g)⁻¹ * (a⁻¹ * h)) = f (g⁻¹ * h)
    congr 1
    group⟩

@[simp]
theorem homogenizeOne_apply (f : Q → ULift (ZMod p)) (g h : Q) :
    (homogenizeOne f).1 g h = f (g⁻¹ * h) :=
  rfl

/-- Additive equivalence between homogeneous and inhomogeneous degree-one
cochains. -/
noncomputable def homogeneousOneCochainAddEquiv :
    (trivialZModPCochainsLifted p Q).X 1 ≃+ (Q → ULift (ZMod p)) where
  toFun := dehomogenizeOne
  invFun := homogenizeOne
  left_inv := by
    intro c
    apply Subtype.ext
    ext g h
    change c.1 1 (g⁻¹ * h) = c.1 g h
    have hinv := homogeneousOneCochainLifted_leftInvariant c g⁻¹ g h
    simp only [inv_mul_cancel] at hinv
    change c.1 1 (g⁻¹ * h) = c.1 g h at hinv
    exact hinv
  right_inv := by
    intro f
    funext g
    change f (1⁻¹ * g) = f g
    simp
  map_add' := by
    intro c d
    funext g
    rfl

/-- Dehomogenize a homogeneous degree-two cochain. -/
def dehomogenizeTwo
    (c : (trivialZModPCochainsLifted p Q).X 2)
    (gh : Q × Q) : ULift (ZMod p) :=
  c.1 1 gh.1 (gh.1 * gh.2)

/-- Homogenize an inhomogeneous degree-two cochain. -/
def homogenizeTwo (f : Q × Q → ULift (ZMod p)) :
    (trivialZModPCochainsLifted p Q).X 2 := by
  let σ₀ : C((Q × Q) × Q, ULift.{0} (ZMod p)) :=
    ⟨fun x ↦ f (x.1.1⁻¹ * x.1.2, x.1.2⁻¹ * x.2),
      continuous_of_discreteTopology⟩
  let σ : C(Q, C(Q, C(Q, ULift.{0} (ZMod p)))) :=
    ContinuousMap.curry (ContinuousMap.curry σ₀)
  exact ⟨σ, by
    intro a
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro h
    apply ContinuousMap.ext
    intro k
    change
      f ((a⁻¹ * g)⁻¹ * (a⁻¹ * h), (a⁻¹ * h)⁻¹ * (a⁻¹ * k)) =
        f (g⁻¹ * h, h⁻¹ * k)
    apply congrArg f
    apply Prod.ext
    · group
    · group⟩

@[simp]
theorem homogenizeTwo_apply
    (f : Q × Q → ULift (ZMod p)) (g h k : Q) :
    (homogenizeTwo f).1 g h k = f (g⁻¹ * h, h⁻¹ * k) :=
  rfl

/-- Additive equivalence between homogeneous and inhomogeneous degree-two
cochains. -/
noncomputable def homogeneousTwoCochainAddEquiv :
    (trivialZModPCochainsLifted p Q).X 2 ≃+ (Q × Q → ULift (ZMod p)) where
  toFun := dehomogenizeTwo
  invFun := homogenizeTwo
  left_inv := by
    intro c
    apply Subtype.ext
    ext g h k
    change
      c.1 1 (g⁻¹ * h)
            ((g⁻¹ * h) * (h⁻¹ * k)) =
        c.1 g h k
    rw [show (g⁻¹ * h) * (h⁻¹ * k) = g⁻¹ * k by group]
    have hinv := homogeneousTwoCochainLifted_leftInvariant c g⁻¹ g h k
    simp only [inv_mul_cancel] at hinv
    change c.1 1 (g⁻¹ * h) (g⁻¹ * k) = c.1 g h k at hinv
    exact hinv
  right_inv := by
    intro f
    funext gh
    change
      f (1⁻¹ * gh.1, gh.1⁻¹ * (gh.1 * gh.2)) = f gh
    simp
  map_add' := by
    intro c d
    funext gh
    rfl

/-- Dehomogenize a homogeneous degree-three cochain. -/
def dehomogenizeThree
    (c : (trivialZModPCochainsLifted p Q).X 3)
    (ghk : Q × Q × Q) : ULift (ZMod p) :=
  (c.1 1 ghk.1 (ghk.1 * ghk.2.1)
    (ghk.1 * ghk.2.1 * ghk.2.2))

/-- Homogenize an inhomogeneous degree-three cochain. -/
def homogenizeThree (f : Q × Q × Q → ULift (ZMod p)) :
    (trivialZModPCochainsLifted p Q).X 3 := by
  let σ₀ : C(((Q × Q) × Q) × Q, ULift.{0} (ZMod p)) :=
    ⟨fun x ↦ f (x.1.1.1⁻¹ * x.1.1.2,
          x.1.1.2⁻¹ * x.1.2, x.1.2⁻¹ * x.2),
      continuous_of_discreteTopology⟩
  let σ :
      C(Q, C(Q, C(Q, C(Q, ULift.{0} (ZMod p))))) :=
    ContinuousMap.curry
      (ContinuousMap.curry (ContinuousMap.curry σ₀))
  exact ⟨σ, by
    intro a
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro h
    apply ContinuousMap.ext
    intro k
    apply ContinuousMap.ext
    intro l
    change
      f ((a⁻¹ * g)⁻¹ * (a⁻¹ * h),
          (a⁻¹ * h)⁻¹ * (a⁻¹ * k),
          (a⁻¹ * k)⁻¹ * (a⁻¹ * l)) =
        f (g⁻¹ * h, h⁻¹ * k, k⁻¹ * l)
    apply congrArg f
    apply Prod.ext
    · group
    · apply Prod.ext
      · group
      · group⟩

@[simp]
theorem homogenizeThree_apply
    (f : Q × Q × Q → ULift (ZMod p)) (g h k l : Q) :
    (homogenizeThree f).1 g h k l =
      f (g⁻¹ * h, h⁻¹ * k, k⁻¹ * l) :=
  rfl

/-- Additive equivalence between homogeneous and inhomogeneous degree-three
cochains. -/
noncomputable def homogeneousThreeCochainAddEquiv :
    (trivialZModPCochainsLifted p Q).X 3 ≃+
      (Q × Q × Q → ULift (ZMod p)) where
  toFun := dehomogenizeThree
  invFun := homogenizeThree
  left_inv := by
    intro c
    apply Subtype.ext
    ext g h k l
    change
      c.1 1 (g⁻¹ * h)
            ((g⁻¹ * h) * (h⁻¹ * k))
            ((g⁻¹ * h) * (h⁻¹ * k) * (k⁻¹ * l)) =
        c.1 g h k l
    rw [show (g⁻¹ * h) * (h⁻¹ * k) = g⁻¹ * k by group]
    rw [show g⁻¹ * k * (k⁻¹ * l) = g⁻¹ * l by group]
    have hinv := homogeneousThreeCochainLifted_leftInvariant c g⁻¹ g h k l
    simp only [inv_mul_cancel] at hinv
    change
      c.1 1 (g⁻¹ * h) (g⁻¹ * k) (g⁻¹ * l) =
        c.1 g h k l at hinv
    exact hinv
  right_inv := by
    intro f
    funext ghk
    change
      f (1⁻¹ * ghk.1,
          ghk.1⁻¹ * (ghk.1 * ghk.2.1),
          (ghk.1 * ghk.2.1)⁻¹ *
            (ghk.1 * ghk.2.1 * ghk.2.2)) = f ghk
    apply congrArg f
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · group
  map_add' := by
    intro c d
    funext ghk
    rfl

end

end ClassFieldTower.Cohomology
