/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Tactic.Group

/-!
# Normalized degree-two cocycles with trivial continuous coefficients

These coefficient-ring-independent formulas share the normalization and
primitive construction between finite-field and integral coefficients.
-/

open scoped Topology
open CategoryTheory TopRep ContRepresentation

namespace TopRep.TrivialDegreeTwoCocycles

noncomputable section
universe u v
variable {R : Type v} [Ring R] [TopologicalSpace R]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable (X : TopRep.{u} R F)
variable (hX : ∀ (g : F) (x : X), X.ρ g x = x)

private def cocycleValue
    (z : ContinuousCohomology.cocycles X 2)
    (x₀ x₁ x₂ : F) : X :=
  (((homogeneousCochains X).iCycles 2).hom z).1 x₀ x₁ x₂

/-- The normalized inhomogeneous cocycle associated to a homogeneous
degree-two cocycle. -/
def normalizedCocycle
    (z : ContinuousCohomology.cocycles X 2) (g h : F) : X :=
  cocycleValue X z 1 g (g * h) - cocycleValue X z 1 1 1

/-- The normalized inhomogeneous cocycle is continuous. -/
theorem normalizedCocycle_continuous
    [LocallyCompactSpace F]
    (z : ContinuousCohomology.cocycles X 2) :
    Continuous fun gh : F × F => normalizedCocycle X z gh.1 gh.2 := by
  let z₀ := ((homogeneousCochains X).iCycles 2).hom z
  change (TopRep.resolutionX X 3).ρ.invariants at z₀
  let zfun : C(F, C(F, C(F, X))) := z₀.1
  change Continuous fun gh : F × F => zfun 1 gh.1 (gh.1 * gh.2) - zfun 1 1 1
  fun_prop

private theorem homogeneousCocycle_leftInvariant
    (hX : ∀ (g : F) (x : X), X.ρ g x = x)
    (z : ContinuousCohomology.cocycles X 2)
    (g x₀ x₁ x₂ : F) :
    (((homogeneousCochains X).iCycles 2).hom z).1
        (g * x₀) (g * x₁) (g * x₂) =
      (((homogeneousCochains X).iCycles 2).hom z).1
        x₀ x₁ x₂ := by
  have h := ContinuousCohomology.degreeTwo_equivariant X z g x₀ x₁ x₂
  rw [hX] at h
  exact h.symm

/-- Normalization preserves the inhomogeneous cocycle equation. -/
theorem normalizedCocycle_cocycle
    (hX : ∀ (g : F) (x : X), X.ρ g x = x)
    (z : ContinuousCohomology.cocycles X 2)
    (g h k : F) :
    normalizedCocycle X z g h + normalizedCocycle X z (g * h) k =
      normalizedCocycle X z h k + normalizedCocycle X z g (h * k) := by
  have hz := ContinuousCohomology.degreeTwo_cocycle_equation X z 1 g (g * h) (g * h * k)
  have hinv := homogeneousCocycle_leftInvariant X hX z g 1 h (h * k)
  simp only [mul_one, mul_assoc] at hz hinv
  rw [hinv] at hz
  let q (x y w : F) : X :=
    (((homogeneousCochains X).iCycles 2).hom z).1 x y w
  let a := q 1 h (h * k)
  let b := q 1 (g * h) (g * (h * k))
  let c := q 1 g (g * (h * k))
  let d := q 1 g (g * h)
  let t := q 1 1 1
  change a - b + c - d = 0 at hz
  have hraw : d + b = a + c := by
    have hzero : d + b - (a + c) = 0 := by
      calc
        d + b - (a + c) = -(a - b + c - d) := by abel
        _ = 0 := by rw [hz, neg_zero]
    exact sub_eq_zero.mp hzero
  unfold normalizedCocycle
  simp only [mul_assoc]
  change (d - t) + (b - t) = (a - t) + (c - t)
  calc
    (d - t) + (b - t) = (d + b) - (t + t) := by abel
    _ = (a + c) - (t + t) := by rw [hraw]
    _ = (a - t) + (c - t) := by abel

/-- The normalized cocycle vanishes when its first argument is one. -/
theorem normalizedCocycle_one_left
    (z : ContinuousCohomology.cocycles X 2) (h : F) :
    normalizedCocycle X z 1 h = 0 := by
  have hz := ContinuousCohomology.degreeTwo_cocycle_equation X z 1 1 1 h
  simp only at hz
  unfold normalizedCocycle
  simp only [one_mul]
  abel_nf at hz ⊢
  exact hz

/-- The normalized cocycle vanishes when its second argument is one. -/
theorem normalizedCocycle_one_right
    (hX : ∀ (g : F) (x : X), X.ρ g x = x)
    (z : ContinuousCohomology.cocycles X 2) (g : F) :
    normalizedCocycle X z g 1 = 0 := by
  have hc := normalizedCocycle_cocycle X hX z g 1 1
  rw [one_mul, mul_one, normalizedCocycle_one_left] at hc
  have hc' : normalizedCocycle X z g 1 + normalizedCocycle X z g 1 =
      normalizedCocycle X z g 1 + 0 := by simpa only [zero_add, add_zero] using hc
  exact add_left_cancel hc'

private theorem homogeneousCocycle_eq_normalized
    (hX : ∀ (g : F) (x : X), X.ρ g x = x)
    (z : ContinuousCohomology.cocycles X 2)
    (x₀ x₁ x₂ : F) :
    cocycleValue X z x₀ x₁ x₂ = cocycleValue X z 1 1 1 +
        normalizedCocycle X z (x₀⁻¹ * x₁) (x₁⁻¹ * x₂) := by
  have hinv := homogeneousCocycle_leftInvariant X hX z x₀⁻¹ x₀ x₁ x₂
  have h02 : (x₀⁻¹ * x₁) * (x₁⁻¹ * x₂) = x₀⁻¹ * x₂ := by group
  simp only [inv_mul_cancel] at hinv
  unfold normalizedCocycle cocycleValue
  rw [h02]
  rw [← hinv]
  abel

/-- The homogeneous degree-one cochain associated to a continuous primitive
of the normalized cocycle. -/
def homogeneousPrimitive
    [LocallyCompactSpace F]
    (z : ContinuousCohomology.cocycles X 2)
    (b : C(F, X)) :
    (homogeneousCochains X).X 1 := by
  let a₀ : X :=
    cocycleValue X z 1 1 1
  let σ : C(F, C(F, X)) := ContinuousMap.curry
    ⟨fun xy : F × F => a₀ - b (xy.1⁻¹ * xy.2),
      continuous_const.sub <| b.continuous_toFun.comp <| by fun_prop⟩
  exact ⟨σ, by
    intro g
    apply ContinuousMap.ext
    intro x
    apply ContinuousMap.ext
    intro y
    change X.ρ g (a₀ - b ((g⁻¹ * x)⁻¹ * (g⁻¹ * y))) = a₀ - b (x⁻¹ * y)
    rw [hX]
    congr 2
    group⟩

@[simp]
private theorem homogeneousPrimitive_apply
    [LocallyCompactSpace F]
    (z : ContinuousCohomology.cocycles X 2)
    (b : C(F, X)) (x y : F) :
    (((homogeneousPrimitive X hX z b).1 : C(F, C(F, X))) x y) =
      cocycleValue X z 1 1 1 - b (x⁻¹ * y) :=
  rfl

/-- A continuous normalized primitive gives an actual homogeneous boundary. -/
theorem homogeneousPrimitive_boundary
    [LocallyCompactSpace F]
    (z : ContinuousCohomology.cocycles X 2)
    (b : C(F, X))
    (hb : ∀ g h, b (g * h) = b g + b h + normalizedCocycle X z g h) :
    ((homogeneousCochains X).d 1 2).hom
        (homogeneousPrimitive X hX z b) =
      ((homogeneousCochains X).iCycles 2).hom z := by
  let C := homogeneousCochains X
  let t : C.X 1 := homogeneousPrimitive X hX z b
  change (C.d 1 2).hom t = (C.iCycles 2).hom z
  apply Subtype.ext
  ext x₀ x₁ x₂
  have hd := TopRep.homogeneousCochains.d_apply X 1 t
  have hdpoint := congrArg (fun τ => τ x₀ x₁ x₂) hd
  rw [hdpoint]
  simp only [Nat.reduceAdd, hom_d_succ, d_zero, hom_ofHom,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun,
    ContinuousMap.sub_apply, ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  rw [homogeneousPrimitive_apply X hX z b x₁ x₂,
    homogeneousPrimitive_apply X hX z b x₀ x₂,
    homogeneousPrimitive_apply X hX z b x₀ x₁]
  change _ = cocycleValue X z x₀ x₁ x₂
  have hprod : (x₀⁻¹ * x₁) * (x₁⁻¹ * x₂) = x₀⁻¹ * x₂ := by group
  have hb' := hb (x₀⁻¹ * x₁) (x₁⁻¹ * x₂)
  rw [hprod] at hb'
  have hcalc :
      (cocycleValue X z 1 1 1 - b (x₁⁻¹ * x₂)) -
          ((cocycleValue X z 1 1 1 - b (x₀⁻¹ * x₂)) -
            (cocycleValue X z 1 1 1 - b (x₀⁻¹ * x₁))) =
        cocycleValue X z 1 1 1 +
          normalizedCocycle X z (x₀⁻¹ * x₁) (x₁⁻¹ * x₂) := by
    rw [hb']
    abel
  rw [homogeneousCocycle_eq_normalized X hX z x₀ x₁ x₂]
  exact hcalc

/-- Actual degree-two continuous cohomology vanishes when every raw
continuous additive two-cocycle has a continuous primitive. -/
theorem continuousH2_eq_zero_of_primitive [LocallyCompactSpace F]
    (hX : ∀ (g : F) (x : X), X.ρ g x = x)
    (hprimitive : ∀ c : C(F × F, X),
      (∀ s t u : F, c (s * t, u) + c (s, t) = c (t, u) + c (s, t * u)) →
      ∃ a : C(F, X), ∀ s t : F, a t + a s - a (s * t) = c (s, t))
    (v : continuousCohomology 2 X) : v = 0 := by
  obtain ⟨z, rfl⟩ := ContinuousCohomology.π_surjective X 2 v
  let c : C(F × F, X) :=
    ⟨fun st => normalizedCocycle X z st.1 st.2, normalizedCocycle_continuous X z⟩
  obtain ⟨a, ha⟩ := hprimitive c (by
    intro s t u
    change normalizedCocycle X z (s * t) u + normalizedCocycle X z s t =
      normalizedCocycle X z t u + normalizedCocycle X z s (t * u)
    rw [add_comm]
    exact normalizedCocycle_cocycle X hX z s t u)
  let b : C(F, X) := -a
  have hb (s t : F) :
      b (s * t) = b s + b t + normalizedCocycle X z s t := by
    change -a (s * t) = -a s + -a t + c (s, t)
    rw [← ha s t]
    abel
  let C := homogeneousCochains X
  let q : C.X 1 := homogeneousPrimitive X hX z b
  have hq : (C.d 1 2).hom q = (C.iCycles 2).hom z :=
    homogeneousPrimitive_boundary X hX z b hb
  have hi : Function.Injective (C.iCycles 2) :=
    (ModuleCat.mono_iff_injective
      ((forget₂ (TopModuleCat R) (ModuleCat R)).map (C.iCycles 2))).mp inferInstance
  have hzc : (C.toCycles 1 2).hom q = z := by
    apply hi
    exact (ConcreteCategory.congr_hom (C.toCycles_i 1 2) q).trans hq
  change C.homologyπ 2 z = 0
  rw [← hzc]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 1 2) q

end
end TopRep.TrivialDegreeTwoCocycles
