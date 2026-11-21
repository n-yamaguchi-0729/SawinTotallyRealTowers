/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology
public import Nyll.GaloisCohomology.Cyclic.MultiplicativeHilbert90

/-!
# Hilbert 90 for the original integral field-unit representation

A faithful group of automorphisms acts on the original field units. Every
degree-one cocycle in the existing integral cohomology backend descends through
its carrier lift to a multiplicative cocycle. Noether's theorem supplies an
actual unit primitive, which lifts back to a coboundary in that same complex.
In particular this proves vanishing for every subgroup of the automorphism
group, without a cyclicity or normality assumption on the subgroup.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable (K : Type u) (L : Type v) [Field K] [Field L]
  [Algebra K L] [FiniteDimensional K L]

/-- Hilbert 90 in the existing integral backend for any faithful action by
field automorphisms. The acting group and both fields have independent universes. -/
theorem unitsH1_isZero_of_injective
    {G : Type w} [Group G] (ρ : G →* Gal(L/K)) (hρ : Function.Injective ρ) :
    Limits.IsZero (cohomology (Rep.res ρ (Rep.ofAlgebraAutOnUnits K L)) 1) := by
  let A : Rep.{v} ℤ G := Rep.res ρ (Rep.ofAlgebraAutOnUnits K L)
  let B := (nativeFunctor G).obj A
  have hz (x : groupCohomology B 1) : x = 0 := by
    refine groupCohomology.H1_induction_on x ?_
    intro c
    apply (groupCohomology.H1π_eq_zero_iff c).mpr
    let f : G → Lˣ := fun g =>
      Additive.toMul (α := Lˣ)
        (show ULift.{w} (Additive Lˣ) from c (ULift.up g)).down
    have hf (g h : G) : f (g * h) = ρ g • f h * f g := by
      exact congrArg (fun z : B => Additive.toMul (α := Lˣ)
        (show ULift.{w} (Additive Lˣ) from z).down)
        ((groupCohomology.mem_cocycles₁_iff c).mp c.property
          (ULift.up g) (ULift.up h))
    obtain ⟨b, hb⟩ := groupCohomology.exists_unit_coboundary_of_injective_algAutHom
      ρ hρ f hf
    refine ⟨ULift.up (Additive.ofMul b), ?_⟩
    funext g
    apply ULift.ext
    apply Additive.toMul.injective
    exact hb g.down
  have hs : Subsingleton (cohomology A 1) :=
    ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact @ModuleCat.isZero_of_subsingleton ℤ _ (cohomology A 1) hs

/-- Every subgroup satisfies Hilbert 90 on the restricted original unit
representation. This includes nonnormal and nonabelian subgroups. -/
theorem subgroupUnitsH1_isZero (H : Subgroup Gal(L/K)) :
    Limits.IsZero (cohomology
      (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 1) :=
  unitsH1_isZero_of_injective K L H.subtype Subtype.val_injective

/-- Hilbert 90 on the original full automorphism representation, in arbitrary
field universes and with no Galois hypothesis on the finite extension. -/
theorem unitsH1_isZero :
    Limits.IsZero (cohomology (Rep.ofAlgebraAutOnUnits K L) 1) :=
  unitsH1_isZero_of_injective K L (MonoidHom.id Gal(L/K)) (fun _ _ h => h)

end IntegralGroupCohomology.Universe
