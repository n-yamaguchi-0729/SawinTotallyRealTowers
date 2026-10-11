/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.PGroup
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Fixed lifts under coprime group actions

A fixed element of an equivariant quotient has an invariant fiber.  This fiber
has the cardinality of the kernel.  Orbit counting for an `r`-group therefore
produces a fixed lift whenever `r` does not divide that cardinality.  In
particular, this holds for a quotient of a finite `p`-group when `r ≠ p`.

No finiteness assumption on the acting group is needed.  The fiber uses the
canonical action on a `SubMulAction`; no action instance is installed here.
-/

namespace ClassFieldTower.ProP

universe u v w

variable {Γ : Type u} {P : Type v} {Q : Type w}
    [Group Γ] [Group P] [Group Q]
    [MulDistribMulAction Γ P] [MulDistribMulAction Γ Q]

/-- Orbit counting on the actual fiber of an equivariant surjection produces a
fixed lift if the acting prime does not divide the kernel's cardinality. -/
theorem exists_fixed_lift_of_not_dvd_card_ker
    {r : ℕ} [Fact r.Prime] (hΓ : IsPGroup r Γ)
    (f : P →*[Γ] Q) (hf : Function.Surjective f)
    (hker : ¬ r ∣ Nat.card f.toMonoidHom.ker)
    (y : Q) (hy : ∀ γ : Γ, γ • y = y) :
    ∃ x : P, f x = y ∧ ∀ γ : Γ, γ • x = x := by
  let X : SubMulAction Γ P :=
    { carrier := f.toMonoidHom ⁻¹' {y}
      smul_mem' := by
        intro γ x hx
        change f (γ • x) = y
        change f x = y at hx
        exact (f.map_smul' γ x).trans ((congrArg (γ • ·) hx).trans (hy γ)) }
  have hcard : Nat.card X = Nat.card f.toMonoidHom.ker :=
    Nat.card_congr
      (MonoidHom.fiberEquivKerOfSurjective (f := f.toMonoidHom) hf y)
  have hrX : ¬ r ∣ Nat.card X := by
    rw [hcard]
    exact hker
  obtain ⟨x, hx⟩ := hΓ.nonempty_fixed_point_of_prime_not_dvd_card X hrX
  refine ⟨(x : P), x.property, ?_⟩
  intro γ
  exact congrArg (fun z : X => (z : P)) ((MulAction.mem_fixedPoints.mp hx) γ)

/-- A fixed element of an equivariant quotient of a finite `p`-group lifts to a
fixed element under any `r`-group action, for distinct primes `r` and `p`. -/
theorem exists_fixed_lift_of_isPGroup
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] [Finite P]
    (hP : IsPGroup p P) (hΓ : IsPGroup r Γ) (hrp : r ≠ p)
    (f : P →*[Γ] Q) (hf : Function.Surjective f)
    (y : Q) (hy : ∀ γ : Γ, γ • y = y) :
    ∃ x : P, f x = y ∧ ∀ γ : Γ, γ • x = x := by
  have hker : IsPGroup p f.toMonoidHom.ker := hP.to_subgroup f.toMonoidHom.ker
  obtain ⟨n, hn⟩ := hker.exists_card_eq
  have hrker : ¬ r ∣ Nat.card f.toMonoidHom.ker := by
    rw [hn]
    intro hdiv
    have hrp' : r ∣ p := (Fact.out : r.Prime).dvd_of_dvd_pow hdiv
    have hpr : p = r :=
      ((Fact.out : p.Prime).dvd_iff_eq (Fact.out : r.Prime).ne_one).mp hrp'
    exact hrp hpr.symm
  exact exists_fixed_lift_of_not_dvd_card_ker hΓ f hf hrker y hy

end ClassFieldTower.ProP
