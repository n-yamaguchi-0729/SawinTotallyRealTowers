/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.Frattini
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Order.Atoms
public import Mathlib.Order.RelIso.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Frattini subgroups of elementary abelian groups

The subgroup lattice of an abelian group of prime exponent is the submodule lattice of its
actual additive group over the prime field. Its coatomicity is therefore valid in arbitrary
dimension. No finiteness or topological separation assumption is used here.
-/

@[expose] public section

namespace ClassFieldTower.ProP

universe u

/-- An abelian group of prime exponent has trivial abstract Frattini subgroup. -/
theorem frattini_eq_bot_of_prime_exponent
    {p : ℕ} {G : Type u} [CommGroup G] [Fact (Nat.Prime p)]
    (hpow : ∀ g : G, g ^ p = 1) : frattini G = ⊥ := by
  have hpowAdd (x : Additive G) : p • x = 0 := by
    change (Additive.toMul x) ^ p = 1
    exact hpow (Additive.toMul x)
  have : Module (ZMod p) (Additive G) := AddCommGroup.zmodModule hpowAdd
  let eZMod : AddSubgroup (Additive G) ≃o Submodule (ZMod p) (Additive G) :=
    AddSubgroup.toZModSubmodule p (M := Additive G)
  let e : Subgroup G ≃o Submodule (ZMod p) (Additive G) :=
    RelIso.trans (Subgroup.toAddSubgroup (G := G)) eZMod
  let : IsCoatomic (Subgroup G) :=
    (OrderIso.isCoatomic_iff e).mpr
      (inferInstance : IsCoatomic (Submodule (ZMod p) (Additive G)))
  let Fadd : AddSubgroup (Additive G) :=
    Subgroup.toAddSubgroup (frattini G)
  let Fmod : Submodule (ZMod p) (Additive G) :=
    AddSubgroup.toZModSubmodule p Fadd
  obtain ⟨Kmod, hKmod⟩ := Fmod.exists_isCompl
  obtain ⟨hdisjmod, hcodisjmod⟩ := hKmod
  let Kadd : AddSubgroup (Additive G) :=
    Kmod.toAddSubgroup
  let K : Subgroup G :=
    AddSubgroup.toSubgroup' Kadd
  have hsup : frattini G ⊔ K = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a, b, ha, hb, hab⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hcodisjmod (Additive.ofMul x)
    have haF : Additive.toMul a ∈ frattini G := by
      exact ha
    have hbK : Additive.toMul b ∈ K := by
      exact hb
    change Additive.toMul a * Additive.toMul b = x at hab
    rw [← hab]
    exact Subgroup.mul_mem _
      ((le_sup_left : frattini G ≤
        frattini G ⊔ K) haF)
      ((le_sup_right : K ≤ frattini G ⊔ K) hbK)
  have hKtop : K = ⊤ :=
    frattini_nongenerating ((sup_comm K (frattini G)).trans hsup)
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxK : x ∈ K := by rw [hKtop]; exact Subgroup.mem_top x
  have hz : Additive.ofMul x = 0 :=
    (Submodule.disjoint_def.mp hdisjmod) (Additive.ofMul x)
      (by exact hx)
      (by exact hxK)
  change x = 1 at hz
  exact hz

end ClassFieldTower.ProP
