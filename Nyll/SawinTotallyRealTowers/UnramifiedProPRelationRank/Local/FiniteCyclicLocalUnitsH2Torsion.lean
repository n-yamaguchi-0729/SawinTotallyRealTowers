/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FiniteCyclicLocalUnitsH2
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Torsion in finite cyclic local unit cohomology

Finite local reciprocity identifies the actual unit-coefficient H² with the
cyclic Galois group. Its n-torsion therefore has at most n elements for every
positive integer n, including n = 2 and every prime n.
-/

@[expose] public section

namespace ClassFieldTower.Martinet.Shafarevich

/-- The n-torsion of the actual unit-coefficient H² of a finite cyclic local
Galois extension has at most n elements. -/
theorem finiteCyclicLocalUnitsH2_torsion_natCard_le
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L/K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g)
    (n : ℕ) (hn : 0 < n) :
    Nat.card {x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 // n • x = 0} ≤ n := by
  classical
  let : IsCyclic (Gal(L / K)) := CyclicCohomology.isCyclic_of_generator g hg
  let e : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ≃+
      Additive (Gal(L / K)) := finiteCyclicLocalUnitsH2AddEquivGalois K L g hg
  let f : {x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 // n • x = 0} →
      {σ : Additive (Gal(L / K)) // n • σ = 0} := fun x ↦
    ⟨e x.val, by rw [← map_nsmul, x.property, map_zero]⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  refine (Nat.card_le_card_of_injective f hf).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsAddCyclic.card_nsmul_eq_zero_le hn

end ClassFieldTower.Martinet.Shafarevich
