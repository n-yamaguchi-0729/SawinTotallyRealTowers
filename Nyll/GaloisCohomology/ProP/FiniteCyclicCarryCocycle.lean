/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Generator coordinates and the cyclic carry cocycle

A specified generator of a finite cyclic group identifies the group with
`ZMod (Nat.card G)`.  Taking the standard natural-number representative
of that coordinate records multiplication by addition with a possible carry.
This file constructs the resulting normalized inhomogeneous two-cocycle from
a coefficient fixed by the chosen generator; cyclicity makes it invariant.

The comparison with the periodic resolution is deliberately left to the next
gate; this file only constructs the explicit bar representative.
-/

@[expose] public section

namespace ClassFieldTower.Cohomology

noncomputable section

open CategoryTheory Representation

universe u

/-- The coordinate in `ZMod (card G)` determined by a specified generator. -/
noncomputable def finiteCyclicGeneratorCoordinate
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : G) :
    ZMod (Nat.card G) :=
  Multiplicative.toAdd
    ((zmodMulEquivOfGenerator hg rfl).symm x)

@[simp]
theorem finiteCyclicGeneratorCoordinate_one
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    finiteCyclicGeneratorCoordinate g hg 1 = 0 := by
  simp only [finiteCyclicGeneratorCoordinate, map_one, toAdd_one]

@[simp]
theorem finiteCyclicGeneratorCoordinate_generator
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    finiteCyclicGeneratorCoordinate g hg g = 1 := by
  simp only [finiteCyclicGeneratorCoordinate, zmodMulEquivOfGenerator_symm_apply_generator,
    toAdd_ofAdd]

@[simp]
theorem finiteCyclicGeneratorCoordinate_mul
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x y : G) :
    finiteCyclicGeneratorCoordinate g hg (x * y) =
      finiteCyclicGeneratorCoordinate g hg x +
        finiteCyclicGeneratorCoordinate g hg y := by
  simp only [finiteCyclicGeneratorCoordinate, map_mul, toAdd_mul]

@[simp]
theorem finiteCyclicGeneratorCoordinate_zpow
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (i : ℤ) :
    finiteCyclicGeneratorCoordinate g hg (g ^ i) =
      (i : ZMod (Nat.card G)) := by
  simp only [finiteCyclicGeneratorCoordinate, zmodMulEquivOfGenerator_symm_apply_zpow, toAdd_ofAdd]

@[simp]
theorem finiteCyclicGeneratorCoordinate_pow
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (i : ℕ) :
    finiteCyclicGeneratorCoordinate g hg (g ^ i) =
      (i : ZMod (Nat.card G)) := by
  simpa using finiteCyclicGeneratorCoordinate_zpow g hg (i : ℤ)

/-- The generator coordinate is injective. -/
theorem finiteCyclicGeneratorCoordinate_injective
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Function.Injective (finiteCyclicGeneratorCoordinate g hg) := by
  intro x y hxy
  apply (zmodMulEquivOfGenerator hg rfl).symm.injective
  exact congrArg Multiplicative.ofAdd hxy

/-- Reconstructing from the standard representative of the generator
coordinate returns the original group element. -/
theorem finiteCyclicGenerator_zpow_coordinate
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : G) :
    g ^ (finiteCyclicGeneratorCoordinate g hg x).val = x := by
  apply finiteCyclicGeneratorCoordinate_injective g hg
  rw [finiteCyclicGeneratorCoordinate_pow, ZMod.natCast_zmod_val]

/-- Powers of a specified cyclic generator enumerate the group. -/
noncomputable def finiteCyclicGeneratorPowEquiv
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) : Fin (Nat.card G) ≃ G where
  toFun i := g ^ i.val
  invFun x := ⟨(finiteCyclicGeneratorCoordinate g hg x).val, ZMod.val_lt _⟩
  left_inv i := by
    apply Fin.ext
    change (finiteCyclicGeneratorCoordinate g hg (g ^ i.val)).val = i.val
    rw [finiteCyclicGeneratorCoordinate_pow]
    exact ZMod.val_natCast_of_lt i.isLt
  right_inv x := finiteCyclicGenerator_zpow_coordinate g hg x

/-- The `0`/`1` carry in the sum of the standard representatives of two
elements of `ZMod n`. -/
def zmodCarry {n : ℕ} [NeZero n] (x y : ZMod n) : ℕ :=
  if n ≤ x.val + y.val then 1 else 0

/-- Scaling both standard coordinates and their modulus by the same
positive integer preserves the carry. This includes characters whose
order is smaller than the original coefficient exponent. -/
theorem zmodCarry_eq_of_scaled_values
    {m n : ℕ} [NeZero m] [NeZero n] (k : ℕ) (hk : 0 < k)
    (hn : n = k * m) (x y : ZMod m) (x' y' : ZMod n)
    (hx : x'.val = k * x.val) (hy : y'.val = k * y.val) :
    zmodCarry x' y' = zmodCarry x y := by
  unfold zmodCarry
  rw [hx, hy, hn, ← Nat.mul_add]
  have hle : k * m ≤ k * (x.val + y.val) ↔ m ≤ x.val + y.val := by
    constructor
    · intro h
      by_contra hnot
      exact (Nat.not_lt.mpr h)
        (Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hnot) hk)
    · exact Nat.mul_le_mul_left k
  simp only [hle]

@[simp]
theorem zmodCarry_eq_one_iff {n : ℕ} [NeZero n] (x y : ZMod n) :
    zmodCarry x y = 1 ↔ n ≤ x.val + y.val := by
  simp only [zmodCarry, ite_eq_left_iff, not_le, zero_ne_one, imp_false, not_lt]

@[simp]
theorem zmodCarry_eq_zero_iff {n : ℕ} [NeZero n] (x y : ZMod n) :
    zmodCarry x y = 0 ↔ x.val + y.val < n := by
  simp only [zmodCarry, ite_eq_right_iff, one_ne_zero, imp_false, not_le]

@[simp]
theorem zmodCarry_zero_left {n : ℕ} [NeZero n] (x : ZMod n) :
    zmodCarry 0 x = 0 := by
  simp only [zmodCarry, ZMod.val_zero, zero_add, ite_eq_right_iff, one_ne_zero, imp_false, not_le,
    ZMod.val_lt x]

@[simp]
theorem zmodCarry_zero_right {n : ℕ} [NeZero n] (x : ZMod n) :
    zmodCarry x 0 = 0 := by
  simp only [zmodCarry, ZMod.val_zero, add_zero, ite_eq_right_iff, one_ne_zero, imp_false, not_le,
    ZMod.val_lt x]

/-- Carries satisfy the inhomogeneous two-cocycle equation on `ZMod n`. -/
theorem zmodCarry_cocycle {n : ℕ} [NeZero n] (x y z : ZMod n) :
    zmodCarry (x + y) z + zmodCarry x y =
      zmodCarry y z + zmodCarry x (y + z) := by
  simp only [zmodCarry]
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hz := ZMod.val_lt z
  by_cases hxy : n ≤ x.val + y.val
  · rw [ZMod.val_add_of_le hxy]
    by_cases hyz : n ≤ y.val + z.val
    · rw [ZMod.val_add_of_le hyz]
      split_ifs <;> omega
    · rw [ZMod.val_add_of_lt (Nat.lt_of_not_ge hyz)]
      split_ifs <;> omega
  · rw [ZMod.val_add_of_lt (Nat.lt_of_not_ge hxy)]
    by_cases hyz : n ≤ y.val + z.val
    · rw [ZMod.val_add_of_le hyz]
      split_ifs <;> omega
    · rw [ZMod.val_add_of_lt (Nat.lt_of_not_ge hyz)]
      split_ifs <;> omega

/-- The natural-number carry attached to multiplication in a finite cyclic
group with a specified generator. -/
def finiteCyclicCarry
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x y : G) : ℕ :=
  let _ : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  zmodCarry (finiteCyclicGeneratorCoordinate g hg x)
    (finiteCyclicGeneratorCoordinate g hg y)

@[simp]
theorem finiteCyclicCarry_one_left
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : G) :
    finiteCyclicCarry g hg 1 x = 0 := by
  let _ : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  simp only [finiteCyclicCarry, finiteCyclicGeneratorCoordinate_one, zmodCarry_zero_left]

@[simp]
theorem finiteCyclicCarry_one_right
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : G) :
    finiteCyclicCarry g hg x 1 = 0 := by
  let _ : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  simp only [finiteCyclicCarry, finiteCyclicGeneratorCoordinate_one, zmodCarry_zero_right]

/-- The carry on a finite cyclic group satisfies the two-cocycle equation. -/
theorem finiteCyclicCarry_cocycle
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x y z : G) :
    finiteCyclicCarry g hg (x * y) z + finiteCyclicCarry g hg x y =
      finiteCyclicCarry g hg y z + finiteCyclicCarry g hg x (y * z) := by
  let _ : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  simpa only [finiteCyclicCarry, finiteCyclicGeneratorCoordinate_mul] using
    zmodCarry_cocycle
      (finiteCyclicGeneratorCoordinate g hg x)
      (finiteCyclicGeneratorCoordinate g hg y)
      (finiteCyclicGeneratorCoordinate g hg z)

@[simp]
theorem finiteCyclicCarry_zpow_val
    {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (i j : ZMod (Nat.card G)) :
    finiteCyclicCarry g hg (g ^ i.val) (g ^ j.val) = zmodCarry i j := by
  let _ : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  simp only [finiteCyclicCarry, finiteCyclicGeneratorCoordinate_pow, ZMod.natCast_val,
    ZMod.cast_id', id_eq]

/-- The normalized inhomogeneous carry cocycle attached to an element fixed
by the chosen generator. -/
noncomputable def finiteCyclicCarryTwoCocycle
    {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :
    groupCohomology.cocycles₂ A := by
  have hag : A.ρ g a.1 = a.1 := by
    have hagzero := a.2
    change A.ρ g a.1 - a.1 = 0 at hagzero
    exact sub_eq_zero.mp hagzero
  have ha : a.1 ∈ A.ρ.invariants :=
    (Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg a.1).2 hag
  refine ⟨fun xy ↦ finiteCyclicCarry g hg xy.1 xy.2 • a.1, ?_⟩
  rw [groupCohomology.mem_cocycles₂_iff]
  intro x y z
  rw [map_nsmul, ha x, ← add_nsmul, ← add_nsmul,
    finiteCyclicCarry_cocycle]

@[simp]
theorem finiteCyclicCarryTwoCocycle_apply
    {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (x y : G) :
    finiteCyclicCarryTwoCocycle A g hg a (x, y) =
      finiteCyclicCarry g hg x y • a.1 :=
  rfl

@[simp]
theorem finiteCyclicCarryTwoCocycle_zpow_val
    {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (i j : ZMod (Nat.card G)) :
    finiteCyclicCarryTwoCocycle A g hg a (g ^ i.val, g ^ j.val) =
      zmodCarry i j • a.1 := by
  rw [finiteCyclicCarryTwoCocycle_apply, finiteCyclicCarry_zpow_val]

@[simp]
theorem finiteCyclicCarryTwoCocycle_one_left
    {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (x : G) :
    finiteCyclicCarryTwoCocycle A g hg a (1, x) = 0 := by
  rw [finiteCyclicCarryTwoCocycle_apply, finiteCyclicCarry_one_left, zero_smul]

@[simp]
theorem finiteCyclicCarryTwoCocycle_one_right
    {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (x : G) :
    finiteCyclicCarryTwoCocycle A g hg a (x, 1) = 0 := by
  rw [finiteCyclicCarryTwoCocycle_apply, finiteCyclicCarry_one_right, zero_smul]

end

end ClassFieldTower.Cohomology
