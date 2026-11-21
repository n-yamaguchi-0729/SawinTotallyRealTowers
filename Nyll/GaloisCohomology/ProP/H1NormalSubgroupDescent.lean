/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Degree-one descent along a normal subgroup

A one-cocycle that vanishes on a normal subgroup takes values in the subgroup
invariants and descends to the quotient.  Subtracting a boundary on the normal
subgroup gives the degree-one vanishing induction step for arbitrary
coefficients.  The construction is used to propagate cyclic class-formation
vanishing to finite solvable extensions.
-/

@[expose] public section

open CategoryTheory

namespace ClassFieldTower.Cohomology

open groupCohomology

noncomputable section

universe u v r

section OriginalCoefficients

variable {R : Type r} {G : Type u} [CommRing R] [Group G]
variable (A : Rep.{v} R G) (N : Subgroup G) [N.Normal]

/-- Every actual crossed homomorphism of the original representation is a boundary. -/
def HasH1Primitives : Prop :=
  ∀ z : G → A, (∀ g h, z (g * h) = A.ρ g (z h) + z g) →
    ∃ a : A, ∀ g, A.ρ g a - a = z g

/-- An actual crossed homomorphism that vanishes on the normal subgroup
takes values in its invariant submodule. -/
theorem h1Function_value_invariant
    (z : G → A) (hc : ∀ g h, z (g * h) = A.ρ g (z h) + z g)
    (hz : ∀ n : N, z n.1 = 0) (g : G) :
    z g ∈ Representation.invariants (A.ρ.comp N.subtype) := by
  intro n
  change A.ρ n.1 (z g) = z g
  have hng := hc n.1 g
  have hmem : g⁻¹ * n.1 * g ∈ N := Subgroup.Normal.conj_mem' inferInstance n.1 n.2 g
  have hgn := hc g (g⁻¹ * n.1 * g)
  rw [hz n, add_zero] at hng
  rw [hz ⟨_, hmem⟩, map_zero, zero_add] at hgn
  simp only [← mul_assoc, mul_inv_cancel, one_mul] at hgn
  exact hng.symm.trans hgn

/-- A cocycle vanishing on the subgroup descends on the original invariant coefficients. -/
def descendedH1Function
    (z : G → A) (hc : ∀ g h, z (g * h) = A.ρ g (z h) + z g)
    (hz : ∀ n : N, z n.1 = 0) : G ⧸ N → (A.quotientToInvariants N) :=
  Quotient.lift
    (fun g => ⟨z g, h1Function_value_invariant A N z hc hz g⟩)
    (by
      intro g h hgh
      apply Subtype.ext
      have hn : g⁻¹ * h ∈ N := (QuotientGroup.leftRel_apply).mp hgh
      have hrel := hc g (g⁻¹ * h)
      rw [hz ⟨_, hn⟩, map_zero, zero_add] at hrel
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hrel.symm)

/-- The descended function satisfies the original cocycle equation on the quotient. -/
theorem descendedH1Function_mul
    (z : G → A) (hc : ∀ g h, z (g * h) = A.ρ g (z h) + z g)
    (hz : ∀ n : N, z n.1 = 0) (g h : G ⧸ N) :
    descendedH1Function A N z hc hz (g * h) =
      (A.quotientToInvariants N).ρ g (descendedH1Function A N z hc hz h) +
        descendedH1Function A N z hc hz g := by
  refine QuotientGroup.induction_on g (fun g => ?_)
  refine QuotientGroup.induction_on h (fun h => ?_)
  apply Subtype.ext
  exact hc g h

/-- The subgroup and quotient primitives give primitives for the original group. -/
theorem hasH1Primitives_of_normalSubgroup
    (hN : HasH1Primitives (Rep.res N.subtype A))
    (hQ : HasH1Primitives (A.quotientToInvariants N)) : HasH1Primitives A := by
  intro z hz
  obtain ⟨a, ha⟩ := hN (fun n => z n.val) (fun n m => hz n.val m.val)
  let v : G → A := fun g => z g - (A.ρ g a - a)
  have hv (g h : G) : v (g * h) = A.ρ g (v h) + v g := by
    dsimp only [v]
    rw [hz, map_sub, map_sub, map_mul, mul_apply_eq_comp]
    abel
  have hn (n : N) : v n.val = 0 := sub_eq_zero.mpr (ha n).symm
  let d := descendedH1Function A N v hv hn
  obtain ⟨b, hb⟩ := hQ d (descendedH1Function_mul A N v hv hn)
  refine ⟨a + b.val, fun g => ?_⟩
  have hg := congrArg Subtype.val (hb (QuotientGroup.mk' N g))
  change A.ρ g b.val - b.val = z g - (A.ρ g a - a) at hg
  rw [map_add]
  calc
    _ = (A.ρ g a - a) + (A.ρ g b.val - b.val) := by abel
    _ = z g := by rw [hg]; abel

/-- Inflating a cocycle and taking an original primitive produces a primitive
in the subgroup invariants, so degree-one vanishing passes to the quotient. -/
theorem hasH1Primitives_quotient_of (hG : HasH1Primitives A) :
    HasH1Primitives (A.quotientToInvariants N) := by
  intro z hz
  let π := QuotientGroup.mk' N
  have h1 : z 1 = 0 := by
    have e := hz 1 1
    rw [one_mul, map_one, one_apply_eq_self] at e
    exact (add_left_cancel (show z 1 + 0 = z 1 + z 1 from (add_zero _).trans e)).symm
  obtain ⟨a, ha⟩ := hG (fun g => (z (π g)).val) (fun g h => by
    rw [map_mul]
    exact congrArg Subtype.val (hz (π g) (π h)))
  let b : A.quotientToInvariants N := ⟨a, fun n => by
    have hn := ha n.val
    have hπ : π n.val = 1 := (QuotientGroup.eq_one_iff n.val).mpr n.property
    rw [hπ, h1] at hn
    exact sub_eq_zero.mp hn⟩
  refine ⟨b, fun q => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  apply Subtype.ext
  exact ha g

end OriginalCoefficients

variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G) (N : Subgroup G) [N.Normal]

/-- A one-cocycle vanishing on a normal subgroup has invariant values. -/
theorem h1Cocycle_value_invariant_of_vanishes
    (z : cocycles₁ A) (hz : ∀ n : N, z n.1 = 0) (g : G) :
    z g ∈ Representation.invariants (A.ρ.comp N.subtype) := by
  exact h1Function_value_invariant A N z ((mem_cocycles₁_iff z).mp z.2) hz g

/-- Descend a one-cocycle vanishing on a normal subgroup to the quotient,
with coefficients in the invariant subrepresentation. -/
def descendedH1Cocycle
    (z : cocycles₁ A) (hz : ∀ n : N, z n.1 = 0) :
    cocycles₁ (A.quotientToInvariants N) := by
  let hc := (mem_cocycles₁_iff z).mp z.2
  exact ⟨descendedH1Function A N z hc hz,
    (mem_cocycles₁_iff _).mpr (descendedH1Function_mul A N z hc hz)⟩

/-- The descended cocycle agrees with the original one on quotient representatives. -/
@[simp]
theorem descendedH1Cocycle_mk
    (z : cocycles₁ A) (hz : ∀ n : N, z n.1 = 0) (g : G) :
    (descendedH1Cocycle A N z hz (QuotientGroup.mk' N g)).1 = z g := rfl

/-- The normal-subgroup induction step for degree-one vanishing.  A primitive
on the subgroup is subtracted first; a quotient primitive then completes the
primitive on the full group. -/
theorem h1_subsingleton_of_normalSubgroup
    (hN : Subsingleton (H1 (Rep.res N.subtype A)))
    (hQ : Subsingleton (H1 (A.quotientToInvariants N))) :
    Subsingleton (H1 A) := by
  have hzero (x : H1 A) : x = 0 := by
    refine H1_induction_on x ?_
    intro z
    let zN : cocycles₁ (Rep.res N.subtype A) :=
      ⟨fun n => z n.1, (mem_cocycles₁_iff _).mpr
        (fun n m => (mem_cocycles₁_iff z).mp z.2 n.1 m.1)⟩
    have hzN : H1π (Rep.res N.subtype A) zN = 0 :=
      @Subsingleton.elim _ hN _ _
    obtain ⟨a, ha⟩ := (H1π_eq_zero_iff zN).mp hzN
    let ba : cocycles₁ A := ⟨d₀₁ A a, d₀₁_apply_mem_cocycles₁ a⟩
    let z' : cocycles₁ A := z - ba
    have hz' : ∀ n : N, z' n.1 = 0 := by
      intro n
      change z n.1 - (d₀₁ A a) n.1 = 0
      exact sub_eq_zero.mpr (congrFun ha n).symm
    let d := descendedH1Cocycle A N z' hz'
    have hd : H1π (A.quotientToInvariants N) d = 0 :=
      @Subsingleton.elim _ hQ _ _
    obtain ⟨b, hb⟩ := (H1π_eq_zero_iff d).mp hd
    apply (H1π_eq_zero_iff z).mpr
    refine ⟨a + b.1, ?_⟩
    funext g
    have hg := congrArg Subtype.val (congrFun hb (QuotientGroup.mk' N g))
    change A.ρ g b.1 - b.1 = z g - (A.ρ g a - a) at hg
    change A.ρ g (a + b.1) - (a + b.1) = z g
    rw [map_add]
    calc
      _ = (A.ρ g a - a) + (A.ρ g b.1 - b.1) := by abel
      _ = z g := by rw [hg]; abel
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

end

end ClassFieldTower.Cohomology
