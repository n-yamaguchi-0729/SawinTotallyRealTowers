/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Invariants
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false
/-!
# Degree-one descent along a normal subgroup

A one-cocycle that vanishes on a normal subgroup takes values in the subgroup
invariants and descends to the quotient.  Subtracting a boundary on the normal
subgroup gives the degree-one vanishing induction step for arbitrary
coefficients.  The construction is used to propagate cyclic class-formation
vanishing to finite solvable extensions.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

open groupCohomology

noncomputable section

variable {k G : Type} [CommRing k] [Group G]
variable (A : Rep k G) (N : Subgroup G) [N.Normal]

/-- A one-cocycle vanishing on a normal subgroup has invariant values. -/
theorem h1Cocycle_value_invariant_of_vanishes
    (z : cocycles₁ A) (hz : ∀ n : N, z n.1 = 0) (g : G) :
    z g ∈ Representation.invariants (A.ρ.comp N.subtype) := by
  intro n
  change A.ρ n.1 (z g) = z g
  have hng := (mem_cocycles₁_iff z).mp z.2 n.1 g
  have hc : g⁻¹ * n.1 * g ∈ N :=
    Subgroup.Normal.conj_mem' inferInstance n.1 n.2 g
  have hgn := (mem_cocycles₁_iff z).mp z.2 g (g⁻¹ * n.1 * g)
  rw [hz n, add_zero] at hng
  rw [hz ⟨_, hc⟩, map_zero, zero_add] at hgn
  simp only [← mul_assoc, mul_inv_cancel, one_mul] at hgn
  exact hng.symm.trans hgn

/-- Descend a one-cocycle vanishing on a normal subgroup to the quotient,
with coefficients in the invariant subrepresentation. -/
def descendedH1Cocycle
    (z : cocycles₁ A) (hz : ∀ n : N, z n.1 = 0) :
    cocycles₁ (A.quotientToInvariants N) := by
  let f : G ⧸ N → (A.quotientToInvariants N) :=
    Quotient.lift
      (fun g => ⟨z g, h1Cocycle_value_invariant_of_vanishes A N z hz g⟩)
      (by
        intro g h hgh
        apply Subtype.ext
        have hn : g⁻¹ * h ∈ N := (QuotientGroup.leftRel_apply).mp hgh
        have hc := (mem_cocycles₁_iff z).mp z.2 g (g⁻¹ * h)
        rw [hz ⟨_, hn⟩, map_zero, zero_add] at hc
        simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hc.symm)
  refine ⟨f, (mem_cocycles₁_iff f).mpr ?_⟩
  intro g h
  refine QuotientGroup.induction_on g (fun g => ?_)
  refine QuotientGroup.induction_on h (fun h => ?_)
  apply Subtype.ext
  exact (mem_cocycles₁_iff z).mp z.2 g h

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

