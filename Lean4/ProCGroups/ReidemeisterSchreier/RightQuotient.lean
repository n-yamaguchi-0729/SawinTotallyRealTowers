import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

/-!
# Right cosets for Schreier rewriting

This module exposes the right-coset quotient of a group by a subgroup and its
natural action

`g • [a] = [a * g⁻¹]`.

The quotient is intentionally only a coset space: for a non-normal subgroup it
has no multiplication.  Algebraic quotient arguments therefore use the usual
left quotient rather than a misleading `MulEquiv` wrapper.
-/

namespace ReidemeisterSchreier

universe u

variable {G : Type u} [Group G]

/-- The right quotient `H \ G`, encoded by mathlib's right-coset relation. -/
abbrev RightQuotient (H : Subgroup G) :=
  Quotient (QuotientGroup.rightRel H)

/-- The right coset of an element modulo a subgroup. -/
def rightCoset (H : Subgroup G) (g : G) : RightQuotient H :=
  Quotient.mk'' g

/-- A right coset is the base coset exactly when its representative lies in the subgroup. -/
theorem rightCoset_eq_basepoint_iff_mem
    {H : Subgroup G} {g : G} :
    rightCoset H g = rightCoset H (1 : G) ↔ g ∈ H := by
  constructor
  · intro hg
    have hrel : QuotientGroup.rightRel H g 1 := Quotient.exact' hg
    have hginv : g⁻¹ ∈ H := by
      simpa using (QuotientGroup.rightRel_apply.mp hrel)
    simpa using H.inv_mem hginv
  · intro hg
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simpa using H.inv_mem hg

/-- Right multiplication on right cosets, expressed as a left action by
`g • [a] = [a * g⁻¹]`. -/
@[reducible] def rightCosetMulAction (H : Subgroup G) :
    MulAction G (RightQuotient H) where
  smul g :=
    Quotient.map' (fun a => a * g⁻¹) fun a b hab => by
      rw [QuotientGroup.rightRel_apply] at hab ⊢
      simpa [mul_assoc] using hab
  one_smul q := by
    refine Quotient.inductionOn' q ?_
    intro a
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simp only [inv_one, mul_one, mul_inv_cancel, one_mem]
  mul_smul g h q := by
    refine Quotient.inductionOn' q ?_
    intro a
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simp only [mul_assoc, mul_inv_rev, inv_inv, inv_mul_cancel_left, mul_inv_cancel, one_mem]

attribute [instance] rightCosetMulAction

/-- Acting on a represented right coset multiplies its representative by the inverse on the
right. -/
@[simp] theorem rightCosetMulAction_mk_smul
    (H : Subgroup G) (g a : G) :
    letI := rightCosetMulAction H
    g • (Quotient.mk'' a : RightQuotient H) = Quotient.mk'' (a * g⁻¹) :=
  rfl

/-- Acting by an inverse on a represented right coset multiplies its representative on the
right. -/
@[simp] theorem rightCosetMulAction_inv_mk_smul
    (H : Subgroup G) (g a : G) :
    letI := rightCosetMulAction H
    g⁻¹ • (Quotient.mk'' a : RightQuotient H) = Quotient.mk'' (a * g) := by
  rw [rightCosetMulAction_mk_smul (H := H) g⁻¹ a]
  simp only [inv_inv]

end ReidemeisterSchreier
