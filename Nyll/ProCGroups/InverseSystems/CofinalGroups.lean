/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.InverseSystems.CofinalityAndDensity
import Nyll.ProCGroups.InverseSystems.GroupSystemRestriction
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Multiplicativity of the existing cofinal restriction

The native homeomorphism already constructs the inverse and proves its
continuity. Its forward map is the original coordinate restriction. The
existing restricted-system owner supplies both group structures.
-/

noncomputable section

namespace ProCGroups.InverseSystems.InverseSystem

universe u v

variable {I : Type u} [Preorder I]

/-- A cofinal subset of a directed preorder is directed. -/
theorem directed_subtype_of_cofinal
    (T : Set I) (hdir : Directed (· ≤ ·) (id : I → I))
    (hcofinal : ∀ i : I, ∃ t : T, i ≤ t.val) :
    Directed (· ≤ ·) (id : T → T) := by
  intro a b
  obtain ⟨i, hai, hbi⟩ := hdir a.val b.val
  obtain ⟨t, hit⟩ := hcofinal i
  exact ⟨t, (show a.val ≤ t.val from le_trans hai hit),
    (show b.val ≤ t.val from le_trans hbi hit)⟩

variable (S : InverseSystem.{u, v} (I := I))
  [∀ i, Group (S.X i)] [IsGroupSystem S]

/-- The existing cofinal restriction homeomorphism preserves multiplication. -/
def continuousMulEquiv_restrict_cofinal
    (T : Set I) (hdir : Directed (· ≤ ·) (id : I → I))
    (hcofinal : ∀ i : I, ∃ t : T, i ≤ t.val) :
    S.inverseLimit ≃ₜ* (S.restrict T).inverseLimit :=
  ContinuousMulEquiv.mk'
    (S.homeomorph_restrict_cofinal T
      (directed_subtype_of_cofinal T hdir hcofinal) hcofinal) (by
    intro x y
    apply (S.restrict T).ext
    intro t
    have hπ (z : S.inverseLimit) :
        (S.restrict T).projection t
          ((S.homeomorph_restrict_cofinal T
            (directed_subtype_of_cofinal T hdir hcofinal) hcofinal).toFun z) =
          S.projection t.val z :=
      congrFun (S.π_comp_homeomorph_restrict_cofinal T
        (directed_subtype_of_cofinal T hdir hcofinal) hcofinal t) z
    exact (hπ (x * y)).trans
      ((projection_mul (S := S) t.val x y).trans
        ((congrArg₂ (fun a b : S.X t.val => a * b) (hπ x).symm (hπ y).symm).trans
          (projection_mul (S := S.restrict T) t
            ((S.homeomorph_restrict_cofinal T
              (directed_subtype_of_cofinal T hdir hcofinal) hcofinal).toFun x)
            ((S.homeomorph_restrict_cofinal T
              (directed_subtype_of_cofinal T hdir hcofinal) hcofinal).toFun y)).symm)))

/-- Restricting a compatible family retains its original coordinate. -/
theorem projection_continuousMulEquiv_restrict_cofinal
    (T : Set I) (hdir : Directed (· ≤ ·) (id : I → I))
    (hcofinal : ∀ i : I, ∃ t : T, i ≤ t.val)
    (t : T) (x : S.inverseLimit) :
    (S.restrict T).projection t
        ((S.continuousMulEquiv_restrict_cofinal T hdir hcofinal).toFun x) =
      S.projection t.val x :=
  congrFun (S.π_comp_homeomorph_restrict_cofinal T
    (directed_subtype_of_cofinal T hdir hcofinal) hcofinal t) x

end ProCGroups.InverseSystems.InverseSystem

end
