/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Extending a finite quotient layer beyond an open subgroup

The kernel of a discrete quotient of an open subgroup is open in the
ambient compact group. Its normal core gives an actual finite ambient
quotient whose subgroup image still maps onto the prescribed quotient.
-/

namespace ProCGroups.FreeProC.Characterization

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- A discrete quotient of an open subgroup factors through its actual image
in a finite quotient of the ambient group. Both resulting maps are continuous
and surjective, and the first map retains the ambient quotient projection.
Finiteness of the given discrete target follows from these conclusions. -/
theorem exists_finiteQuotient_factor_of_openSubgroup (H : OpenSubgroup G)
    {B : Type v} [Group B] [TopologicalSpace B] [DiscreteTopology B]
    (π : H →ₜ* B) (hπ : Function.Surjective π) :
    ∃ V : OpenNormalSubgroup G, (V : Subgroup G) ≤ (H : Subgroup G) ∧
      let q : H →* G ⧸ (V : Subgroup G) :=
        (QuotientGroup.mk' (V : Subgroup G)).comp (H : Subgroup G).subtype
      ∃ θ : H →ₜ* q.range, ∃ ρ : q.range →ₜ* B,
        Function.Surjective θ ∧ Function.Surjective ρ ∧
          (∀ h : H, (θ h : G ⧸ (V : Subgroup G)) =
            ProC.OpenNormalSubgroup.quotientProj V (h : G)) ∧
          ρ.comp θ = π ∧
          (∀ x : G, ProC.OpenNormalSubgroup.quotientProj V x ∈ q.range ↔ x ∈ H) := by
  classical
  let W : OpenSubgroup G :=
    { toSubgroup := π.toMonoidHom.ker.map (H : Subgroup G).subtype
      isOpen' := H.isOpen.isOpenMap_subtype_val _
        (ProC.OpenNormalSubgroup.ker π).isOpen' }
  let V : OpenNormalSubgroup G := ProC.OpenNormalSubgroup.normalCore W
  have hVW : (V : Subgroup G) ≤ (W : Subgroup G) :=
    ProC.OpenNormalSubgroup.normalCore_le W
  have hVH : (V : Subgroup G) ≤ (H : Subgroup G) := by
    intro g hg
    obtain ⟨h, _, hh⟩ := hVW hg
    rw [← hh]
    exact h.property
  have hVker (h : H) (hh : (h : G) ∈ (V : Subgroup G)) : π h = 1 := by
    obtain ⟨k, hk, hkh⟩ := hVW hh
    have heq : k = h := Subtype.ext hkh
    exact heq ▸ hk
  refine ⟨V, hVH, ?_⟩
  let q : H →* G ⧸ (V : Subgroup G) :=
    (QuotientGroup.mk' (V : Subgroup G)).comp (H : Subgroup G).subtype
  let θ : H →ₜ* q.range :=
    { toMonoidHom := q.rangeRestrict
      continuous_toFun :=
        ((ProC.OpenNormalSubgroup.quotientProj V).continuous_toFun.comp
          continuous_subtype_val).subtype_mk (fun h => ⟨h, rfl⟩) }
  have hθ : Function.Surjective θ := MonoidHom.rangeRestrict_surjective q
  have hker : θ.toMonoidHom.ker ≤ π.toMonoidHom.ker := by
    intro h hh
    change θ h = 1 at hh
    have hq : ProC.OpenNormalSubgroup.quotientProj V (h : G) = 1 :=
      congrArg Subtype.val hh
    exact hVker h (ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mp hq)
  let ρ : q.range →ₜ* B :=
    { toMonoidHom := θ.toMonoidHom.liftOfSurjective hθ ⟨π.toMonoidHom, hker⟩
      continuous_toFun := continuous_of_discreteTopology }
  have hρ (h : H) : ρ (θ h) = π h :=
    θ.toMonoidHom.liftOfRightInverse_comp_apply (Function.surjInv hθ)
      (Function.rightInverse_surjInv hθ) ⟨π.toMonoidHom, hker⟩ h
  refine ⟨θ, ρ, hθ, ?_, ?_, ?_, ?_⟩
  · intro b
    obtain ⟨h, hh⟩ := hπ b
    exact ⟨θ h, (hρ h).trans hh⟩
  · intro h
    rfl
  · exact ContinuousMonoidHom.ext hρ
  · intro x
    constructor
    · rintro ⟨h, hh⟩
      change ProC.OpenNormalSubgroup.quotientProj V (h : G) =
        ProC.OpenNormalSubgroup.quotientProj V x at hh
      have hdiv : x / (h : G) ∈ (V : Subgroup G) :=
        ProC.OpenNormalSubgroup.quotientProj_eq_quotientProj_iff.mp hh.symm
      have hx : x / (h : G) * (h : G) ∈ H := H.mul_mem (hVH hdiv) h.property
      simpa only [div_mul_cancel] using hx
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩

end ProCGroups.FreeProC.Characterization
