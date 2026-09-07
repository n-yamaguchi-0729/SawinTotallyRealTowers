import ProCGroups.Cohomology.FiniteInvariantCharacter
import ProCGroups.ProC.InverseLimits.Predicates
import ProCGroups.ProC.OpenNormalSubgroups.Separation
import Mathlib.Topology.Instances.ZMod

set_option autoImplicit false
/-!
# Relative Nakayama characters for pro-p groups

A strict inclusion of closed ambient-normal subgroups of a pro-`p` group can be detected by a
nonzero continuous `ZMod p`-valued character.  The construction separates one element in a finite
`p`-group quotient and applies the finite invariant-character theorem there.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC

noncomputable section

universe u

/-- Relative pro-`p` Nakayama in character form: a strict inclusion of closed ambient-normal
subgroups is detected by a nonzero continuous character which vanishes on the smaller subgroup
and is invariant under conjugation by the ambient group. -/
theorem relativeNakayama_character
    {p : ℕ} [Fact p.Prime]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (hF : HasPGroupOpenNormalBasis p F)
    (K R : ClosedSubgroup F) [K.Normal] [R.Normal] (hKR : K < R) :
    ∃ χ : R →ₜ* Multiplicative (ZMod p),
      χ ≠ 1 ∧
        (∀ k : K, χ ⟨k, hKR.le k.2⟩ = 1) ∧
        ∀ (f : F) (r : R), χ (MulAut.conjNormal f r) = χ r := by
  classical
  obtain ⟨x, hxR, hxK⟩ := SetLike.exists_of_lt hKR
  obtain ⟨W, _hWtop, hxKW⟩ :=
    exists_openNormalSubgroup_le_not_mem_sup_closedSubgroup K hxK
      (⊤ : OpenNormalSubgroup F)
  let U : OpenNormalSubgroup F :=
    openNormalSubgroup_sup_normal (K : Subgroup F) W
  have hxU : x ∉ (U : Subgroup F) := by
    change x ∉ (K : Subgroup F) ⊔ (W : Subgroup F)
    exact hxKW
  let P := F ⧸ (U : Subgroup F)
  let q : F →ₜ* P := OpenNormalSubgroup.quotientProj U
  let N : Subgroup P := R.map q.toMonoidHom
  let _ : N.Normal :=
    (inferInstance : R.Normal).map q.toMonoidHom
      (QuotientGroup.mk'_surjective (U : Subgroup F))
  have hNne : N ≠ ⊥ := by
    intro hNbot
    have hqxN : q x ∈ N := ⟨x, hxR, rfl⟩
    rw [hNbot] at hqxN
    have hqx : q x = 1 := hqxN
    exact hxU ((QuotientGroup.eq_one_iff x).1 hqx)
  have hPclass : FiniteGroupClass.pGroup p P :=
    HasOpenNormalBasisInClass.quotient_mem
      (FiniteGroupClass.pGroup_formation p) hF U
  have hP : IsPGroup p P := hPclass.2
  obtain ⟨χbar, hχbarNe, hχbarInv⟩ :=
    exists_nontrivial_conjugationInvariant_character_finite hP N hNne
  let qR : R →ₜ* N :=
    { toMonoidHom :=
        { toFun := fun r ↦ ⟨q r.1, ⟨r.1, r.2, rfl⟩⟩
          map_one' := Subtype.ext (map_one q)
          map_mul' := fun a b ↦ Subtype.ext (map_mul q a.1 b.1) }
      continuous_toFun :=
        Continuous.subtype_mk
          (q.continuous_toFun.comp continuous_subtype_val)
          (fun r ↦ ⟨r.1, r.2, rfl⟩) }
  have hqRsurj : Function.Surjective qR := by
    intro y
    obtain ⟨x, hxR', hxy⟩ := y.2
    exact ⟨⟨x, hxR'⟩, Subtype.ext hxy⟩
  let χ : R →ₜ* Multiplicative (ZMod p) :=
    { toMonoidHom := χbar.comp qR.toMonoidHom
      continuous_toFun :=
        (continuous_of_discreteTopology : Continuous χbar).comp
          qR.continuous_toFun }
  have hχNe : χ ≠ 1 := by
    intro hχ
    apply hχbarNe
    apply MonoidHom.ext
    intro y
    obtain ⟨r, rfl⟩ := hqRsurj y
    exact DFunLike.congr_fun hχ r
  refine ⟨χ, hχNe, ?_, ?_⟩
  · intro k
    change χbar (qR ⟨k, hKR.le k.2⟩) = 1
    rw [show qR ⟨k, hKR.le k.2⟩ = 1 by
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff k.1).2
        (show k.1 ∈ (K : Subgroup F) ⊔ (W : Subgroup F) from
          (le_sup_left : (K : Subgroup F) ≤
            (K : Subgroup F) ⊔ (W : Subgroup F)) k.2)]
    exact map_one χbar
  · intro f r
    change χbar (qR (MulAut.conjNormal f r)) = χbar (qR r)
    rw [show qR (MulAut.conjNormal f r) =
        MulAut.conjNormal (q f) (qR r) by
      apply Subtype.ext
      change q (f * r.1 * f⁻¹) = q f * q r.1 * (q f)⁻¹
      simp only [map_mul, map_inv]]
    exact hχbarInv (q f) (qR r)

end

end ClassFieldTower.ProP
