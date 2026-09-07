import ProCGroups.ProP.FiniteFrattini
import ProCGroups.ProC.InverseLimits.Predicates
import ProCGroups.ProC.OpenNormalSubgroups.Separation

set_option autoImplicit false
/-!
# The Frattini subgroup of a pro-p group

This file defines the profinite Frattini subgroup by detection in every open
normal finite quotient.  For a group with an open-normal finite `p`-group
basis, it proves the pro-`p` formula

`profiniteFrattini G = closedPowerCommutator p G`.

The proof reuses the finite Burnside--Frattini formula quotient by quotient.
No commutative-group or module structure is exported from this file.
-/

open Set

namespace ClassFieldTower.ProP

universe u v

/-- A surjective homomorphism realizes every target `p`-power inside the image of the source
`p`-power subgroup. -/
theorem powerSubgroup_le_map_of_surjective
    {p : ℕ} {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    powerSubgroup p H ≤ (powerSubgroup p G).map f := by
  rw [powerSubgroup, Subgroup.closure_le]
  rintro _ ⟨h, rfl⟩
  obtain ⟨g, rfl⟩ := hf h
  exact ⟨g ^ p, pow_mem_powerSubgroup p G g, map_pow f g p⟩

/-- A surjective homomorphism realizes the target commutator subgroup inside the image of the
source commutator subgroup. -/
theorem commutator_le_map_of_surjective
    {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    commutator H ≤ (commutator G).map f := by
  rw [_root_.map_commutator_eq]
  have hrange : f.range = (⊤ : Subgroup H) := by
    apply top_unique
    intro h _
    obtain ⟨g, rfl⟩ := hf h
    exact ⟨g, rfl⟩
  rw [hrange]
  exact le_rfl

/-- Over a finite Hausdorff target, a surjective continuous homomorphism maps the closed
power--commutator subgroup onto the target one, reverse-inclusion direction. -/
theorem closedPowerCommutator_le_map_of_surjective_finite
    {p : ℕ} {G : Type u} {H : Type v}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace H] [Group H] [IsTopologicalGroup H] [T1Space H] [Finite H]
    (f : G →ₜ* H) (hf : Function.Surjective f) :
    closedPowerCommutator p H ≤
      (closedPowerCommutator p G).map f.toMonoidHom := by
  rw [closedPowerCommutator]
  apply Subgroup.topologicalClosure_minimal
  · apply sup_le
    · exact (powerSubgroup_le_map_of_surjective f.toMonoidHom hf).trans
        (Subgroup.map_mono (powerSubgroup_le_closedPowerCommutator p G))
    · exact (commutator_le_map_of_surjective f.toMonoidHom hf).trans
        (Subgroup.map_mono (commutator_le_closedPowerCommutator p G))
  · exact ((closedPowerCommutator p G).map f.toMonoidHom : Set H).toFinite.isClosed

/-- A surjective continuous homomorphism onto a finite Hausdorff group maps the closed
power--commutator subgroup exactly onto the target one. -/
theorem closedPowerCommutator_map_eq_of_surjective_finite
    {p : ℕ} {G : Type u} {H : Type v}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace H] [Group H] [IsTopologicalGroup H] [T1Space H] [Finite H]
    (f : G →ₜ* H) (hf : Function.Surjective f) :
    (closedPowerCommutator p G).map f.toMonoidHom =
      closedPowerCommutator p H :=
  le_antisymm (closedPowerCommutator_map_le p G f)
    (closedPowerCommutator_le_map_of_surjective_finite f hf)

/-- The profinite Frattini subgroup, detected in every open normal finite quotient. -/
def profiniteFrattini
    (G : Type u) [TopologicalSpace G] [Group G] : Subgroup G :=
  ⨅ U : OpenNormalSubgroup G,
    (frattini (G ⧸ (U : Subgroup G))).comap (QuotientGroup.mk' (U : Subgroup G))

/-- Membership in the profinite Frattini subgroup is membership in the Frattini subgroup after
every open normal quotient projection. -/
theorem mem_profiniteFrattini_iff
    {G : Type u} [TopologicalSpace G] [Group G] {x : G} :
    x ∈ profiniteFrattini G ↔
      ∀ U : OpenNormalSubgroup G,
        QuotientGroup.mk' (U : Subgroup G) x ∈ frattini (G ⧸ (U : Subgroup G)) := by
  simp [profiniteFrattini, Subgroup.mem_iInf]

/-- In a pro-`p` group, the closed power--commutator subgroup lies in the profinite Frattini
subgroup. -/
theorem closedPowerCommutator_le_profiniteFrattini
    {p : ℕ} {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Fact (Nat.Prime p)]
    (hG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G) :
    closedPowerCommutator p G ≤ profiniteFrattini G := by
  rw [profiniteFrattini]
  refine le_iInf fun U ↦ ?_
  intro x hx
  have hQU := ProCGroups.ProC.HasOpenNormalBasisInClass.quotient_mem
    (ProCGroups.FiniteGroupClass.pGroup_formation p) hG U
  rw [frattini_eq_closedPowerCommutator_of_isPGroup hQU.2]
  exact closedPowerCommutator_map_le p G
    (ProCGroups.ProC.OpenNormalSubgroup.quotientProj U) ⟨x, hx, rfl⟩

/-- In a pro-`p` group, finite-quotient Frattini detection gives no elements beyond the closed
power--commutator subgroup. -/
theorem profiniteFrattini_le_closedPowerCommutator
    {p : ℕ} {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Fact (Nat.Prime p)]
    (hG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G) :
    profiniteFrattini G ≤ closedPowerCommutator p G := by
  intro x hx
  apply (ProCGroups.mem_closed_iff_forall_openNormal_quotient
    (isClosed_closedPowerCommutator p G)).2
  intro U
  have hxU := (mem_profiniteFrattini_iff (G := G) (x := x)).mp hx U
  have hQU := ProCGroups.ProC.HasOpenNormalBasisInClass.quotient_mem
    (ProCGroups.FiniteGroupClass.pGroup_formation p) hG U
  rw [frattini_eq_closedPowerCommutator_of_isPGroup hQU.2] at hxU
  rcases closedPowerCommutator_le_map_of_surjective_finite
      (p := p) (ProCGroups.ProC.OpenNormalSubgroup.quotientProj U)
      (ProCGroups.ProC.OpenNormalSubgroup.quotientProj_surjective U) hxU with
    ⟨y, hy, hyx⟩
  exact ⟨y, hy, hyx⟩

/-- The pro-`p` Burnside--Frattini formula. -/
theorem profiniteFrattini_eq_closedPowerCommutator
    {p : ℕ} {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Fact (Nat.Prime p)]
    (hG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G) :
    profiniteFrattini G = closedPowerCommutator p G := by
  exact le_antisymm (profiniteFrattini_le_closedPowerCommutator hG)
    (closedPowerCommutator_le_profiniteFrattini hG)

end ClassFieldTower.ProP
