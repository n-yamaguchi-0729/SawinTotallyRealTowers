import ProCGroups.ProP.ProfiniteFrattini
import ProCGroups.Generation.QuotientCriteria
import ProCGroups.ProC.Quotients.LeftQuotientMaps

set_option autoImplicit false
/-!
# The pro-p Burnside basis criterion

For a profinite group with an open-normal finite `p`-group basis, a set
topologically generates the group exactly when its image generates the
power--commutator quotient.  This is the topological Burnside basis
criterion, with the Frattini subgroup interpreted through finite continuous
quotients.

The only locally synthesized structure in the main theorem is normality of
the closed power--commutator subgroup.  No quotient algebra or module
instance is exported.
-/

open Set

namespace ClassFieldTower.ProP

universe u

open ProCGroups.Generation

/-- If a set generates a quotient, adjoining the kernel makes it generate the source. -/
theorem topologicallyGenerates_union_normal_of_quotient
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {N : Subgroup G} [N.Normal] {X : Set G}
    (hX : TopologicallyGenerates (G := G ⧸ N) ((QuotientGroup.mk' N) '' X)) :
    TopologicallyGenerates (G := G) (X ∪ (N : Set G)) := by
  apply (topologicallyGenerates_union_subgroup_iff_forall_openNormalQuotient
    (G := G) (N := N) (X := X)).2
  intro U hNU
  let f : (G ⧸ N) →ₜ* (G ⧸ (U : Subgroup G)) :=
    { toMonoidHom := QuotientGroup.map N (U : Subgroup G) (MonoidHom.id G) hNU
      continuous_toFun :=
        ProCGroups.ProC.continuous_leftQuotientProjection N (U : Subgroup G) hNU }
  have hfgen : TopologicallyGenerates (G := G ⧸ (U : Subgroup G))
      (f '' ((QuotientGroup.mk' N) '' X)) :=
    topologicallyGenerates_image_of_continuousSurjective
      f.toMonoidHom f.continuous_toFun
        (ProCGroups.ProC.surjective_leftQuotientProjection N (U : Subgroup G) hNU) hX
  have himage : f '' ((QuotientGroup.mk' N) '' X) =
      (QuotientGroup.mk' (U : Subgroup G)) '' X := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨QuotientGroup.mk' N x, ⟨x, hx, rfl⟩, rfl⟩
  rwa [himage] at hfgen

/-- Over a finite discrete group, adjoining the Frattini subgroup does not help a set
topologically generate. -/
theorem topologicallyGenerates_of_union_frattini_finite
    {Q : Type u} [TopologicalSpace Q] [Group Q] [DiscreteTopology Q] [Finite Q]
    {S : Set Q}
    (hS : TopologicallyGenerates (G := Q) (S ∪ (frattini Q : Set Q))) :
    TopologicallyGenerates (G := Q) S := by
  have hclosure : Subgroup.closure (S ∪ (frattini Q : Set Q)) = ⊤ := by
    simpa [TopologicallyGenerates] using hS
  have hsup : Subgroup.closure S ⊔ frattini Q = ⊤ := by
    simpa [Subgroup.closure_union] using hclosure
  have htop : Subgroup.closure S = ⊤ := frattini_nongenerating hsup
  simp [TopologicallyGenerates, htop]

/-- The pro-`p` Burnside basis criterion: topological generation is detected by the
power--commutator quotient. -/
theorem topologicallyGenerates_iff_powerCommutatorQuotient_image
    {p : ℕ} {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Fact (Nat.Prime p)]
    (hG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G) {X : Set G} :
    letI : (closedPowerCommutator p G).Normal := closedPowerCommutator_normal p G
    TopologicallyGenerates (G := G) X ↔
      TopologicallyGenerates (G := powerCommutatorQuotient p G)
        ((powerCommutatorQuotientMk p G) '' X) := by
  let _ : (closedPowerCommutator p G).Normal := closedPowerCommutator_normal p G
  constructor
  · exact topologicallyGenerates_quotient_image
      (closedPowerCommutator p G)
  · intro hX
    have hXcore : TopologicallyGenerates (G := G)
        (X ∪ (closedPowerCommutator p G : Set G)) :=
      topologicallyGenerates_union_normal_of_quotient hX
    apply (topologicallyGenerates_iff_forall_quotientProj_image (G := G)).2
    intro U
    have hQU := ProCGroups.ProC.HasOpenNormalBasisInClass.quotient_mem
      (ProCGroups.FiniteGroupClass.pGroup_formation p) hG U
    have hgenUnion := topologicallyGenerates_quotient_image
      (U : Subgroup G) hXcore
    have hsubset :
        (QuotientGroup.mk' (U : Subgroup G)) ''
            (X ∪ (closedPowerCommutator p G : Set G)) ⊆
          ((QuotientGroup.mk' (U : Subgroup G)) '' X) ∪
            (frattini (G ⧸ (U : Subgroup G)) : Set (G ⧸ (U : Subgroup G))) := by
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with hx | hx
      · exact Or.inl ⟨x, hx, rfl⟩
      · apply Or.inr
        rw [frattini_eq_closedPowerCommutator_of_isPGroup hQU.2]
        exact closedPowerCommutator_map_le p G
          (ProCGroups.ProC.OpenNormalSubgroup.quotientProj U) ⟨x, hx, rfl⟩
    have hgenWithFrattini :
        TopologicallyGenerates (G := G ⧸ (U : Subgroup G))
          (((QuotientGroup.mk' (U : Subgroup G)) '' X) ∪
            (frattini (G ⧸ (U : Subgroup G)) : Set (G ⧸ (U : Subgroup G)))) :=
      topologicallyGenerates_mono hgenUnion hsubset
    exact topologicallyGenerates_of_union_frattini_finite hgenWithFrattini

end ClassFieldTower.ProP
