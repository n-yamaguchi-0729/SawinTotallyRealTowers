import ProCGroups.FiniteGroups.StandardClasses

set_option autoImplicit false
/-!
# Maximal subgroups of finite p-groups

This file proves the finite-group source needed for the Burnside basis theorem:
a maximal subgroup of a finite `p`-group is normal, and its quotient has order
exactly `p`.
-/

namespace ClassFieldTower.ProP

universe u

/-- Every maximal subgroup of a finite `p`-group is normal. -/
theorem isCoatom_normal_of_isPGroup
    {p : ℕ} {G : Type u} [Group G] [Finite G] [Fact (Nat.Prime p)]
    (hG : IsPGroup p G) {M : Subgroup G} (hM : IsCoatom M) :
    M.Normal := by
  exact ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 2 rfl rfl).mp
    hG.isNilpotent M hM

/-- A quotient by a maximal normal subgroup has no nontrivial proper subgroups. -/
theorem quotient_subgroup_eq_bot_or_eq_top_of_isCoatom
    {G : Type u} [Group G] {M : Subgroup G} [M.Normal]
    (hM : IsCoatom M) (K : Subgroup (G ⧸ M)) :
    K = ⊥ ∨ K = ⊤ := by
  have hle : M ≤ K.comap (QuotientGroup.mk' M) :=
    QuotientGroup.le_comap_mk' M K
  by_cases htop : K.comap (QuotientGroup.mk' M) = ⊤
  · right
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
    simpa using htop
  · left
    have heq : K.comap (QuotientGroup.mk' M) = M :=
      (hM.le_iff_eq htop).mp hle
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
    simpa using heq

/-- The quotient by a maximal normal subgroup is nontrivial. -/
theorem quotient_nontrivial_of_isCoatom
    {G : Type u} [Group G] {M : Subgroup G} [M.Normal]
    (hM : IsCoatom M) :
    Nontrivial (G ⧸ M) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro h
  exact hM.ne_top (QuotientGroup.subgroup_eq_top_of_subsingleton M h)

/-- The quotient by a maximal normal subgroup is cyclic. -/
theorem quotient_isCyclic_of_isCoatom
    {G : Type u} [Group G] {M : Subgroup G} [M.Normal]
    (hM : IsCoatom M) :
    IsCyclic (G ⧸ M) := by
  let _ : Nontrivial (G ⧸ M) := quotient_nontrivial_of_isCoatom hM
  obtain ⟨g, hg⟩ := exists_ne (1 : G ⧸ M)
  have htop : Subgroup.zpowers g = ⊤ :=
    (quotient_subgroup_eq_bot_or_eq_top_of_isCoatom hM (Subgroup.zpowers g)).resolve_left
      (Subgroup.zpowers_ne_bot.2 hg)
  exact ⟨⟨g, (Subgroup.eq_top_iff' _).1 htop⟩⟩

/-- The quotient by a maximal normal subgroup is a simple group. -/
theorem quotient_isSimpleGroup_of_isCoatom
    {G : Type u} [Group G] {M : Subgroup G} [M.Normal]
    (hM : IsCoatom M) :
    IsSimpleGroup (G ⧸ M) := by
  let _ : Nontrivial (G ⧸ M) := quotient_nontrivial_of_isCoatom hM
  exact ⟨fun K _ => quotient_subgroup_eq_bot_or_eq_top_of_isCoatom hM K⟩

/-- A maximal-subgroup quotient of a finite `p`-group has cardinality `p`. -/
theorem card_quotient_eq_prime_of_isCoatom_isPGroup
    {p : ℕ} {G : Type u} [Group G] [Finite G] [hp : Fact (Nat.Prime p)]
    (hG : IsPGroup p G) {M : Subgroup G} (hM : IsCoatom M) :
    Nat.card (G ⧸ M) = p := by
  let : M.Normal := isCoatom_normal_of_isPGroup hG hM
  let _ : Nontrivial (G ⧸ M) := quotient_nontrivial_of_isCoatom hM
  let : IsCyclic (G ⧸ M) := quotient_isCyclic_of_isCoatom hM
  let : IsMulCommutative (G ⧸ M) := inferInstance
  let : IsSimpleGroup (G ⧸ M) := quotient_isSimpleGroup_of_isCoatom hM
  have hcardPrime : Nat.Prime (Nat.card (G ⧸ M)) :=
    Group.is_simple_iff_prime_card.mp (inferInstance : IsSimpleGroup (G ⧸ M))
  have hQ : IsPGroup p (G ⧸ M) := hG.to_quotient M
  have hcard_ne_one : Nat.card (G ⧸ M) ≠ 1 := by
    intro h
    exact not_subsingleton (G ⧸ M) (Nat.card_eq_one_iff_unique.mp h).1
  have hp_dvd : p ∣ Nat.card (G ⧸ M) :=
    (hQ.card_eq_or_dvd).resolve_left hcard_ne_one
  exact (hcardPrime.dvd_iff_eq hp.out.ne_one).mp hp_dvd

end ClassFieldTower.ProP
