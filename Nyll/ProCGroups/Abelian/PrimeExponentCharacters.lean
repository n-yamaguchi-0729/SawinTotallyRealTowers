/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Topology.Instances.ZMod
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Nyll.ProCGroups.ProC.Quotients.ClosedNormal
import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
import Nyll.ProCGroups.Abelian.AbelianModPower

/-!
# Prime-exponent characters detect abelian classes

Continuous characters with values in `ZMod q` separate profinite commutative
groups of exponent `q`. In particular, simultaneous extension of characters
forces the product map on abelianizations modulo `q` to be injective.
-/

namespace ProCGroups.Abelian

variable {q : ℕ} [Fact q.Prime]

/-- A nonidentity element of a finite commutative group of prime exponent
is detected by a character with values in that prime cyclic group. -/
theorem exists_prime_character_finite
    {A : Type*} [CommGroup A] [Finite A]
    (hA : ∀ a : A, a ^ q = 1) {x : A} (hx : x ≠ 1) :
    ∃ χ : A →* Multiplicative (ZMod q), χ x ≠ 1 := by
  classical
  obtain ⟨ι, instι, m, hm, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  have hcoord : ∃ i : ι, e x i ≠ 1 := by
    by_contra! h
    apply hx
    apply e.injective
    rw [map_one]
    exact funext h
  obtain ⟨i, hi⟩ := hcoord
  let ψ : A →* Multiplicative (ZMod (m i)) :=
    (Pi.evalMonoidHom (fun j : ι => Multiplicative (ZMod (m j))) i).comp e.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro a
    refine ⟨e.symm (Function.update 1 i a), ?_⟩
    change e (e.symm (Function.update 1 i a)) i = a
    rw [e.apply_symm_apply, Function.update_self]
  have hmdiv : m i ∣ q := by
    obtain ⟨a, ha⟩ := hψ (Multiplicative.ofAdd (1 : ZMod (m i)))
    have hp : (Multiplicative.ofAdd (1 : ZMod (m i))) ^ q = 1 := by
      rw [← ha, ← map_pow, hA, map_one]
    apply (ZMod.natCast_eq_zero_iff q (m i)).mp
    have h := congrArg Multiplicative.toAdd hp
    change q • (1 : ZMod (m i)) = 0 at h
    simpa only [nsmul_eq_mul, mul_one] using h
  have hmi : m i = q := ((Nat.dvd_prime (Fact.out : q.Prime)).mp hmdiv).resolve_left
    (Nat.ne_of_gt (hm i))
  let ec := (ZMod.ringEquivCongr hmi).toAddEquiv.toMultiplicative
  refine ⟨ec.toMonoidHom.comp ψ, ?_⟩
  intro hχ
  apply hi
  apply ec.injective
  exact hχ.trans (map_one ec).symm

/-- Prime cyclic characters separate a profinite commutative group
of prime exponent. -/
theorem exists_prime_character_profinite
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    (hA : ∀ a : A, a ^ q = 1) {x : A} (hx : x ≠ 1) :
    ∃ χ : A →ₜ* Multiplicative (ZMod q), χ x ≠ 1 := by
  obtain ⟨U, hU⟩ := ProCGroups.ProC.exists_openNormalSubgroup_not_mem hx
  have hquot : ∀ a : A ⧸ (U : Subgroup A), a ^ q = 1 := by
    intro a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup A) a
    rw [← map_pow, hA, map_one]
  have hxquot : QuotientGroup.mk' (U : Subgroup A) x ≠ 1 := by
    intro h
    exact hU ((QuotientGroup.eq_one_iff (N := (U : Subgroup A)) x).mp h)
  obtain ⟨χ, hχ⟩ := exists_prime_character_finite hquot hxquot
  let χcont : (A ⧸ (U : Subgroup A)) →ₜ* Multiplicative (ZMod q) :=
    ⟨χ, continuous_of_discreteTopology⟩
  exact ⟨χcont.comp (ProC.OpenNormalSubgroup.quotientProj U), hχ⟩

/-- Prime cyclic characters separate the quotient of a profinite group
by commutators and prime powers. -/
theorem exists_prime_character_abelianModPower
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {x : abelianModPower G q} (hx : x ≠ 1) :
    ∃ χ : abelianModPower G q →ₜ* Multiplicative (ZMod q), χ x ≠ 1 := by
  let B := TopologicalAbelianization G
  let P : Subgroup B := (powMonoidHom (α := B) q).range
  have : TotallyDisconnectedSpace B :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator G) (Subgroup.isClosed_closedCommutator G)
  let powerMap : B →ₜ* B := ⟨powMonoidHom q, continuous_id.pow _⟩
  have hP : IsClosed (P : Set B) := ContinuousMonoidHom.isClosed_range powerMap
  have : IsClosed (P : Set B) := hP
  have : TotallyDisconnectedSpace (B ⧸ P) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal P hP
  have hpow : ∀ z : B ⧸ P, z ^ q = 1 := by
    intro z
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective P z
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := P) _).mpr ⟨a, rfl⟩
  exact exists_prime_character_profinite hpow hx

/-- If every tuple of prime cyclic characters extends to the ambient group,
the product of the induced maps on abelianizations modulo that prime is injective. -/
theorem injective_prod_abelianModPowerMap_of_character_surjective
    {ι : Type*} [Fintype ι]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : ι → Type*) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, CompactSpace (H i)]
    [∀ i, T2Space (H i)] [∀ i, TotallyDisconnectedSpace (H i)]
    (f : ∀ i, H i →ₜ* G)
    (hchar : Function.Surjective (fun χ : G →ₜ* Multiplicative (ZMod q) =>
      fun i => χ.comp (f i))) :
    Function.Injective (fun z : ∀ i, abelianModPower (H i) q =>
      ∏ i, abelianModPowerMap q (f i) (z i)) := by
  classical
  have hpow : ∀ a : Multiplicative (ZMod q), a ^ q = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    change q • a.toAdd = (0 : ZMod q)
    simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hker : ∀ z : (∀ i, abelianModPower (H i) q),
      (∏ i, abelianModPowerMap q (f i) (z i)) = 1 → z = 1 := by
    intro z hz
    funext i
    by_contra hzi
    obtain ⟨χi, hχi⟩ := exists_prime_character_abelianModPower hzi
    let ψ : ∀ j, H j →ₜ* Multiplicative (ZMod q) :=
      Function.update 1 i (χi.comp (abelianModPowerMk (H i) q))
    obtain ⟨χ, hχ⟩ := hchar ψ
    let χbar := abelianModPowerLift q χ hpow
    have hi : χbar (abelianModPowerMap q (f i) (z i)) = χi (z i) := by
      obtain ⟨a, ha⟩ := abelianModPowerMk_surjective (G := H i) q (z i)
      rw [← ha]
      change χ (f i a) = χi (abelianModPowerMk (H i) q a)
      have h := DFunLike.congr_fun (congrFun hχ i) a
      simp only [ψ, Function.update_self] at h
      exact h
    have hj (j : ι) (hji : j ≠ i) : χbar (abelianModPowerMap q (f j) (z j)) = 1 := by
      obtain ⟨a, ha⟩ := abelianModPowerMk_surjective (G := H j) q (z j)
      rw [← ha]
      change χ (f j a) = 1
      have h := DFunLike.congr_fun (congrFun hχ j) a
      simp only [ψ, Function.update_of_ne hji, Pi.one_apply] at h
      exact h
    have hprod : (∏ j, χbar (abelianModPowerMap q (f j) (z j))) = χi (z i) := by
      rw [Finset.prod_eq_single i]
      · exact hi
      · intro j _ hji
        exact hj j hji
      · intro h
        exact False.elim (h (Finset.mem_univ i))
    apply hχi
    rw [← hprod, ← map_prod, hz, map_one]
  intro x y hxy
  have hdiv : (∏ i, abelianModPowerMap q (f i) ((x / y) i)) = 1 := by
    change (∏ i, abelianModPowerMap q (f i) (x i / y i)) = 1
    simp only [map_div, Finset.prod_div_distrib]
    exact div_eq_one.mpr hxy
  exact div_eq_one.mp (hker (x / y) hdiv)

end ProCGroups.Abelian
