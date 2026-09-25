/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2CentralExtensionClass
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

set_option autoImplicit false
/-!
# Prime central extensions and the Frattini subgroup

A surjection with kernel of prime order can split only if its kernel is not
contained in the Frattini subgroup.  Applied to the cocycle extension of a
nonzero degree-two class, this identifies the coefficient kernel as a cyclic
Frattini obstruction.
-/

open scoped Topology

noncomputable section

namespace ClassFieldTower.ProP

open ClassFieldTower.Cohomology

universe u v

variable {E : Type u} {Q : Type v} [Group E] [Group Q]
variable {p : ℕ} [Fact p.Prime]

/-- A nonsplit surjection whose kernel has prime cardinality has its entire
kernel in the Frattini subgroup of the source. -/
theorem ker_le_frattini_of_no_section_of_prime_card
    (f : E →* Q) (hf : Function.Surjective f)
    (hcard : Nat.card f.ker = p)
    (hno : ¬ ∃ s : Q →* E, f.comp s = MonoidHom.id Q) :
    f.ker ≤ frattini E := by
  by_contra hle
  obtain ⟨k, hkker, hkfr⟩ := SetLike.not_le_iff_exists.mp hle
  have hkcoatom : ∃ M : Subgroup E, IsCoatom M ∧ k ∉ M := by
    have h := hkfr
    simp only [frattini, Order.radical, Subgroup.mem_iInf,
      Set.mem_ofPred_eq, not_forall] at h
    obtain ⟨M, hM, hkM⟩ := h
    exact ⟨M, hM, hkM⟩
  obtain ⟨M, hM, hkM⟩ := hkcoatom
  have hMsup : M ⊔ f.ker = ⊤ := by
    apply hM.lt_iff.mp
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    exact hkM (hEq.symm ▸
      ((le_sup_right : f.ker ≤ M ⊔ f.ker) hkker))
  have hmapM : M.map f = ⊤ := by
    have hmap := congrArg (fun H : Subgroup E => H.map f) hMsup
    simp only [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq,
      Subgroup.map_top_of_surjective f hf] at hmap
    exact hmap
  have hresSurj : Function.Surjective (f.domRestrict M) := by
    intro q
    have hq : q ∈ M.map f := by
      rw [hmapM]
      exact Subgroup.mem_top q
    obtain ⟨e, heM, heq⟩ := hq
    exact ⟨⟨e, heM⟩, heq⟩
  have hresInj : Function.Injective (f.domRestrict M) := by
    intro a b hab
    apply Subtype.ext
    have hdiffKer : a.1 * b.1⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      change f a.1 = f b.1 at hab
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hdiffM : a.1 * b.1⁻¹ ∈ M :=
      M.mul_mem a.2 (M.inv_mem b.2)
    have hdiffOne : a.1 * b.1⁻¹ = 1 := by
      by_contra hne
      let d : f.ker := ⟨a.1 * b.1⁻¹, hdiffKer⟩
      let k' : f.ker := ⟨k, hkker⟩
      have hdne : d ≠ 1 := by
        intro hd
        exact hne (congrArg Subtype.val hd)
      have hkpow : k' ∈ Subgroup.zpowers d :=
        mem_zpowers_of_prime_card hcard hdne
      exact hkM (by
        rcases hkpow with ⟨n, hn⟩
        have hnval : d.1 ^ n = k'.1 := congrArg Subtype.val hn
        have hmem : d.1 ^ n ∈ M := M.zpow_mem hdiffM n
        rw [hnval] at hmem
        exact hmem)
    exact mul_inv_eq_one.mp hdiffOne
  let e : M ≃* Q :=
    MulEquiv.ofBijective (f.domRestrict M) ⟨hresInj, hresSurj⟩
  let s : Q →* E := M.subtype.comp e.symm.toMonoidHom
  apply hno
  refine ⟨s, ?_⟩
  ext q
  exact e.apply_symm_apply q

/-- The coefficient kernel of the explicit degree-two cocycle extension has
cardinality `p`. -/
theorem degreeTwoCentralExtension_kernel_card
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (x : continuousCohomologyZModPLifted p Q 2) :
    Nat.card
      (H2CocycleExtension.projection
        (degreeTwoCocycleRepresentative x)).ker = p := by
  rw [Nat.card_congr
    (H2CocycleExtension.kernelMulEquiv
      (degreeTwoCocycleRepresentative x)).toEquiv]
  simp [FreeProPH2Cocycle.A]

/-- The coefficient kernel of the explicit degree-two cocycle extension is
cyclic. -/
theorem degreeTwoCentralExtension_kernel_isCyclic
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (x : continuousCohomologyZModPLifted p Q 2) :
    IsCyclic
      (H2CocycleExtension.projection
        (degreeTwoCocycleRepresentative x)).ker :=
  isCyclic_of_prime_card (degreeTwoCentralExtension_kernel_card x)

/-- For a nonzero degree-two class on a discrete group, the cyclic
coefficient kernel of its explicit nonsplit extension lies in the Frattini
subgroup. -/
theorem degreeTwoCentralExtension_kernel_le_frattini_of_ne_zero
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [DiscreteTopology Q] [LocallyCompactSpace Q]
    {x : continuousCohomologyZModPLifted p Q 2}
    (hx : x ≠ 0) :
    (H2CocycleExtension.projection
        (degreeTwoCocycleRepresentative x)).ker ≤
      frattini (DegreeTwoCentralExtension x) := by
  let f := H2CocycleExtension.projection
    (degreeTwoCocycleRepresentative x)
  apply ker_le_frattini_of_no_section_of_prime_card f.toMonoidHom
    (H2CocycleExtension.projection_surjective
      (degreeTwoCocycleRepresentative x))
    (degreeTwoCentralExtension_kernel_card x)
  intro hsection
  apply degreeTwoCentralExtension_no_section_of_ne_zero hx
  obtain ⟨s, hs⟩ := hsection
  let s' : Q →ₜ* DegreeTwoCentralExtension x :=
    ContinuousMonoidHom.mk s continuous_of_discreteTopology
  refine ⟨s', ?_⟩
  ext q
  exact DFunLike.congr_fun hs q

end ClassFieldTower.ProP
