/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.FiniteIndexTransfer
import GaloisCohomology.ProP.H2CocycleExtensionPullback
import GaloisCohomology.ProP.H2CocycleExtensionLiftDifference
import GaloisCohomology.ProP.H2CocycleExtensionKernelCharacter

set_option autoImplicit false
/-!
# Prime-to-index injectivity of continuous degree-two restriction

Vanishing on an open finite-index subgroup supplies a continuous lift to the cocycle
extension. The difference between this lift and the inclusion gives a coefficient character
on the preimage subgroup. Its continuous transfer is multiplication by the index on the
central kernel. Inverting that index in `ZMod p` constructs a global splitting character.

This proves injectivity without a cohomological corestriction package, finite-stage descent,
or a normality assumption. The only local instances record local compactness of the closed
subgroup and the finite index of its preimage under a surjective projection.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CategoryTheory TopRep ContRepresentation FreeProPH2Cocycle

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- A class whose restriction vanishes is zero when the subgroup index is prime to `p`.
The global splitting character is constructed by transferring the difference of two actual
lifts, then dividing its central-kernel value by the subgroup index. -/
theorem H2CocycleExtension.π_eq_zero_of_restriction_of_index_not_dvd
    (H : OpenSubgroup G)
    (hindex : ¬ p ∣ H.toSubgroup.index)
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (hz : (Cohomology.continuousCohomologyZModPMapLifted p
      (Cohomology.subgroupInclusion H.toSubgroup) 2).hom
      (ContinuousCohomology.π (Cohomology.trivialZModPLifted p G) 2 z) = 0) :
    ContinuousCohomology.π (Cohomology.trivialZModPLifted p G) 2 z = 0 := by
  let : H.toSubgroup.FiniteIndex :=
    ⟨fun hzero => hindex (by rw [hzero]; exact dvd_zero p)⟩
  let : LocallyCompactSpace H := H.isClosed.locallyCompactSpace
  obtain ⟨s, hs⟩ := H2CocycleExtension.exists_lift_of_restriction_eq_zero
    (Cohomology.subgroupInclusion H.toSubgroup) z hz
  let E := H2CocycleExtension z
  let EH : OpenSubgroup E := H.comap (H2CocycleExtension.projection z).toMonoidHom
    (H2CocycleExtension.projection z).continuous_toFun
  let q : EH →ₜ* H :=
    { toFun := fun e => ⟨e.1.right, e.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun := Continuous.subtype_mk
        ((H2CocycleExtension.projection z).continuous_toFun.comp continuous_subtype_val) _ }
  let i : EH →ₜ* E := Cohomology.subgroupInclusion EH.toSubgroup
  have hst : (H2CocycleExtension.projection z).comp i =
      (H2CocycleExtension.projection z).comp (s.comp q) := by
    ext e
    exact (DFunLike.congr_fun hs (q e)).symm
  let φ := H2CocycleExtension.liftDifference z i (s.comp q) hst
  have hidx : EH.toSubgroup.index = H.toSubgroup.index :=
    H.toSubgroup.index_comap_of_surjective (H2CocycleExtension.projection_surjective z)
  let : EH.toSubgroup.FiniteIndex :=
    ⟨by rw [hidx]; exact H.toSubgroup.index_ne_zero_of_finite⟩
  let T : E →ₜ* Multiplicative (ZMod p) := Cohomology.openSubgroupTransfer EH φ
  have hφ (a : A p) : φ ⟨⟨a, 1⟩, H.one_mem⟩ = Multiplicative.ofAdd a.down := by
    change Multiplicative.ofAdd (a.down - (s 1).left.down) = Multiplicative.ofAdd a.down
    rw [map_one]
    change Multiplicative.ofAdd (a.down - 0) = Multiplicative.ofAdd a.down
    rw [sub_zero]
  have hT (a : A p) : T ⟨a, 1⟩ = (Multiplicative.ofAdd a.down) ^ H.toSubgroup.index := by
    let x : EH := ⟨⟨a, 1⟩, H.one_mem⟩
    have hc : (x : E) ∈ Subgroup.center E :=
      H2CocycleExtension.kernel_le_center z rfl
    have hkey (k : ℕ) (g₀ : E) (_hg : g₀⁻¹ * (x : E) ^ k * g₀ ∈ EH.toSubgroup) :
        g₀⁻¹ * (x : E) ^ k * g₀ = (x : E) ^ k := by
      have hcomm := Subgroup.mem_center_iff.mp ((Subgroup.center E).pow_mem hc k) g₀
      rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    calc
      T ⟨a, 1⟩ = φ (x ^ EH.toSubgroup.index) :=
        MonoidHom.transfer_eq_pow φ.toMonoidHom (x : E) hkey
      _ = (Multiplicative.ofAdd a.down) ^ H.toSubgroup.index := by
        rw [map_pow, hidx]
        exact congrArg (fun y => y ^ H.toSubgroup.index) (hφ a)
  have hTadd (a : A p) : (T ⟨a, 1⟩).toAdd =
      (H.toSubgroup.index : ZMod p) * a.down := by
    rw [hT]
    simp
  let χ : E →ₜ* Multiplicative (ZMod p) :=
    { toFun := fun e => Multiplicative.ofAdd
        ((H.toSubgroup.index : ZMod p)⁻¹ * (T e).toAdd)
      map_one' := by simp
      map_mul' := by
        intro x y
        change (H.toSubgroup.index : ZMod p)⁻¹ * (T (x * y)).toAdd = _
        rw [map_mul]
        exact mul_add _ _ _
      continuous_toFun := by
        change Continuous fun e => (H.toSubgroup.index : ZMod p)⁻¹ * (T e).toAdd
        exact continuous_const.mul T.continuous_toFun }
  apply H2CocycleExtension.π_eq_zero_of_kernelCharacter z χ
  intro a
  apply Multiplicative.toAdd.injective
  change (H.toSubgroup.index : ZMod p)⁻¹ * (T ⟨a, 1⟩).toAdd = a.down
  have hn : (H.toSubgroup.index : ZMod p) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff H.toSubgroup.index p).not.mpr hindex
  rw [hTadd, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- Restriction of continuous trivial-coefficient `H²` is injective for an open subgroup of
index prime to `p`. Normality is not required. -/
theorem continuousH2Restriction_injective_of_index_not_dvd
    (H : OpenSubgroup G)
    (hindex : ¬ p ∣ H.toSubgroup.index) :
    Function.Injective (Cohomology.continuousCohomologyZModPMapLifted p
      (Cohomology.subgroupInclusion H.toSubgroup) 2).hom := by
  intro x y hxy
  have hzero : (Cohomology.continuousCohomologyZModPMapLifted p
      (Cohomology.subgroupInclusion H.toSubgroup) 2).hom (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := PresentationH2Aux.homologyπ_surjective
    (Cohomology.trivialZModPLifted p G) 2 (x - y)
  have hz0 := H2CocycleExtension.π_eq_zero_of_restriction_of_index_not_dvd H hindex z
    (by rw [hz]; exact hzero)
  exact sub_eq_zero.mp (hz.symm.trans hz0)

end
end ClassFieldTower.ProP
