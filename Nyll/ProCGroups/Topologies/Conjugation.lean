/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.GroupTheory.Conjugation
import Nyll.ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

/-!
# Continuous conjugation actions

This file bundles conjugation by a normalizing element as a continuous multiplicative
equivalence. It also descends conjugation to quotients by topologically characteristic
subgroups and records the formula on quotient representatives.
-/

open scoped Topology

namespace ProCGroups

namespace Subgroup

universe u

/-- Conjugation by an ambient element as a continuous automorphism of a normal subgroup. -/
noncomputable def conjNormalContinuousMulEquiv
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (g : G) : N ≃ₜ* N :=
  { toMulEquiv := MulAut.conjNormal g
    continuous_toFun := by
      apply Continuous.subtype_mk
      change Continuous fun x : N => g * (x : G) * g⁻¹
      exact
        ((continuous_const : Continuous fun _ : N => g).mul continuous_subtype_val).mul
          (continuous_const : Continuous fun _ : N => g⁻¹)
    continuous_invFun := by
      apply Continuous.subtype_mk
      change Continuous fun x : N => g⁻¹ * (x : G) * (g⁻¹)⁻¹
      exact
        ((continuous_const : Continuous fun _ : N => g⁻¹).mul continuous_subtype_val).mul
          (continuous_const : Continuous fun _ : N => (g⁻¹)⁻¹) }

/-- The conjugation equivalence is evaluated by conjugating representatives. -/
@[simp] theorem conjNormalContinuousMulEquiv_apply
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (g : G) (x : N) :
    conjNormalContinuousMulEquiv N g x = MulAut.conjNormal g x :=
  rfl

end Subgroup

end ProCGroups

namespace ProCGroups.Topologies

universe u

/--
Topological variant of
\(\mathrm{ProCGroups.GroupTheory.quotientConjugationOnCharacteristicQuotient}\). It only needs
\(K\) to be preserved by continuous automorphisms, since the conjugation maps used to define the
action are continuous.
-/
noncomputable def quotientConjugationOnTopologicallyCharacteristicQuotient
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (K : Subgroup N) [K.TopologicallyCharacteristic]
    (hNactsTrivially :
      ∀ n x : N, (((MulAut.conjNormal (n : G)) x) * x⁻¹ : N) ∈ K) :
    (G ⧸ N) →* MulAut (N ⧸ K) := by
  let prequotientAction : G →* MulAut (N ⧸ K) :=
    { toFun := fun g =>
        (inferInstance : K.TopologicallyCharacteristic).quotientMulEquiv
          (Subgroup.conjNormalContinuousMulEquiv (G := G) N g)
      map_one' := by
        ext a
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K a
        simp only [Subgroup.TopologicallyCharacteristic.quotientMulEquiv_mk,
          Subgroup.conjNormalContinuousMulEquiv_apply, map_one, MulAut.one_apply]
      map_mul' := by
        intro g h
        ext a
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K a
        simp only [MulAut.mul_apply,
          Subgroup.TopologicallyCharacteristic.quotientMulEquiv_mk]
        apply congrArg (QuotientGroup.mk' K)
        simpa only [Subgroup.conjNormalContinuousMulEquiv_apply, MulAut.mul_apply] using
          congrArg (fun e : MulAut N => e x)
            (map_mul (MulAut.conjNormal (H := N)) g h) }
  have hNker : N ≤ prequotientAction.ker := by
    intro g hg
    ext a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K a
    change
      QuotientGroup.mk' K ((MulAut.conjNormal g) x) =
        QuotientGroup.mk' K x
    exact
      (QuotientGroup.eq_iff_div_mem (N := K)
        (x := (MulAut.conjNormal g) x) (y := x)).2
        (by simpa only [div_eq_mul_inv] using hNactsTrivially ⟨g, hg⟩ x)
  exact QuotientGroup.lift N prequotientAction hNker

/-- The topological conjugation action sends representatives to conjugates. -/
@[simp] theorem quotientConjugationOnTopologicallyCharacteristicQuotient_mk_apply_mk
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (K : Subgroup N) [K.TopologicallyCharacteristic]
    (hNactsTrivially :
      ∀ n x : N, (((MulAut.conjNormal (n : G)) x) * x⁻¹ : N) ∈ K)
    (g : G) (n : N) :
    quotientConjugationOnTopologicallyCharacteristicQuotient
      (G := G) N K hNactsTrivially
      (QuotientGroup.mk' N g) (QuotientGroup.mk' K n) =
        QuotientGroup.mk' K ((MulAut.conjNormal g) n) := by
  dsimp [quotientConjugationOnTopologicallyCharacteristicQuotient]
  rfl

end ProCGroups.Topologies
