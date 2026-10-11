/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.SetTheory.Cardinal.NatCard
import Nyll.ProCGroups.FreeConstructions.Framework

/-!
# Generator bounds from finite subgroup families

Independent generating tuples for finitely many subgroups can be concatenated.
The two theorems below turn that elementary construction into explicit
ambient-group rank bounds.
-/

namespace ProCGroups.FreeConstructions

universe u v

/-- If two subgroups generate `G` and each has an `r`-element generating
family, concatenating those families gives a `2r`-element generating family
for `G`. -/
theorem generatorRankLE_add_of_two_subgroups
    (G : Type u) [Group G] (r : Nat) (A B : Subgroup G)
    (hABtop : Subgroup.closure ((A : Set G) ∪ (B : Set G)) = ⊤)
    (hA : AbstractGeneratorRankLE A r)
    (hB : AbstractGeneratorRankLE B r) :
    AbstractGeneratorRankLE G (r + r) := by
  rcases hA with ⟨genA, hgenA⟩
  rcases hB with ⟨genB, hgenB⟩
  let gen : Fin (r + r) → G :=
    Fin.append (fun i => (genA i : G)) (fun i => (genB i : G))
  let S : Set G := Set.range gen
  refine ⟨gen, ?_⟩
  have hA_le : (A : Set G) ⊆ Subgroup.closure S := by
    intro a ha
    let aA : A := ⟨a, ha⟩
    have haA : aA ∈ Subgroup.closure (Set.range genA) := by
      rw [hgenA]
      trivial
    exact Subgroup.closure_induction
      (p := fun (x : A) _ => (x : G) ∈ Subgroup.closure S)
      (fun x hx => by
        rcases hx with ⟨i, rfl⟩
        exact Subgroup.subset_closure (by
          refine ⟨Fin.castAdd r i, ?_⟩
          simp only [Fin.append_left, gen]))
      (by simp only [OneMemClass.coe_one, one_mem])
      (fun x y _ _ hx hy => by
        simpa using (Subgroup.mul_mem (Subgroup.closure S) hx hy))
      (fun x _ hx => by
        simpa using (Subgroup.inv_mem (Subgroup.closure S) hx))
      haA
  have hB_le : (B : Set G) ⊆ Subgroup.closure S := by
    intro b hb
    let bB : B := ⟨b, hb⟩
    have hbB : bB ∈ Subgroup.closure (Set.range genB) := by
      rw [hgenB]
      trivial
    exact Subgroup.closure_induction
      (p := fun (x : B) _ => (x : G) ∈ Subgroup.closure S)
      (fun x hx => by
        rcases hx with ⟨i, rfl⟩
        exact Subgroup.subset_closure (by
          refine ⟨Fin.natAdd r i, ?_⟩
          simpa [gen] using
            (Fin.append_right (fun i => (genA i : G)) (fun i => (genB i : G)) i)))
      (by simp only [OneMemClass.coe_one, one_mem])
      (fun x y _ _ hx hy => by
        simpa using (Subgroup.mul_mem (Subgroup.closure S) hx hy))
      (fun x _ hx => by
        simpa using (Subgroup.inv_mem (Subgroup.closure S) hx))
      hbB
  apply le_antisymm
  · exact le_top
  · rw [← hABtop]
    exact (Subgroup.closure_le (K := Subgroup.closure S)).2 (by
      intro x hx
      exact hx.elim (fun hxA => hA_le hxA) (fun hxB => hB_le hxB))

/-- If an `s`-element family of subgroups generates `G` and every member has
an `r`-element generating family, concatenating all families gives an
`s * r`-element generating family for `G`. -/
theorem finite_subgroup_family_generator_bound
    {ι : Type v} [Finite ι] (G : Type u) [Group G]
    (subgroups : ι → Subgroup G) (r s : Nat)
    (hcard : Nat.card ι = s)
    (hgenerates : Subgroup.closure (Set.iUnion fun i => (subgroups i : Set G)) = ⊤)
    (hEach : ∀ i, AbstractGeneratorRankLE (subgroups i) r) :
    AbstractGeneratorRankLE G (s * r) := by
  classical
  have hprod : Nat.card (ι × Fin r) = s * r := by
    rw [Nat.card_prod, hcard, Nat.card_fin]
  let e : Fin (s * r) ≃ ι × Fin r := (Finite.equivFinOfCardEq hprod).symm
  let genSub : (i : ι) → Fin r → subgroups i :=
    fun i => Classical.choose (hEach i)
  have hgenSub : ∀ i, Subgroup.closure (Set.range (genSub i)) = ⊤ :=
    fun i => Classical.choose_spec (hEach i)
  let gen : Fin (s * r) → G := fun a => (genSub (e a).1 (e a).2 : G)
  let S : Set G := Set.range gen
  refine ⟨gen, ?_⟩
  let K : Subgroup G := Subgroup.closure S
  have hsub_le : ∀ i, (subgroups i : Set G) ⊆ K := by
    intro i x hx
    let xi : subgroups i := ⟨x, hx⟩
    have hxi : xi ∈ Subgroup.closure (Set.range (genSub i)) := by
      rw [hgenSub i]
      trivial
    exact Subgroup.closure_induction
      (p := fun (y : subgroups i) _ => (y : G) ∈ K)
      (fun y hy => by
        rcases hy with ⟨j, rfl⟩
        exact Subgroup.subset_closure (by
          refine ⟨e.symm (i, j), ?_⟩
          simpa [gen] using
            congrArg (fun p : ι × Fin r => (genSub p.1 p.2 : G))
              (e.apply_symm_apply (i, j))))
      (by simp only [OneMemClass.coe_one, one_mem, K])
      (fun y z _ _ hy hz => by
        simpa [K] using Subgroup.mul_mem K hy hz)
      (fun y _ hy => by
        simpa [K] using Subgroup.inv_mem K hy)
      hxi
  apply le_antisymm
  · exact le_top
  · rw [← hgenerates]
    exact (Subgroup.closure_le (K := K)).2 (by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      exact hsub_le i hxi)

end ProCGroups.FreeConstructions
