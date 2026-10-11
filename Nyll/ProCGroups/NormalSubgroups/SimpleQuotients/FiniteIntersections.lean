/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.NormalSubgroups.SimpleQuotients.Algebraic

/-!
# Finite intersections above a simple-quotient kernel

This module proves normality of indexed intersections and shows that finite intersections retain
the full-product property with the kernel of a noncommutative simple quotient.
-/

namespace ProCGroups.NormalSubgroups

universe u

/--
An arbitrary infimum of normal subgroups is normal, when normality is known for every subgroup
in the indexing set.
-/
theorem sInf_normal_of_forall_normal
    {G : Type u} [Group G] {S : Set (Subgroup G)}
    (hSnormal : ∀ M ∈ S, M.Normal) :
    (sInf S).Normal := by
  rw [sInf_eq_iInf']
  exact Subgroup.normal_iInf_normal (fun M : S => hSnormal M.1 M.2)

/--
Finite-intersection step: in a noncommutative simple quotient, any finite intersection of normal
subgroups whose product with K is all of G still has product \(\top\) with K.
-/
theorem finite_sInf_sup_eq_top_of_noncomm_simple_quotient
    {G : Type u} [Group G] (K : Subgroup G) [K.Normal]
    [IsSimpleGroup (G ⧸ K)]
    (hquotNoncomm : ProCGroups.IsNoncommutativeGroup (G ⧸ K))
    {S : Set (Subgroup G)} (hSfinite : S.Finite)
    (hSnormal : ∀ M ∈ S, M.Normal)
    (hStop : ∀ M ∈ S, M ⊔ K = ⊤) :
    sInf S ⊔ K = ⊤ := by
  induction S, hSfinite using Set.Finite.induction_on with
  | empty =>
      simp only [sInf_empty, le_top, sup_of_le_left]
  | @insert a S ha hSfinite ih =>
      have hSnormal' : ∀ M ∈ S, M.Normal := by
        intro M hM
        exact hSnormal M (by simp only [Set.mem_insert_iff, hM, or_true])
      have hStop' : ∀ M ∈ S, M ⊔ K = ⊤ := by
        intro M hM
        exact hStop M (by simp only [Set.mem_insert_iff, hM, or_true])
      have : a.Normal := hSnormal a (by simp only [Set.mem_insert_iff, true_or])
      have hInfNormal : (sInf S).Normal := sInf_normal_of_forall_normal hSnormal'
      rw [sInf_insert]
      exact inf_sup_eq_top_of_noncomm_simple_quotient K a (sInf S)
        hquotNoncomm (hStop a (by simp only [Set.mem_insert_iff, true_or])) (ih hSnormal' hStop')

end ProCGroups.NormalSubgroups
