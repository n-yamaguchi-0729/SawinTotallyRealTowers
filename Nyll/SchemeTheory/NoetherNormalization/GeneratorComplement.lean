/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.NoetherNormalization.Trdeg
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.StdBasis

/-!
# Completing linear normalizing coordinates by original generators

The linear normalization theorem produces algebraically independent elements
in the linear span of a prescribed generating tuple.  This file develops the
finite-dimensional exchange argument which completes those elements by a
subset of the original tuple.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06

open Function

variable {K : Type*} [Field K]

/--
Algebraically independent elements in the span of a finite family admit a
linearly independent family of coefficient vectors.
-/
theorem exists_linearIndependent_coefficientVectors
    {A : Type*} [CommRing A] [Algebra K A] {n r : ℕ}
    (x : Fin n → A) (t : Fin r → A)
    (htspan : ∀ i, t i ∈ Submodule.span K (Set.range x))
    (htind : AlgebraicIndependent K t) :
    ∃ q : Fin r → (Fin n → K),
      LinearIndependent K q ∧
        ∀ i, Fintype.linearCombination K x (q i) = t i := by
  choose q hq using fun i => (Submodule.mem_span_range_iff_exists_fun K).mp (htspan i)
  have hq_eval :
      ∀ i, Fintype.linearCombination K x (q i) = t i := by
    intro i
    simpa only [Fintype.linearCombination_apply] using hq i
  refine ⟨q, ?_, hq_eval⟩
  apply LinearIndependent.of_comp (Fintype.linearCombination K x)
  have hcomp : (Fintype.linearCombination K x) ∘ q = t := by
    funext i
    exact hq_eval i
  rw [hcomp]
  exact htind.linearIndependent

/--
A linearly independent family of `r` vectors in `Kⁿ` can be completed to a
basis using exactly `n - r` standard coordinate vectors.

The set of standard vectors is recorded by a finset of coordinate indices.
-/
theorem exists_standardBasis_complement
    {n r : ℕ} (q : Fin r → (Fin n → K))
    (hq : LinearIndependent K q) :
    ∃ J : Finset (Fin n),
      J.card = n - r ∧
        Submodule.span K
          (Set.range q ∪
            (fun i : Fin n => Pi.single i 1) '' (J : Set (Fin n))) = ⊤ := by
  classical
  let e : Fin n → (Fin n → K) := Pi.basisFun K (Fin n)
  let v : Fin r ⊕ Fin n → (Fin n → K) := Sum.elim q e
  let s : Set (Fin r ⊕ Fin n) := Set.range (Sum.inl : Fin r → Fin r ⊕ Fin n)
  have hs : LinearIndepOn K v s := by
    apply (linearIndepOn_range_iff Sum.inl_injective v).mpr
    change LinearIndependent K q
    exact hq
  have hst : s ⊆ (Set.univ : Set (Fin r ⊕ Fin n)) := Set.subset_univ s
  let b : Set (Fin r ⊕ Fin n) := hs.extend hst
  have hsb : s ⊆ b := by
    simpa only [b] using hs.subset_extend hst
  have hb_ind : LinearIndepOn K v b := by
    simpa only [b] using hs.linearIndepOn_extend hst
  have hb_span_eq :
      Submodule.span K (v '' b) =
        Submodule.span K (v '' (Set.univ : Set (Fin r ⊕ Fin n))) := by
    simpa only [b] using hs.span_image_extend_eq_span_image hst
  have he_span : Submodule.span K (Set.range e) = ⊤ :=
    (Pi.basisFun K (Fin n)).span_eq
  have he_subset :
      Set.range e ⊆ v '' (Set.univ : Set (Fin r ⊕ Fin n)) := by
    rintro y ⟨i, rfl⟩
    exact ⟨Sum.inr i, Set.mem_univ _, by simp [v]⟩
  have hv_univ :
      Submodule.span K (v '' (Set.univ : Set (Fin r ⊕ Fin n))) = ⊤ := by
    apply top_unique
    rw [← he_span]
    exact Submodule.span_mono he_subset
  have hb_span : Submodule.span K (v '' b) = ⊤ :=
    hb_span_eq.trans hv_univ
  have hrange_restrict : Set.range (b.domRestrict v) = v '' b :=
    Set.range_domRestrict v b
  let bb : Module.Basis b K (Fin n → K) :=
    Module.Basis.mk hb_ind.linearIndependent_restrict (by
      rw [hrange_restrict, hb_span])
  have hcardb : Fintype.card b = n := by
    have h := Module.finrank_eq_card_basis bb
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  have hinl (i : Fin r) : Sum.inl i ∈ b :=
    hsb ⟨i, rfl⟩
  let J : Finset (Fin n) :=
    Finset.univ.filter fun j => Sum.inr j ∈ b
  let eLeft : {i : Fin r // Sum.inl i ∈ b} ≃ Fin r :=
    { toFun := fun i => i
      invFun := fun i => ⟨i, hinl i⟩
      left_inv := fun i => Subtype.ext rfl
      right_inv := fun _ => rfl }
  have hleft : Fintype.card {i : Fin r // Sum.inl i ∈ b} = r := by
    simpa using Fintype.card_congr eLeft
  let eRight : {j : Fin n // Sum.inr j ∈ b} ≃ J :=
    { toFun := fun j => ⟨j, by
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
        exact j.property⟩
      invFun := fun j => ⟨j, by
        have hj : (j : Fin n) ∈ J := j.property
        simpa only [J, Finset.mem_filter, Finset.mem_univ, true_and] using hj⟩
      left_inv := fun j => Subtype.ext rfl
      right_inv := fun _ => rfl }
  have hright :
      Fintype.card {j : Fin n // Sum.inr j ∈ b} = J.card := by
    calc
      Fintype.card {j : Fin n // Sum.inr j ∈ b} =
          Fintype.card J := Fintype.card_congr eRight
      _ = J.card := Fintype.card_coe J
  have hsplit :
      Fintype.card b =
        Fintype.card {i : Fin r // Sum.inl i ∈ b} +
          Fintype.card {j : Fin n // Sum.inr j ∈ b} := by
    calc
      Fintype.card b =
          Fintype.card
            ({i : Fin r // Sum.inl i ∈ b} ⊕
              {j : Fin n // Sum.inr j ∈ b}) :=
        Fintype.card_congr
          (Equiv.subtypeSum
            (p := fun z : Fin r ⊕ Fin n => z ∈ b))
      _ = _ := Fintype.card_sum
  have hJcard : J.card = n - r := by
    omega
  refine ⟨J, hJcard, ?_⟩
  have hb_subset :
      v '' b ⊆
        Set.range q ∪ e '' (J : Set (Fin n)) := by
    rintro y ⟨i, hi, rfl⟩
    cases i with
    | inl i =>
        exact Set.mem_union_left _ ⟨i, rfl⟩
    | inr j =>
        exact Set.mem_union_right _ ⟨j, by simpa [J] using hi, rfl⟩
  have hspan :
      Submodule.span K
        (Set.range q ∪ e '' (J : Set (Fin n))) = ⊤ := by
    apply top_unique
    rw [← hb_span]
    exact Submodule.span_mono hb_subset
  simpa only [e, Pi.basisFun_apply] using hspan

/--
Algebraically independent linear combinations can be completed by exactly
`n - r` members of the original `n`-tuple.  The resulting family has the same
linear span, hence generates the same `K`-subalgebra.
-/
theorem exists_originalGenerator_complement
    {A : Type*} [CommRing A] [Algebra K A] {n r : ℕ}
    (x : Fin n → A) (t : Fin r → A)
    (htspan : ∀ i, t i ∈ Submodule.span K (Set.range x))
    (htind : AlgebraicIndependent K t) :
    ∃ J : Finset (Fin n),
      J.card = n - r ∧
        Submodule.span K
          (Set.range t ∪ x '' (J : Set (Fin n))) =
            Submodule.span K (Set.range x) ∧
        Algebra.adjoin K
          (Set.range t ∪ x '' (J : Set (Fin n))) =
            Algebra.adjoin K (Set.range x) := by
  classical
  obtain ⟨q, hqind, hqeval⟩ :=
    exists_linearIndependent_coefficientVectors x t htspan htind
  obtain ⟨J, hJcard, hqspan⟩ :=
    exists_standardBasis_complement q hqind
  let e : Fin n → (Fin n → K) := fun i => Pi.single i 1
  let L : (Fin n → K) →ₗ[K] A := Fintype.linearCombination K x
  let source : Set (Fin n → K) :=
    Set.range q ∪ e '' (J : Set (Fin n))
  let target : Set A :=
    Set.range t ∪ x '' (J : Set (Fin n))
  have hsource : Submodule.span K source = ⊤ := by
    simpa only [source, e] using hqspan
  have hmap_le :
      Submodule.map L (Submodule.span K source) ≤
        Submodule.span K target := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro y ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · obtain ⟨i, rfl⟩ := hz
      exact Set.mem_union_left _ ⟨i, by
        simpa only [L] using (hqeval i).symm⟩
    · obtain ⟨i, hi, rfl⟩ := hz
      exact Set.mem_union_right _ ⟨i, hi, by
        simp only [L, e, Fintype.linearCombination_apply_single, one_smul]⟩
  have hx_mem_target : ∀ i, x i ∈ Submodule.span K target := by
    intro i
    have hei : e i ∈ Submodule.span K source := by
      rw [hsource]
      trivial
    have hmap :
        L (e i) ∈ Submodule.map L (Submodule.span K source) :=
      ⟨e i, hei, rfl⟩
    have := hmap_le hmap
    simpa only [L, e, Fintype.linearCombination_apply_single, one_smul] using this
  have hx_le :
      Submodule.span K (Set.range x) ≤ Submodule.span K target := by
    rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact hx_mem_target i
  have htarget_le :
      Submodule.span K target ≤ Submodule.span K (Set.range x) := by
    rw [Submodule.span_le]
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨i, rfl⟩ := hy
      exact htspan i
    · obtain ⟨i, -, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
  have hspan :
      Submodule.span K target = Submodule.span K (Set.range x) :=
    le_antisymm htarget_le hx_le
  have hadjoin :
      Algebra.adjoin K target = Algebra.adjoin K (Set.range x) := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      intro y hy
      apply
        (Submodule.span_le.mpr fun z hz =>
          Algebra.subset_adjoin hz :
            Submodule.span K (Set.range x) ≤
              (Algebra.adjoin K (Set.range x)).toSubmodule)
      rw [← hspan]
      exact Submodule.subset_span hy
    · rw [Algebra.adjoin_le_iff]
      intro y hy
      apply
        (Submodule.span_le.mpr fun z hz =>
          Algebra.subset_adjoin hz :
            Submodule.span K target ≤
              (Algebra.adjoin K target).toSubmodule)
      rw [hspan]
      exact Submodule.subset_span hy
  exact ⟨J, hJcard, by simpa only [target] using hspan,
    by simpa only [target] using hadjoin⟩

universe u

/--
The generator-sensitive infinite-field form of Noether normalization.

Besides the linear normalizing family and its transcendence-degree statement,
this returns exactly `n - r` indices from the prescribed generating tuple.
Together with the normalizing family, those original elements generate the
same algebra as the whole prescribed tuple.
-/
theorem exists_linear_normalization_with_generatorComplement
    (K A : Type u) [Field K] [Infinite K] [CommRing A] [IsDomain A]
    [Algebra K A] {n : ℕ} (x : Fin n → A)
    (hx : Algebra.adjoin K (Set.range x) = ⊤) :
    ∃ r : ℕ, r ≤ n ∧
      ∃ t : Fin r → A,
        (∀ i, t i ∈ Submodule.span K (Set.range x)) ∧
          AlgebraicIndependent K t ∧
            Algebra.IsIntegral (Algebra.adjoin K (Set.range t)) A ∧
              Algebra.trdeg K (FractionRing A) = r ∧
                ∃ J : Finset (Fin n),
                  J.card = n - r ∧
                    Algebra.adjoin K
                      (Set.range t ∪ x '' (J : Set (Fin n))) =
                        Algebra.adjoin K (Set.range x) := by
  obtain ⟨r, hr, t, htspan, htind, htint, htrdeg⟩ :=
    exists_linear_normalization_with_trdeg K A x hx
  obtain ⟨J, hJcard, -, hJadjoin⟩ :=
    exists_originalGenerator_complement x t htspan htind
  exact ⟨r, hr, t, htspan, htind, htint, htrdeg, J, hJcard, hJadjoin⟩

end Chapter06
end FieldArithmetic
