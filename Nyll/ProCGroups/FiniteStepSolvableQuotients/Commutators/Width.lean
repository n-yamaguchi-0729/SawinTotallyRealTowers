/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Rank
import Nyll.ProCGroups.FiniteGeneration.CharacteristicChainsAndIndices

/-!
# Uniform commutator-width estimates

This module encodes products of commutators with prescribed factors and proves the functorial and
rank-theoretic estimates used to obtain uniform width bounds.
-/

open scoped Topology Pointwise commutatorElement

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.FiniteGeneration

universe u

/--
A product of commutators whose left factors lie in \(A\) and whose right factors are prescribed
by \(x\).
-/
def IsProductOfCommutatorsAlongInSubgroup
    {G : Type u} [Group G] (A : Subgroup G) {n : ℕ}
    (x : Fin n → G) (g : G) : Prop :=
  ∃ a : Fin n → G,
    (∀ i, a i ∈ A) ∧
      (List.ofFn fun i : Fin n => ⁅a i, x i⁆).prod = g

/--
A product of commutators in which the right factors come from two prescribed families and all
left factors lie in the same subgroup.
-/
def IsProductOfCommutatorsAlongPairInSubgroup
    {G : Type u} [Group G] (A : Subgroup G) {m n : ℕ}
    (x : Fin m → G) (y : Fin n → G) (g : G) : Prop :=
  ∃ a : Fin m → G, ∃ b : Fin n → G,
    (∀ i, a i ∈ A) ∧ (∀ j, b j ∈ A) ∧
      (List.ofFn fun i : Fin m => ⁅a i, x i⁆).prod *
        (List.ofFn fun j : Fin n => ⁅b j, y j⁆).prod = g

/--
A product-of-commutators witness remains valid after enlarging the allowed number of commutator
factors.
-/
theorem IsProductOfCommutatorsAlongInSubgroup.mono
    {G : Type u} [Group G] {A B : Subgroup G} {n : ℕ}
    {x : Fin n → G} {g : G}
    (hAB : A ≤ B)
    (h : IsProductOfCommutatorsAlongInSubgroup A x g) :
    IsProductOfCommutatorsAlongInSubgroup B x g := by
  rcases h with ⟨a, ha, hprod⟩
  exact ⟨a, fun i => hAB (ha i), hprod⟩

/-- Being a product of commutators along a subgroup is preserved by the induced map. -/
theorem IsProductOfCommutatorsAlongInSubgroup.map
    {G H : Type u} [Group G] [Group H] {A : Subgroup G} {n : ℕ}
    {x : Fin n → G} {g : G}
    (f : G →* H)
    (h : IsProductOfCommutatorsAlongInSubgroup A x g) :
    IsProductOfCommutatorsAlongInSubgroup (A.map f) (fun i => f (x i)) (f g) := by
    rcases h with ⟨a, ha, hprod⟩
    refine ⟨fun i => f (a i), ?_, ?_⟩
    · intro i
      exact ⟨a i, ha i, rfl⟩
    · let l : List (G × G) := List.ofFn fun i : Fin n => (a i, x i)
      have hmapList :
          ∀ l : List (G × G),
            f ((l.map fun p : G × G => ⁅p.1, p.2⁆).prod) =
              (l.map fun p : G × G => ⁅f p.1, f p.2⁆).prod := by
        intro l
        induction l with
        | nil =>
            simp only [List.map_nil, List.prod_nil, map_one]
        | cons p t ih =>
            simp only [List.map_cons, List.prod_cons, map_mul, map_commutatorElement, ih]
      calc
        (List.ofFn fun i : Fin n => ⁅f (a i), f (x i)⁆).prod =
            (l.map fun p : G × G => ⁅f p.1, f p.2⁆).prod := by
              dsimp [l]
              rw [List.map_ofFn]
              rfl
        _ = f ((l.map fun p : G × G => ⁅p.1, p.2⁆).prod) := (hmapList l).symm
        _ = f g := by
              have hcommList :
                  (l.map fun p : G × G => ⁅p.1, p.2⁆) =
                    List.ofFn (fun i : Fin n => ⁅a i, x i⁆) := by
                dsimp [l]
                rw [List.map_ofFn]
                rfl
              rw [hcommList, hprod]

/--
Multiplying two subgroup-bounded commutator-product witnesses gives a witness with the sum of
the allowed widths.
-/
theorem IsProductOfCommutatorsAlongInSubgroup.mul
    {G : Type u} [Group G] {A : Subgroup G} {m n : ℕ}
    {x : Fin m → G} {y : Fin n → G} {g h : G}
    (hg : IsProductOfCommutatorsAlongInSubgroup A x g)
    (hh : IsProductOfCommutatorsAlongInSubgroup A y h) :
    IsProductOfCommutatorsAlongInSubgroup A (Fin.append x y) (g * h) := by
  rcases hg with ⟨a, ha, hprodg⟩
  rcases hh with ⟨b, hb, hprodh⟩
  refine ⟨Fin.append a b, ?_, ?_⟩
  · intro i
    cases i using Fin.addCases with
    | left i =>
        simpa [Fin.append_left] using ha i
    | right i =>
        simpa [Fin.append_right] using hb i
  · have hlist :
          List.ofFn (fun i : Fin (m + n) =>
              ⁅(Fin.append a b i), (Fin.append x y i)⁆) =
            List.ofFn (fun i : Fin m => ⁅a i, x i⁆) ++
              List.ofFn (fun i : Fin n => ⁅b i, y i⁆) := by
        have hfun :
            (fun i : Fin (m + n) => ⁅(Fin.append a b i), (Fin.append x y i)⁆) =
              Fin.append (fun i : Fin m => ⁅a i, x i⁆) (fun i : Fin n => ⁅b i, y i⁆) := by
          funext i
          cases i using Fin.addCases with
          | left i =>
              simp only [Fin.append_left]
          | right i =>
              simp only [Fin.append_right]
        rw [hfun, List.ofFn_fin_append]
    rw [hlist, List.prod_append, hprodg, hprodh]

/-- A rank bound supplies a generating family of the corresponding bounded cardinality. -/
theorem exists_generating_family_of_rank_le
    {K : Type u} [Group K] [Group.FG K] {d : ℕ}
    (hd : Group.rank K ≤ d) :
    ∃ x : Fin d → K, Subgroup.closure (Set.range x) = (⊤ : Subgroup K) := by
  classical
  rcases Group.rank_spec K with ⟨S, hScard, hSgen⟩
  have hcard : Fintype.card {a : K // a ∈ S} ≤ Fintype.card (Fin d) := by
    simpa [hScard] using hd
  let e : {a : K // a ∈ S} ↪ Fin d :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  let x : Fin d → K := fun i =>
    if h : ∃ a : {a : K // a ∈ S}, e a = i then
      ((Classical.choose h : {a : K // a ∈ S}) : K)
    else 1
  have hSsubset : (S : Set K) ⊆ Set.range x := by
    intro a ha
    let aS : {a : K // a ∈ S} := ⟨a, ha⟩
    refine ⟨e aS, ?_⟩
    dsimp [x]
    let hEx : ∃ b : {a : K // a ∈ S}, e b = e aS := ⟨aS, rfl⟩
    rw [dite_eq_left hEx]
    change ((Classical.choose hEx : {a : K // a ∈ S}) : K) = (aS : K)
    exact congrArg Subtype.val (e.injective (Classical.choose_spec hEx))
  refine ⟨x, le_antisymm le_top ?_⟩
  rw [← hSgen]
  exact Subgroup.closure_mono hSsubset

/--
In a semidirect product generated by at most d elements, the kernel admits d normal generators.
-/
theorem exists_normalGenerators_of_split_group_of_rank_le
    {K : Type u} [Group K] [Group.FG K] {H L : Subgroup K} [_hH : H.Normal]
    (hsplit : IsCompl H L) {d : ℕ} (hd : Group.rank K ≤ d) :
    ∃ y : Fin d → K, Subgroup.normalClosure (Set.range y) = H := by
  classical
  rcases exists_generating_family_of_rank_le (K := K) hd with ⟨x, hx⟩
  let qH : K →* K ⧸ H := QuotientGroup.mk' H
  have hmapH : Subgroup.map qH H = (⊥ : Subgroup (K ⧸ H)) := by
    ext z
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact (QuotientGroup.eq_one_iff (N := H) h).2 hh
    · intro hz
      rw [Subgroup.mem_bot] at hz
      subst z
      exact ⟨1, H.one_mem, by simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_one, qH]⟩
  have hmapL : Subgroup.map qH L = (⊤ : Subgroup (K ⧸ H)) := by
    have hmapSup :
        Subgroup.map qH (H ⊔ L) = (⊤ : Subgroup (K ⧸ H)) := by
      rw [hsplit.sup_eq_top]
      exact Subgroup.map_top_of_surjective qH (QuotientGroup.mk'_surjective H)
    rw [Subgroup.map_sup, hmapH, bot_sup_eq] at hmapSup
    exact hmapSup
  have hlift :
      ∀ i : Fin d, ∃ l : K, l ∈ L ∧ qH l = qH (x i) := by
    intro i
    have hxmem : qH (x i) ∈ Subgroup.map qH L := by
      rw [hmapL]
      simp only [Subgroup.mem_top]
    exact (Subgroup.mem_map.mp hxmem)
  choose l hlL hlq using hlift
  let y : Fin d → K := fun i => (l i)⁻¹ * x i
  refine ⟨y, ?_⟩
  let N : Subgroup K := Subgroup.normalClosure (Set.range y)
  have : N.Normal := Subgroup.normalClosure_normal
  have hyH : ∀ i, y i ∈ H := by
    intro i
    exact QuotientGroup.eq.mp (hlq i)
  have hNleH : N ≤ H := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro z ⟨i, rfl⟩
    exact hyH i
  have hHleN : H ≤ N := by
    let qN : K →* K ⧸ N := QuotientGroup.mk' N
    let M : Subgroup (K ⧸ N) := Subgroup.map qN L
    have hxM : ∀ i : Fin d, qN (x i) ∈ M := by
      intro i
      refine Subgroup.mem_map.mpr ⟨l i, hlL i, ?_⟩
      have hyN : y i ∈ N := Subgroup.subset_normalClosure ⟨i, rfl⟩
      exact QuotientGroup.eq.mpr hyN
    have htopLe : (⊤ : Subgroup K) ≤ Subgroup.comap qN M := by
      rw [← hx]
      exact (Subgroup.closure_le (Subgroup.comap qN M)).2 <| by
        rintro z ⟨i, rfl⟩
        exact hxM i
    intro h hh
    have hqmem : qN h ∈ M := htopLe (by simp only [Subgroup.mem_top])
    rcases Subgroup.mem_map.mp hqmem with ⟨l0, hl0L, hqeq⟩
    have hn : l0⁻¹ * h ∈ N := QuotientGroup.eq.mp hqeq
    have hl0H : l0 ∈ H := by
      have hnH : l0⁻¹ * h ∈ H := hNleH hn
      have hlinvH : l0⁻¹ ∈ H := by
        simpa [mul_assoc] using H.mul_mem hnH (H.inv_mem hh)
      simpa using H.inv_mem hlinvH
    have hl0bot : l0 ∈ (⊥ : Subgroup K) := by
      rw [← hsplit.inf_eq_bot]
      exact ⟨hl0H, hl0L⟩
    have hl0one : l0 = 1 := by
      simpa using hl0bot
    have hqone : qN h = 1 := by
      simpa [hl0one] using hqeq.symm
    exact (QuotientGroup.eq_one_iff (N := N) h).mp hqone
  exact le_antisymm hNleH hHleN

end ProCGroups.FiniteStepSolvableQuotients
