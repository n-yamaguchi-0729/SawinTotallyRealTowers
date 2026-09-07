import Mathlib.GroupTheory.Schreier
import ProCGroups.ReidemeisterSchreier.Discrete.OpenSubgroups.Words.Basic
import ProCGroups.ReidemeisterSchreier.RightQuotient

set_option autoImplicit false

universe u

/-!
# Reidemeister Schreier / Discrete / Open Subgroups / Transversals

This module defines full and partial right Schreier transversals in free
groups, proves their complement and prefix-closure properties, and supplies
the existence and extension results used later.
-/

namespace ReidemeisterSchreier.Discrete.OpenSubgroups

section RightSchreierTransversals

open scoped Pointwise
open _root_.ReidemeisterSchreier.FreeGroup

/--
A right Schreier transversal is a right transversal containing every initial segment of each of
its elements.
-/
def IsRightSchreierTransversal {X : Type u} [DecidableEq X]
    (L : Subgroup (FreeGroup X)) (T : Set (FreeGroup X)) : Prop :=
  Subgroup.IsComplement (L : Set (FreeGroup X)) T ∧
    (1 : FreeGroup X) ∈ T ∧
      ∀ ⦃t : FreeGroup X⦄, t ∈ T → freeGroupInitialSegments t ⊆ T

/--
A right partial Schreier transversal is prefix-closed, contains 1, and meets each right coset in
at most one element.
-/
def IsRightPartialSchreierTransversal {X : Type u} [DecidableEq X]
    (L : Subgroup (FreeGroup X)) (T : Set (FreeGroup X)) : Prop :=
  (1 : FreeGroup X) ∈ T ∧
    (∀ ⦃t : FreeGroup X⦄, t ∈ T → freeGroupInitialSegments t ⊆ T) ∧
      ∀ ⦃a b : FreeGroup X⦄, a ∈ T → b ∈ T →
        (Quotient.mk'' a : Quotient (QuotientGroup.rightRel L)) =
          Quotient.mk'' b → a = b

/-- A right Schreier transversal gives the required complement to the subgroup action. -/
theorem IsRightSchreierTransversal.isComplement {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    Subgroup.IsComplement (L : Set (FreeGroup X)) T :=
  hT.1

/-- A right Schreier transversal contains the identity word. -/
theorem IsRightSchreierTransversal.one_mem {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    (1 : FreeGroup X) ∈ T :=
  hT.2.1

/-- A right Schreier transversal is closed under initial segments. -/
theorem IsRightSchreierTransversal.prefix_closed {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {t : FreeGroup X} (ht : t ∈ T) :
    freeGroupInitialSegments t ⊆ T :=
  hT.2.2 ht

/-- A right partial Schreier transversal contains the identity word. -/
theorem IsRightPartialSchreierTransversal.one_mem {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightPartialSchreierTransversal (X := X) L T) :
    (1 : FreeGroup X) ∈ T :=
  hT.1

/-- A right partial Schreier transversal is closed under initial segments. -/
theorem IsRightPartialSchreierTransversal.prefix_closed {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightPartialSchreierTransversal (X := X) L T)
    {t : FreeGroup X} (ht : t ∈ T) :
    freeGroupInitialSegments t ⊆ T :=
  hT.2.1 ht

/-- Two right Schreier transversal representatives are equal when their right quotients agree. -/
theorem IsRightPartialSchreierTransversal.eq_of_rightQuotient_eq
    {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightPartialSchreierTransversal (X := X) L T)
    {a b : FreeGroup X} (ha : a ∈ T) (hb : b ∈ T)
    (hEq :
      (Quotient.mk'' a : Quotient (QuotientGroup.rightRel L)) =
        Quotient.mk'' b) :
    a = b :=
  hT.2.2 ha hb hEq

/-- The prefix parent of a partial Schreier word satisfies the required membership condition. -/
theorem prefixParent_mem_of_partial {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightPartialSchreierTransversal (X := X) L T)
    {t : FreeGroup X} (ht : t ∈ T) :
    FreeGroup.prefixParent t ∈ T := by
  exact hT.2.1 ht ⟨(FreeGroup.toWord t).length - 1, Nat.sub_le (FreeGroup.toWord t).length 1, by
    simp only [prefixParent, List.dropLast_eq_take]⟩

/--
A nonempty chain of right partial Schreier transversals has a union that is again a right
partial Schreier transversal. This is the chain-upper-bound step used in the Zorn construction.
-/
theorem chain_sUnion_isRightPartialSchreierTransversal
    {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {c : Set (Set (FreeGroup X))}
    (hcn : c.Nonempty)
    (hc :
      ∀ ⦃s⦄, s ∈ c → ∀ ⦃t⦄, t ∈ c → s ≠ t → s ⊆ t ∨ t ⊆ s)
    (hcPartial :
      ∀ ⦃s⦄, s ∈ c → IsRightPartialSchreierTransversal (X := X) L s) :
    IsRightPartialSchreierTransversal (X := X) L (⋃₀ c) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hcn with ⟨s, hs⟩
    exact Set.mem_sUnion_of_mem ((hcPartial hs).1) hs
  · intro t ht u hu
    rcases Set.mem_sUnion.mp ht with ⟨s, hs, hts⟩
    exact Set.mem_sUnion.mpr ⟨s, hs, (hcPartial hs).2.1 hts hu⟩
  · intro a b ha hb hab
    rcases Set.mem_sUnion.mp ha with ⟨s, hs, has⟩
    rcases Set.mem_sUnion.mp hb with ⟨t, ht, hbt⟩
    by_cases hst : s = t
    · subst hst
      exact (hcPartial ht).2.2 has hbt hab
    · rcases hc hs ht hst with hst' | hts'
      · exact (hcPartial ht).2.2 (hst' has) hbt hab
      · exact (hcPartial hs).2.2 has (hts' hbt) hab

/-- Every right partial Schreier transversal extends to a full right Schreier transversal. -/
theorem exists_rightSchreierTransversal_of_partial {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T₀ : Set (FreeGroup X)}
    (hT₀ : IsRightPartialSchreierTransversal (X := X) L T₀) :
    ∃ T : Set (FreeGroup X), T₀ ⊆ T ∧ IsRightSchreierTransversal (X := X) L T := by
  classical
  let S : Set (Set (FreeGroup X)) :=
    {T | T₀ ⊆ T ∧ IsRightPartialSchreierTransversal (X := X) L T}
  have hT₀S : T₀ ∈ S := by
    exact ⟨Set.Subset.rfl, hT₀⟩
  obtain ⟨T, hTS, hTmax⟩ :=
    zorn_subset_nonempty S
      (fun c hcS hc hcn => by
        refine ⟨⋃₀ c, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · intro t ht
            rcases hcn with ⟨s, hs⟩
            exact Set.mem_sUnion_of_mem ((hcS hs).1 ht) hs
          · exact chain_sUnion_isRightPartialSchreierTransversal
              (X := X) (L := L) hcn (fun {s} hs {t} ht hst => hc hs ht hst)
              (fun {s} hs => (hcS hs).2)
        · intro s hs
          exact Set.subset_sUnion_of_mem hs)
      T₀ hT₀S
  have hTpartial : IsRightPartialSchreierTransversal (X := X) L T := hTmax.prop.2
  have hTcover :
      ∀ g : FreeGroup X,
        ∃ t ∈ T,
          (Quotient.mk'' t : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' g := by
    intro g
    by_contra hnog
    let Missing : FreeGroup X → Prop := fun w =>
      ∀ t ∈ T,
        (Quotient.mk'' t : Quotient (QuotientGroup.rightRel L)) ≠ Quotient.mk'' w
    have hmissing : Missing g := by
      intro t ht hEq
      exact hnog ⟨t, ht, hEq⟩
    let P : ℕ → Prop := fun n =>
      ∃ w : FreeGroup X, Missing w ∧ (FreeGroup.toWord w).length = n
    have hP : ∃ n, P n := ⟨(FreeGroup.toWord g).length, g, hmissing, rfl⟩
    let n := Nat.find hP
    obtain ⟨w, hwmiss, hwlen⟩ := Nat.find_spec hP
    have hmin : ∀ u : FreeGroup X, Missing u → n ≤ (FreeGroup.toWord u).length := by
      intro u hu
      exact Nat.find_min' hP ⟨u, hu, rfl⟩
    have hw1 : w ≠ 1 := by
      intro hw1
      exact hwmiss 1 hTpartial.1 (by simp only [hw1])
    have hwword : FreeGroup.toWord w ≠ [] := by
      exact mt (FreeGroup.toWord_eq_nil_iff.mp) hw1
    let y : X × Bool := (FreeGroup.toWord w).getLast hwword
    let u : FreeGroup X := FreeGroup.prefixParent w
    have huWitness :
        ∃ t ∈ T,
          (Quotient.mk'' t : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' u := by
      by_contra hu
      have humiss : Missing u := by
        intro t ht hEq
        exact hu ⟨t, ht, hEq⟩
      have hlt : (FreeGroup.toWord u).length < n := by
        simpa [u, n, hwlen] using
          Internal.FreeGroupWord.FreeGroup.toWord_length_prefixParent_lt (t := w) hw1
      exact (Nat.not_lt_of_ge (hmin u humiss)) hlt
    obtain ⟨t, htT, htq⟩ := huWitness
    let z : FreeGroup X := t * FreeGroup.mk [y]
    have hzq :
        (Quotient.mk'' z : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' w := by
      apply Quotient.sound'
      have hrel : QuotientGroup.rightRel L t u := Quotient.exact' htq
      rw [QuotientGroup.rightRel_apply] at hrel ⊢
      have hwrep :
          u * FreeGroup.mk [y] = w := by
        exact Internal.FreeGroupWord.FreeGroup.prefixParent_mul_mk_singleton_of_last
          w y hwword (by rfl)
      have hzw : w * z⁻¹ = u * t⁻¹ := by
        have hcancelWord :
            FreeGroup.mk [y] * FreeGroup.mk (FreeGroup.invRev [y]) = (1 : FreeGroup X) := by
          rw [← FreeGroup.inv_mk (L := [y])]
          exact mul_inv_cancel (FreeGroup.mk [y])
        have hcancelWord' :
            FreeGroup.mk (y :: FreeGroup.invRev [y]) = (1 : FreeGroup X) := by
          simpa using hcancelWord
        have htail :
            FreeGroup.mk [y] * (FreeGroup.mk (FreeGroup.invRev [y]) * t⁻¹) =
              FreeGroup.mk (y :: FreeGroup.invRev [y]) * t⁻¹ := by
          calc
            FreeGroup.mk [y] * (FreeGroup.mk (FreeGroup.invRev [y]) * t⁻¹)
                = (FreeGroup.mk [y] * FreeGroup.mk (FreeGroup.invRev [y])) * t⁻¹ := by
                    rw [mul_assoc]
            _ = FreeGroup.mk (y :: FreeGroup.invRev [y]) * t⁻¹ := by
                  rw [FreeGroup.mul_mk]
                  rfl
        calc
          w * z⁻¹ = (u * FreeGroup.mk [y]) * z⁻¹ := by rw [hwrep]
          _ = (u * FreeGroup.mk [y]) * (t * FreeGroup.mk [y])⁻¹ := by rfl
          _ = (u * FreeGroup.mk [y]) * (FreeGroup.mk (FreeGroup.invRev [y]) * t⁻¹) := by
                simp only [mul_inv_rev, FreeGroup.inv_mk]
          _ = u * (FreeGroup.mk [y] * (FreeGroup.mk (FreeGroup.invRev [y]) * t⁻¹)) := by
                rw [← mul_assoc, ← mul_assoc, mul_assoc]
          _ = u * (FreeGroup.mk (y :: FreeGroup.invRev [y]) * t⁻¹) := by
                exact congrArg (fun x => u * x) htail
          _ = u * (1 * t⁻¹) := by rw [hcancelWord']
          _ = u * t⁻¹ := by simp only [one_mul]
      simpa [hzw] using hrel
    by_cases hcancel :
        ∃ hw' : FreeGroup.toWord t ≠ [],
          (FreeGroup.toWord t).getLast hw' = (y.1, !y.2)
    · rcases hcancel with ⟨hw', hlast'⟩
      have hzEqPrefix : z = FreeGroup.prefixParent t := by
        simpa [z, FreeGroup.prefixParent] using
          Internal.FreeGroupWord.FreeGroup.mul_mk_singleton_eq_mk_dropLast_of_cancels
            t y hw' hlast'
      have hzT : z ∈ T := by
        simpa [hzEqPrefix] using prefixParent_mem_of_partial (X := X) (L := L) hTpartial htT
      exact hwmiss z hzT hzq
    · have hzWord : FreeGroup.toWord z = FreeGroup.toWord t ++ [y] :=
        Internal.FreeGroupWord.FreeGroup.toWord_mul_mk_singleton_of_not_cancels t y hcancel
      let U : Set (FreeGroup X) := Set.insert z T
      have hzPrefix : freeGroupInitialSegments z ⊆ U := by
        intro v hv
        rcases hv with ⟨m, hm, rfl⟩
        have hlenz : (FreeGroup.toWord z).length = (FreeGroup.toWord t).length + 1 := by
          rw [hzWord]
          simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
        have hm' : m ≤ (FreeGroup.toWord t).length + 1 := by
          simpa [hlenz] using hm
        rcases Nat.eq_or_lt_of_le hm' with hmEq | hmLt
        · left
          have hmz : m = (FreeGroup.toWord z).length := by
            simpa [hlenz] using hmEq
          have htake : List.take m (FreeGroup.toWord z) = FreeGroup.toWord z := by
            rw [hmz, List.take_length]
          rw [htake]
          exact FreeGroup.mk_toWord (x := z)
        · right
          have hmle : m ≤ (FreeGroup.toWord t).length := Nat.lt_succ_iff.mp hmLt
          have htake : List.take m (FreeGroup.toWord z) = List.take m (FreeGroup.toWord t) := by
            rw [hzWord, List.take_append_of_le_length hmle]
          rw [htake]
          exact hTpartial.2.1 htT ⟨m, hmle, rfl⟩
      have hUin : U ∈ S := by
        refine ⟨?_, ?_⟩
        · intro s hs
          exact Or.inr (hTmax.prop.1 hs)
        · refine ⟨Or.inr hTpartial.1, ?_, ?_⟩
          · intro s hs
            rcases hs with rfl | hsT
            · exact hzPrefix
            · intro v hv
              exact Or.inr (hTpartial.2.1 hsT hv)
          · intro a b ha hb hab
            rcases ha with rfl | haT
            · rcases hb with rfl | hbT
              · rfl
              · exfalso
                exact hwmiss b hbT (hab.symm.trans hzq)
            · rcases hb with rfl | hbT
              · exfalso
                exact hwmiss a haT (hab.trans hzq)
              · exact hTpartial.2.2 haT hbT hab
      have hTU : T = U := hTmax.eq_of_subset hUin (by intro s hs; exact Or.inr hs)
      have hzT : z ∈ T := by
        have hzU : z ∈ U := by
          change z ∈ Set.insert z T
          exact Set.mem_insert z T
        exact hTU.symm ▸ hzU
      exact hwmiss z hzT hzq
  refine ⟨T, hTmax.prop.1, ?_⟩
  refine ⟨?_, hTpartial.1, hTpartial.2.1⟩
  rw [Subgroup.isComplement_iff_existsUnique_mul_inv_mem]
  intro g
  rcases hTcover g with ⟨t, htT, htq⟩
  refine ⟨⟨t, htT⟩, ?_, ?_⟩
  · have hrel : QuotientGroup.rightRel L t g := Quotient.exact' htq
    simpa [QuotientGroup.rightRel_apply] using hrel
  · intro t' hmem
    apply Subtype.ext
    apply hTpartial.2.2 t'.2 htT
    calc
      (Quotient.mk'' (t' : FreeGroup X) :
          Quotient (QuotientGroup.rightRel L)) =
        Quotient.mk'' g := by
        apply Quotient.sound'
        rw [QuotientGroup.rightRel_apply]
        simpa using hmem
      _ = Quotient.mk'' t := htq.symm

/-- Every subgroup of a free group admits a right Schreier transversal. -/
theorem exists_rightSchreierTransversal {X : Type u} [DecidableEq X]
    (L : Subgroup (FreeGroup X)) :
    ∃ T : Set (FreeGroup X), IsRightSchreierTransversal (X := X) L T := by
  let T₀ : Set (FreeGroup X) := {(1 : FreeGroup X)}
  have hT₀ : IsRightPartialSchreierTransversal (X := X) L T₀ := by
    refine ⟨by simp only [Set.mem_singleton_iff, T₀], ?_, ?_⟩
    · intro t ht u hu
      have ht1 : t = 1 := by
        simpa [T₀] using ht
      subst t
      rcases hu with ⟨n, hn, hu⟩
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero (by simpa using hn)
      subst hn0
      change u = (1 : FreeGroup X)
      exact hu.trans FreeGroup.one_eq_mk.symm
    · intro a b ha hb _
      have ha1 : a = 1 := by
        simpa [T₀] using ha
      have hb1 : b = 1 := by
        simpa [T₀] using hb
      subst a
      subst b
      rfl
  rcases exists_rightSchreierTransversal_of_partial (X := X) (L := L) hT₀ with ⟨T, _, hT⟩
  exact ⟨T, hT⟩

/--
If two generator powers determine the same right quotient, their difference lies in the
subgroup.
-/
theorem generatorPower_sub_mem_of_rightQuotient_eq {X : Type u}
    {L : Subgroup (FreeGroup X)} (x : X) {m n : ℕ} (hmn : m ≤ n)
    (hEq :
      (Quotient.mk'' ((FreeGroup.of x) ^ m) : Quotient (QuotientGroup.rightRel L)) =
        Quotient.mk'' ((FreeGroup.of x) ^ n)) :
    (FreeGroup.of x) ^ (n - m) ∈ L := by
  have hrel : QuotientGroup.rightRel L ((FreeGroup.of x) ^ m) ((FreeGroup.of x) ^ n) :=
    Quotient.exact' hEq
  rw [QuotientGroup.rightRel_apply] at hrel
  have hcalc :
      (FreeGroup.of x) ^ n * (((FreeGroup.of x) ^ m)⁻¹) =
        (FreeGroup.of x) ^ (n - m) := by
    calc
      (FreeGroup.of x) ^ n * (((FreeGroup.of x) ^ m)⁻¹)
          = (FreeGroup.of x) ^ ((n - m) + m) * (((FreeGroup.of x) ^ m)⁻¹) := by
              rw [Nat.sub_add_cancel hmn]
      _ = (((FreeGroup.of x) ^ (n - m)) * (FreeGroup.of x) ^ m) *
            (((FreeGroup.of x) ^ m)⁻¹) := by
              rw [pow_add]
      _ = (FreeGroup.of x) ^ (n - m) := by simp only [mul_assoc, mul_inv_cancel, mul_one]
  exact hcalc ▸ hrel

/--
The representatives built from minimal generator powers form a right partial Schreier
transversal.
-/
theorem isRightPartialSchreierTransversal_generatorPowers_of_minimalPower
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} (x : X) {N : ℕ}
    (hN : 0 < N)
    (hmin : ∀ m : ℕ, 0 < m → m < N → (FreeGroup.of x) ^ m ∉ L) :
    IsRightPartialSchreierTransversal (X := X) L
      (Set.range fun i : Fin N => (FreeGroup.of x) ^ (i : ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨⟨0, hN⟩, by simp only [pow_zero]⟩
  · intro t ht u hu
    rcases ht with ⟨i, rfl⟩
    rcases hu with ⟨m, hm, rfl⟩
    have hm' : m ≤ (i : ℕ) := by
      simpa [FreeGroup.toWord_of_pow, List.length_replicate] using hm
    refine ⟨⟨m, lt_of_le_of_lt hm' i.2⟩, ?_⟩
    rw [FreeGroup.toWord_of_pow, List.take_replicate, min_eq_left hm',
      ← FreeGroup.toWord_of_pow, FreeGroup.mk_toWord]
  · intro a b ha hb hEq
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    have hij : (i : ℕ) = j := by
      by_contra hij
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · have hmem : (FreeGroup.of x) ^ ((j : ℕ) - i) ∈ L :=
          generatorPower_sub_mem_of_rightQuotient_eq (X := X) (L := L) x
            (Nat.le_of_lt hijlt) hEq
        exact hmin ((j : ℕ) - i) (Nat.sub_pos_of_lt hijlt)
          (lt_of_le_of_lt (Nat.sub_le _ _) j.2) hmem
      · have hmem : (FreeGroup.of x) ^ ((i : ℕ) - j) ∈ L :=
          generatorPower_sub_mem_of_rightQuotient_eq (X := X) (L := L) x
            (Nat.le_of_lt hjilt) hEq.symm
        exact hmin ((i : ℕ) - j) (Nat.sub_pos_of_lt hjilt)
          (lt_of_le_of_lt (Nat.sub_le _ _) i.2) hmem
    have hij' : i = j := Fin.ext hij
    subst hij'
    rfl

/--
Right multiplication on right cosets, expressed as a left action via \(g \cdot [t] = [t *
g{}^{-1}]\). This is the action naturally compatible with Schreier generators of the form \(t x
(\widetilde{t x}){}^{-1}\).
-/
instance rightCosetLeftMulActionByInverse {X : Type u} (L : Subgroup (FreeGroup X)) :
    MulAction (FreeGroup X) (Quotient (QuotientGroup.rightRel L)) :=
  _root_.ReidemeisterSchreier.rightCosetMulAction L

attribute [-instance] rightCosetLeftMulActionByInverse

/-- The Schreier generator component of the corresponding rewriting map. -/
@[simp] theorem rightCosetLeftMulActionByInverse_mk_smul {X : Type u}
    (L : Subgroup (FreeGroup X)) (g a : FreeGroup X) :
    g • (Quotient.mk'' a : Quotient (QuotientGroup.rightRel L)) =
      Quotient.mk'' (a * g⁻¹) :=
  rfl

end RightSchreierTransversals

end ReidemeisterSchreier.Discrete.OpenSubgroups
