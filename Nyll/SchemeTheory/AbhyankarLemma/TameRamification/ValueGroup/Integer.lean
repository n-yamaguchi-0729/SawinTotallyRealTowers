/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup
import Mathlib.Data.Int.ModEq

/-!
# Integer value-group arithmetic

The tame Abhyankar value-group step reduces to lcm arithmetic in a rank-one
integer value group.  This file isolates that arithmetic without assuming any
field-theoretic ramification comparison.
-/

noncomputable section

namespace TameAbhyankar

open LocalFieldTheory.DiscreteValuationField

/-- Membership in both integer-multiple value subgroups is the same as
membership in the subgroup cut out by the lcm.  This is the integer
divisibility core of the value-group computation used by tame Abhyankar. -/
theorem int_lcm_dvd_iff_dvd_and_dvd (d e n : ℤ) :
    ((d.lcm e : ℕ) : ℤ) ∣ n ↔ d ∣ n ∧ e ∣ n := by
  have h :=
    (Int.modEq_and_modEq_iff_modEq_lcm
      (a := n) (b := 0) (m := d) (n := e))
  simpa [Int.modEq_iff_dvd] using h.symm

/-- Introduction form for the integer value-group lcm divisibility. -/
theorem int_lcm_dvd_of_dvd_of_dvd {d e n : ℤ}
    (hd : d ∣ n) (he : e ∣ n) :
    ((d.lcm e : ℕ) : ℤ) ∣ n :=
  (int_lcm_dvd_iff_dvd_and_dvd d e n).2 ⟨hd, he⟩

/-- Left projection from lcm divisibility in the integer value group. -/
theorem int_dvd_left_of_lcm_dvd {d e n : ℤ}
    (h : ((d.lcm e : ℕ) : ℤ) ∣ n) :
    d ∣ n :=
  ((int_lcm_dvd_iff_dvd_and_dvd d e n).1 h).1

/-- Right projection from lcm divisibility in the integer value group. -/
theorem int_dvd_right_of_lcm_dvd {d e n : ℤ}
    (h : ((d.lcm e : ℕ) : ℤ) ∣ n) :
    e ∣ n :=
  ((int_lcm_dvd_iff_dvd_and_dvd d e n).1 h).2

/-- Existing `LocalFieldTheory.DiscreteValuationField.integerMultipleSubgroup` form of the lcm
value-group intersection. -/
theorem mem_integerMultipleSubgroup_lcm_iff
    (d e : ℤ) (n : Multiplicative ℤ) :
    n ∈ integerMultipleSubgroup ((d.lcm e : ℕ) : ℤ) ↔
      n ∈ integerMultipleSubgroup d ∧
        n ∈ integerMultipleSubgroup e := by
  rw [mem_integerMultipleSubgroup_iff,
    mem_integerMultipleSubgroup_iff,
    mem_integerMultipleSubgroup_iff]
  exact int_lcm_dvd_iff_dvd_and_dvd d e (Multiplicative.toAdd n)

/-- The subgroup of value exponents divisible by `lcm d e` is the intersection
of the subgroups divisible by `d` and by `e`. -/
theorem integerMultipleSubgroup_lcm_eq_inf (d e : ℤ) :
    integerMultipleSubgroup ((d.lcm e : ℕ) : ℤ) =
      integerMultipleSubgroup d ⊓ integerMultipleSubgroup e := by
  ext n
  change n ∈ integerMultipleSubgroup ((d.lcm e : ℕ) : ℤ) ↔
    n ∈ integerMultipleSubgroup d ∧ n ∈ integerMultipleSubgroup e
  exact mem_integerMultipleSubgroup_lcm_iff d e n

/-- Introduction form for the lcm value-subgroup intersection. -/
theorem mem_integerMultipleSubgroup_lcm_of_mem_left_of_mem_right
    {d e : ℤ} {n : Multiplicative ℤ}
    (hd : n ∈ integerMultipleSubgroup d)
    (he : n ∈ integerMultipleSubgroup e) :
    n ∈ integerMultipleSubgroup ((d.lcm e : ℕ) : ℤ) :=
  (mem_integerMultipleSubgroup_lcm_iff d e n).2 ⟨hd, he⟩

/-- Inclusion between integer-multiple value subgroups is exactly divisibility
of the corresponding integer steps, with the order reversed. -/
theorem integerMultipleSubgroup_le_iff_dvd (a b : ℤ) :
    integerMultipleSubgroup b ≤ integerMultipleSubgroup a ↔ a ∣ b := by
  constructor
  · intro h
    have hb : Multiplicative.ofAdd b ∈ integerMultipleSubgroup b := by
      rw [ofAdd_mem_integerMultipleSubgroup_iff]
    have ha := h hb
    simpa using ha
  · intro h
    exact integerMultipleSubgroup_le_of_dvd h

/-- If an integer-multiple value subgroup lies in the intersection of the
two lower value-step subgroups, its step is divisible by the lcm of the two
lower steps. -/
theorem integerMultipleSubgroup_le_inf_iff_lcm_dvd (n d e : ℤ) :
    integerMultipleSubgroup n ≤ integerMultipleSubgroup d ⊓
        integerMultipleSubgroup e ↔
      ((d.lcm e : ℕ) : ℤ) ∣ n := by
  rw [← integerMultipleSubgroup_lcm_eq_inf d e]
  exact integerMultipleSubgroup_le_iff_dvd ((d.lcm e : ℕ) : ℤ) n

/-- Introduction form for extracting lcm divisibility from two
integer-multiple subgroup inclusions. -/
theorem int_lcm_dvd_of_integerMultipleSubgroup_le_of_le
    {n d e : ℤ}
    (hd : integerMultipleSubgroup n ≤ integerMultipleSubgroup d)
    (he : integerMultipleSubgroup n ≤ integerMultipleSubgroup e) :
    ((d.lcm e : ℕ) : ℤ) ∣ n :=
  (integerMultipleSubgroup_le_inf_iff_lcm_dvd n d e).1 (le_inf hd he)

end TameAbhyankar

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

open TameAbhyankar

variable {G : Type _} [Group G]

/-- The values attained by a subgroup form a sub-value group of the ambient
value subgroup. -/
theorem subgroupValueSubgroup_le_valueSubgroup
    (V : MultiplicativeIntegerValuation G) (S : Subgroup G) :
    V.subgroupValueSubgroup S ≤ V.valueSubgroup := by
  intro n hn
  rw [V.mem_subgroupValueSubgroup_iff S n] at hn
  rcases hn with ⟨x, _hx, hxn⟩
  rw [V.mem_valueSubgroup_iff]
  exact ⟨x, hxn⟩

/-- Introduction form for lcm divisibility on a subgroup value image. -/
theorem subgroupValueSubgroup_le_integerMultipleSubgroup_lcm
    (V : MultiplicativeIntegerValuation G) (S : Subgroup G) {d e : ℤ}
    (hd : V.subgroupValueSubgroup S ≤ integerMultipleSubgroup d)
    (he : V.subgroupValueSubgroup S ≤ integerMultipleSubgroup e) :
    V.subgroupValueSubgroup S ≤
      integerMultipleSubgroup ((d.lcm e : ℕ) : ℤ) := by
  rw [integerMultipleSubgroup_lcm_eq_inf]
  exact le_inf hd he

/-- Membership of the generator `ofAdd n` in a subgroup value image generates
the whole integer-multiple subgroup cut out by `n`. -/
theorem integerMultipleSubgroup_le_subgroupValueSubgroup_of_ofAdd_mem
    (V : MultiplicativeIntegerValuation G) {S : Subgroup G} {n : ℤ}
    (hn : Multiplicative.ofAdd n ∈ V.subgroupValueSubgroup S) :
    integerMultipleSubgroup n ≤ V.subgroupValueSubgroup S :=
  V.integerMultipleSubgroup_le_subgroupValueSubgroup_of_exists_mem_val
    ((V.ofAdd_mem_subgroupValueSubgroup_iff S n).1 hn)

/-- The integer-multiple subgroup generated by `n` lies in a subgroup value
image exactly when the generator `ofAdd n` lies in that image. -/
theorem integerMultipleSubgroup_le_subgroupValueSubgroup_iff_ofAdd_mem
    (V : MultiplicativeIntegerValuation G) (S : Subgroup G) (n : ℤ) :
    integerMultipleSubgroup n ≤ V.subgroupValueSubgroup S ↔
      Multiplicative.ofAdd n ∈ V.subgroupValueSubgroup S := by
  constructor
  · intro h
    have hn : Multiplicative.ofAdd n ∈ integerMultipleSubgroup n := by
      rw [ofAdd_mem_integerMultipleSubgroup_iff]
    exact h hn
  · intro hn
    exact V.integerMultipleSubgroup_le_subgroupValueSubgroup_of_ofAdd_mem hn

/-- The subgroup-image inclusion required in the value-group comparison is
equivalent to producing an actual subgroup element with valuation `n`. -/
theorem integerMultipleSubgroup_le_subgroupValueSubgroup_iff_exists_mem_val
    (V : MultiplicativeIntegerValuation G) (S : Subgroup G) (n : ℤ) :
    integerMultipleSubgroup n ≤ V.subgroupValueSubgroup S ↔
      ∃ x : G, x ∈ S ∧ V.val x = n := by
  rw [V.integerMultipleSubgroup_le_subgroupValueSubgroup_iff_ofAdd_mem S n,
    V.ofAdd_mem_subgroupValueSubgroup_iff S n]

/-- Subgroup-image sandwich form: if an integer-multiple subgroup maps into a
subgroup value image, and that image lies in two lower value-step subgroups,
then the image step is divisible by the lcm of the two lower steps. -/
theorem int_lcm_dvd_of_integerMultipleSubgroup_le_subgroupValueSubgroup_of_subgroupValueSubgroup_le
    (V : MultiplicativeIntegerValuation G) {S : Subgroup G} {n d e : ℤ}
    (himage : integerMultipleSubgroup n ≤ V.subgroupValueSubgroup S)
    (hd : V.subgroupValueSubgroup S ≤ integerMultipleSubgroup d)
    (he : V.subgroupValueSubgroup S ≤ integerMultipleSubgroup e) :
    ((d.lcm e : ℕ) : ℤ) ∣ n :=
  int_lcm_dvd_of_integerMultipleSubgroup_le_of_le
    (le_trans himage hd) (le_trans himage he)

/-- Membership form of the subgroup-image lcm sandwich: once the generator
`ofAdd n` lies in the subgroup value image, two lower value-step inclusions for
that image force `n` to be divisible by the lcm of the lower steps. -/
theorem int_lcm_dvd_of_ofAdd_mem_subgroupValueSubgroup_of_subgroupValueSubgroup_le
    (V : MultiplicativeIntegerValuation G) {S : Subgroup G} {n d e : ℤ}
    (hn : Multiplicative.ofAdd n ∈ V.subgroupValueSubgroup S)
    (hd : V.subgroupValueSubgroup S ≤ integerMultipleSubgroup d)
    (he : V.subgroupValueSubgroup S ≤ integerMultipleSubgroup e) :
    ((d.lcm e : ℕ) : ℤ) ∣ n :=
  int_lcm_dvd_of_integerMultipleSubgroup_le_subgroupValueSubgroup_of_subgroupValueSubgroup_le
    V
    (V.integerMultipleSubgroup_le_subgroupValueSubgroup_of_ofAdd_mem hn)
    hd he

/-- A value-subgroup inclusion into an integer-multiple subgroup is exactly a
divisibility statement for every valuation exponent. -/
theorem valueSubgroup_le_integerMultipleSubgroup_iff
    (V : MultiplicativeIntegerValuation G) (d : ℤ) :
    V.valueSubgroup ≤ integerMultipleSubgroup d ↔
      ∀ x : G, d ∣ V.val x := by
  constructor
  · intro h x
    have hxvalue : V.valuationHom x ∈ V.valueSubgroup := by
      rw [V.mem_valueSubgroup_iff]
      exact ⟨x, rfl⟩
    have hx := h hxvalue
    rw [mem_integerMultipleSubgroup_iff] at hx
    simpa
      [_root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.valuationHom]
      using hx
  · intro h n hn
    rw [V.mem_valueSubgroup_iff] at hn
    rcases hn with ⟨x, rfl⟩
    rw [mem_integerMultipleSubgroup_iff]
    simpa
      [_root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.valuationHom]
      using h x

/-- A value subgroup lies in the lcm multiple subgroup exactly when it lies in
both lower multiple subgroups.  This is the subgroup-inclusion form needed when
the ramification-image comparison has produced the two lower value-step
inclusions. -/
theorem valueSubgroup_le_integerMultipleSubgroup_lcm_iff
    (V : MultiplicativeIntegerValuation G) (d e : ℤ) :
    V.valueSubgroup ≤ integerMultipleSubgroup ((d.lcm e : ℕ) : ℤ) ↔
      V.valueSubgroup ≤ integerMultipleSubgroup d ∧
        V.valueSubgroup ≤ integerMultipleSubgroup e := by
  rw [integerMultipleSubgroup_lcm_eq_inf]
  exact le_inf_iff

/-- Introduction form for the lcm value-subgroup inclusion. -/
theorem valueSubgroup_le_integerMultipleSubgroup_lcm
    (V : MultiplicativeIntegerValuation G) {d e : ℤ}
    (hd : V.valueSubgroup ≤ integerMultipleSubgroup d)
    (he : V.valueSubgroup ≤ integerMultipleSubgroup e) :
    V.valueSubgroup ≤ integerMultipleSubgroup ((d.lcm e : ℕ) : ℤ) :=
  (valueSubgroup_le_integerMultipleSubgroup_lcm_iff V d e).2 ⟨hd, he⟩

/-- If the valuation takes the value `n`, then all multiples of `n` lie in the
value subgroup.  This supplies the image-subgroup inclusion used by the
ramification-image comparison from an actual value generator. -/
theorem integerMultipleSubgroup_le_valueSubgroup_of_exists_val
    (V : MultiplicativeIntegerValuation G) {n : ℤ}
    (hn : ∃ x : G, V.val x = n) :
    integerMultipleSubgroup n ≤ V.valueSubgroup := by
  rcases hn with ⟨x, hx⟩
  intro m hm
  rw [mem_integerMultipleSubgroup_iff] at hm
  rcases hm with ⟨k, hk⟩
  rw [V.mem_valueSubgroup_iff]
  refine ⟨x ^ k, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [V.valuationHom_apply, toAdd_ofAdd, V.val_zpow, hx]
  exact (mul_comm k n).trans hk.symm

/-- Membership of `Multiplicative.ofAdd n` in the value subgroup generates the
whole integer-multiple subgroup cut out by `n`. -/
theorem integerMultipleSubgroup_le_valueSubgroup_of_ofAdd_mem
    (V : MultiplicativeIntegerValuation G) {n : ℤ}
    (hn : Multiplicative.ofAdd n ∈ V.valueSubgroup) :
    integerMultipleSubgroup n ≤ V.valueSubgroup :=
  integerMultipleSubgroup_le_valueSubgroup_of_exists_val V
    (V.exists_val_of_ofAdd_mem_valueSubgroup hn)

/-- The whole integer-multiple subgroup generated by `n` lies in the value
subgroup exactly when its generator lies in the value subgroup. -/
theorem integerMultipleSubgroup_le_valueSubgroup_iff_ofAdd_mem
    (V : MultiplicativeIntegerValuation G) (n : ℤ) :
    integerMultipleSubgroup n ≤ V.valueSubgroup ↔
      Multiplicative.ofAdd n ∈ V.valueSubgroup := by
  constructor
  · intro h
    have hn : Multiplicative.ofAdd n ∈ integerMultipleSubgroup n := by
      rw [ofAdd_mem_integerMultipleSubgroup_iff]
    exact h hn
  · intro hn
    exact integerMultipleSubgroup_le_valueSubgroup_of_ofAdd_mem V hn

/-- The image-subgroup inclusion required in the value-group comparison is
equivalent to producing an actual element with valuation `n`. -/
theorem integerMultipleSubgroup_le_valueSubgroup_iff_exists_val
    (V : MultiplicativeIntegerValuation G) (n : ℤ) :
    integerMultipleSubgroup n ≤ V.valueSubgroup ↔ ∃ x : G, V.val x = n := by
  rw [integerMultipleSubgroup_le_valueSubgroup_iff_ofAdd_mem V n,
    V.ofAdd_mem_valueSubgroup_iff n]

/-- If an integer-multiple value subgroup maps into a valuation value subgroup,
and that value subgroup lies in two lower value-step subgroups, then the image
step is divisible by the lcm of the two lower steps. -/
theorem int_lcm_dvd_of_integerMultipleSubgroup_le_valueSubgroup_of_valueSubgroup_le
    (V : MultiplicativeIntegerValuation G) {n d e : ℤ}
    (himage : integerMultipleSubgroup n ≤ V.valueSubgroup)
    (hd : V.valueSubgroup ≤ integerMultipleSubgroup d)
    (he : V.valueSubgroup ≤ integerMultipleSubgroup e) :
    ((d.lcm e : ℕ) : ℤ) ∣ n :=
  int_lcm_dvd_of_integerMultipleSubgroup_le_of_le
    (le_trans himage hd) (le_trans himage he)

/-- Generator form of the value-subgroup sandwich: once the value subgroup has
a value generator `n`, two lower value-step inclusions force `n` to be
divisible by the lcm of the two lower steps. -/
theorem int_lcm_dvd_of_exists_val_of_valueSubgroup_le
    (V : MultiplicativeIntegerValuation G) {n d e : ℤ}
    (hn : ∃ x : G, V.val x = n)
    (hd : V.valueSubgroup ≤ integerMultipleSubgroup d)
    (he : V.valueSubgroup ≤ integerMultipleSubgroup e) :
    ((d.lcm e : ℕ) : ℤ) ∣ n :=
  int_lcm_dvd_of_integerMultipleSubgroup_le_valueSubgroup_of_valueSubgroup_le V
    (integerMultipleSubgroup_le_valueSubgroup_of_exists_val V hn) hd he

/-- Elementwise valuation-exponent form of the lcm criterion. -/
theorem forall_lcm_dvd_val_iff
    (V : MultiplicativeIntegerValuation G) (d e : ℤ) :
    (∀ x : G, ((d.lcm e : ℕ) : ℤ) ∣ V.val x) ↔
      (∀ x : G, d ∣ V.val x) ∧
        (∀ x : G, e ∣ V.val x) := by
  rw [← valueSubgroup_le_integerMultipleSubgroup_iff V
      ((d.lcm e : ℕ) : ℤ),
    ← valueSubgroup_le_integerMultipleSubgroup_iff V d,
    ← valueSubgroup_le_integerMultipleSubgroup_iff V e,
    valueSubgroup_le_integerMultipleSubgroup_lcm_iff V d e]

/-- Introduction form for the elementwise valuation-exponent lcm criterion. -/
theorem lcm_dvd_val_of_dvd_val_of_dvd_val
    (V : MultiplicativeIntegerValuation G) {d e : ℤ}
    (hd : ∀ x : G, d ∣ V.val x)
    (he : ∀ x : G, e ∣ V.val x) :
    ∀ x : G, ((d.lcm e : ℕ) : ℤ) ∣ V.val x :=
  (forall_lcm_dvd_val_iff V d e).2 ⟨hd, he⟩

/-- Elementwise valuation form of the lcm value-subgroup inclusion. -/
theorem valuationHom_mem_integerMultipleSubgroup_lcm_of_mem_left_of_mem_right
    (V : MultiplicativeIntegerValuation G) {d e : ℤ} (x : G)
    (hd : V.valuationHom x ∈ integerMultipleSubgroup d)
    (he : V.valuationHom x ∈ integerMultipleSubgroup e) :
    V.valuationHom x ∈ integerMultipleSubgroup ((d.lcm e : ℕ) : ℤ) :=
  mem_integerMultipleSubgroup_lcm_of_mem_left_of_mem_right hd he

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

namespace LocalFieldTheory.DiscreteValuationField.ValuedNorm

open TameAbhyankar

variable {G H : Type _} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}

/-- A source uniformizer for a valued norm produces a target element whose
valuation is the norm residue degree. -/
theorem exists_val_residueDegree_of_source_uniformizer
    (N : ValuedNorm vG vH) {ϖ : H} (hϖ : vH.IsUniformizer ϖ) :
    ∃ x : G, vG.val x = (N.residueDegree : ℤ) := by
  refine ⟨N.toHom ϖ, ?_⟩
  rw [N.valuation_apply, hϖ, mul_one]

/-- The value subgroup generated by the norm image of a source uniformizer
contains the integer-multiple subgroup cut out by the residue degree. -/
theorem integerMultipleSubgroup_residueDegree_le_valueSubgroup_of_source_uniformizer
    (N : ValuedNorm vG vH) {ϖ : H} (hϖ : vH.IsUniformizer ϖ) :
    integerMultipleSubgroup (N.residueDegree : ℤ) ≤ vG.valueSubgroup :=
  MultiplicativeIntegerValuation.integerMultipleSubgroup_le_valueSubgroup_of_exists_val
    vG (N.exists_val_residueDegree_of_source_uniformizer hϖ)

/-- A lower value-step inclusion forces the valued norm residue degree to be
divisible by that step, once the source valuation has a uniformizer. -/
theorem dvd_residueDegree_of_source_uniformizer_of_valueSubgroup_le
    (N : ValuedNorm vG vH) {ϖ : H} (hϖ : vH.IsUniformizer ϖ)
    {d : ℤ} (hd : vG.valueSubgroup ≤ integerMultipleSubgroup d) :
    d ∣ (N.residueDegree : ℤ) := by
  have hdivs :=
    (MultiplicativeIntegerValuation.valueSubgroup_le_integerMultipleSubgroup_iff
      vG d).1 hd
  have htarget := hdivs (N.toHom ϖ)
  rwa [N.valuation_apply, hϖ, mul_one] at htarget

/-- Two lower value-step inclusions force the valued norm residue degree to be
divisible by their lcm.  This is the norm-image input shape needed by the
tame Abhyankar value-group comparison. -/
theorem lcm_dvd_residueDegree_of_source_uniformizer_of_valueSubgroup_le
    (N : ValuedNorm vG vH) {ϖ : H} (hϖ : vH.IsUniformizer ϖ)
    {d e : ℤ}
    (hd : vG.valueSubgroup ≤ integerMultipleSubgroup d)
    (he : vG.valueSubgroup ≤ integerMultipleSubgroup e) :
    ((d.lcm e : ℕ) : ℤ) ∣ (N.residueDegree : ℤ) :=
  int_lcm_dvd_of_dvd_of_dvd
    (N.dvd_residueDegree_of_source_uniformizer_of_valueSubgroup_le hϖ hd)
    (N.dvd_residueDegree_of_source_uniformizer_of_valueSubgroup_le hϖ he)

/-- With a source uniformizer, the valuation values attained on the valued
norm subgroup are exactly the residue-degree multiples. -/
theorem subgroupValueSubgroup_normSubgroup_eq_integerMultipleSubgroup
    (N : ValuedNorm vG vH) {ϖ : H} (hϖ : vH.IsUniformizer ϖ) :
    vG.subgroupValueSubgroup N.normSubgroup =
      integerMultipleSubgroup (N.residueDegree : ℤ) := by
  ext n
  rw [MultiplicativeIntegerValuation.mem_subgroupValueSubgroup_iff,
    mem_integerMultipleSubgroup_iff]
  constructor
  · rintro ⟨x, hx, hxn⟩
    rw [← hxn, vG.valuationHom_apply, toAdd_ofAdd]
    exact N.residueDegree_dvd_valuation_of_mem_normSubgroup hx
  · intro hn
    rcases
      (N.exists_normSubgroup_val_eq_iff_residueDegree_dvd_of_uniformizer
        hϖ (Multiplicative.toAdd n)).2 hn with
      ⟨x, hx, hval⟩
    refine ⟨x, hx, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [vG.valuationHom_apply, toAdd_ofAdd, hval]

/-- A lower value-step inclusion on the actual valued-norm image forces the
valued norm residue degree to be divisible by that step. -/
theorem dvd_residueDegree_of_source_uniformizer_of_normSubgroupValueSubgroup_le
    (N : ValuedNorm vG vH) {ϖ : H} (hϖ : vH.IsUniformizer ϖ)
    {d : ℤ}
    (hd :
      vG.subgroupValueSubgroup N.normSubgroup ≤ integerMultipleSubgroup d) :
    d ∣ (N.residueDegree : ℤ) := by
  have hnorm :=
    N.subgroupValueSubgroup_normSubgroup_eq_integerMultipleSubgroup hϖ
  have hd' :
      integerMultipleSubgroup (N.residueDegree : ℤ) ≤
        integerMultipleSubgroup d := by
    simpa [← hnorm] using hd
  exact (integerMultipleSubgroup_le_iff_dvd d (N.residueDegree : ℤ)).1 hd'

/-- Two lower value-step inclusions on the actual valued-norm image force the
valued norm residue degree to be divisible by the lcm of those two steps. -/
theorem lcm_dvd_residueDegree_of_source_uniformizer_of_normSubgroupValueSubgroup_le
    (N : ValuedNorm vG vH) {ϖ : H} (hϖ : vH.IsUniformizer ϖ)
    {d e : ℤ}
    (hd :
      vG.subgroupValueSubgroup N.normSubgroup ≤ integerMultipleSubgroup d)
    (he :
      vG.subgroupValueSubgroup N.normSubgroup ≤ integerMultipleSubgroup e) :
    ((d.lcm e : ℕ) : ℤ) ∣ (N.residueDegree : ℤ) :=
  int_lcm_dvd_of_dvd_of_dvd
    (N.dvd_residueDegree_of_source_uniformizer_of_normSubgroupValueSubgroup_le
      hϖ hd)
    (N.dvd_residueDegree_of_source_uniformizer_of_normSubgroupValueSubgroup_le
      hϖ he)

end LocalFieldTheory.DiscreteValuationField.ValuedNorm

end
