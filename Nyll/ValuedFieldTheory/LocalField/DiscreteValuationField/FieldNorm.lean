/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.SetTheory.Cardinal.Finite
public import Nyll.ValuedFieldTheory.LocalField.NormUnits
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Quotients
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.NormFiltration
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup

/-!
# Field norm on unit groups

This file connects mathlib's `Algebra.norm` with the unit-group and valued-norm
APIs used by local CFT.
-/

@[expose] public section

namespace LocalFieldTheory



noncomputable section

universe u v w

namespace DiscreteValuationField

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- The norm subgroup from the top field of a tower lies in the norm subgroup from the
intermediate field. -/
theorem fieldNormSubgroup_le_of_tower
    (E : Type w) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [Module.Free E L] :
    localNormSubgroup K L ≤ localNormSubgroup K E :=
  localNormSubgroup_le_of_tower K E L

/--
Characterizes `z ∈ MonoidHom.ker (normUnits K L)` by the equivalent condition `Algebra.norm K
(z : L) = 1`.
-/
theorem mem_fieldNormUnits_ker_iff_norm_eq_one (z : Lˣ) :
    z ∈ MonoidHom.ker (normUnits K L) ↔
      Algebra.norm K (z : L) = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hz
    exact congrArg (fun u : Kˣ => (u : K)) hz
  · intro hz
    ext
    simpa using hz

/--
Characterizes `x / y ∈ localNormSubgroup K L` by the equivalent condition `y⁻¹ * x ∈
localNormSubgroup K L`.
-/
theorem fieldNormSubgroup_div_mem_iff_inv_mul_mem (x y : Kˣ) :
    x / y ∈ localNormSubgroup K L ↔
      y⁻¹ * x ∈ localNormSubgroup K L := by
  rw [div_eq_mul_inv, mul_comm x y⁻¹]

/--
Characterizes `y⁻¹ * x ∈ localNormSubgroup K L` by the equivalent condition `x / y ∈
localNormSubgroup K L`.
-/
theorem fieldNormSubgroup_inv_mul_mem_iff_div_mem (x y : Kˣ) :
    y⁻¹ * x ∈ localNormSubgroup K L ↔
      x / y ∈ localNormSubgroup K L :=
  (fieldNormSubgroup_div_mem_iff_inv_mul_mem K L x y).symm

/--
Characterizes `x / y ∈ localNormSubgroup K L` by the equivalent condition `∃ z : Lˣ,
normUnits K L z * y = x`.
-/
theorem fieldNormSubgroup_div_mem_iff_exists_norm_mul_eq
    (x y : Kˣ) :
    x / y ∈ localNormSubgroup K L ↔
      ∃ z : Lˣ, normUnits K L z * y = x := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz, div_mul_cancel]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have h := congrArg (fun t : Kˣ => t * y⁻¹) hz
    simpa [div_eq_mul_inv, mul_assoc] using h

/--
Characterizes `y⁻¹ * x ∈ localNormSubgroup K L` by the equivalent condition `∃ z : Lˣ, y *
normUnits K L z = x`.
-/
theorem fieldNormSubgroup_inv_mul_mem_iff_exists_mul_norm_eq
    (x y : Kˣ) :
    y⁻¹ * x ∈ localNormSubgroup K L ↔
      ∃ z : Lˣ, y * normUnits K L z = x := by
  rw [fieldNormSubgroup_inv_mul_mem_iff_div_mem K L x y,
    fieldNormSubgroup_div_mem_iff_exists_norm_mul_eq K L x y]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa [mul_comm, mul_left_comm, mul_assoc] using hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa [mul_comm, mul_left_comm, mul_assoc] using hz⟩

/-- Norm of an element coming from the base field. -/
@[simp] theorem fieldNormUnits_algebraMap (u : Kˣ) :
    normUnits K L (Units.map (algebraMap K L).toMonoidHom u) =
      u ^ Module.finrank K L := by
  ext
  simp [normUnits, Algebra.norm_algebraMap]

/-- Establishes the identity `normUnits K L (Units.map (algebraMap K L).toMonoidHom u) = u`. -/
theorem fieldNormUnits_algebraMap_of_finrank_eq_one
    (hfin : Module.finrank K L = 1) (u : Kˣ) :
    normUnits K L (Units.map (algebraMap K L).toMonoidHom u) = u := by
  simpa [hfin] using fieldNormUnits_algebraMap K L u

/-- Establishes the membership statement `u ^ Module.finrank K L ∈ localNormSubgroup K L`. -/
theorem fieldNormSubgroup_pow_finrank_mem (u : Kˣ) :
    u ^ Module.finrank K L ∈ localNormSubgroup K L :=
  ⟨Units.map (algebraMap K L).toMonoidHom u,
    by rw [fieldNormUnits_algebraMap K L u]⟩

/-- Establishes the identity `localNormSubgroup K L = ⊤`. -/
theorem fieldNormSubgroup_eq_top_of_finrank_eq_one
    (hfin : Module.finrank K L = 1) :
    localNormSubgroup K L = ⊤ := by
  ext u
  constructor
  · intro _
    trivial
  · intro _
    simpa [hfin] using fieldNormSubgroup_pow_finrank_mem K L u

/--
Establishes the identity `(QuotientGroup.mk' (localNormSubgroup K L) u) ^ Module.finrank K L = 1`.
-/
theorem fieldNormQuotient_mk_pow_finrank_eq_one (u : Kˣ) :
    (QuotientGroup.mk' (localNormSubgroup K L) u) ^
        Module.finrank K L = 1 := by
  rw [← (QuotientGroup.mk' (localNormSubgroup K L)).map_pow]
  exact (QuotientGroup.eq_one_iff (N := localNormSubgroup K L)
    (u ^ Module.finrank K L)).2 (fieldNormSubgroup_pow_finrank_mem K L u)

/-- Establishes the identity `q ^ Module.finrank K L = 1`. -/
theorem fieldNormQuotient_pow_finrank_eq_one
    (q : Kˣ ⧸ localNormSubgroup K L) :
    q ^ Module.finrank K L = 1 := by
  rcases QuotientGroup.mk'_surjective (localNormSubgroup K L) q with
    ⟨u, rfl⟩
  exact fieldNormQuotient_mk_pow_finrank_eq_one K L u

/-- Establishes the identity `(QuotientGroup.mk' (localNormSubgroup K L) u) ^ n = 1`. -/
theorem fieldNormQuotient_mk_pow_eq_one_of_finrank_dvd
    {n : ℕ} (hn : Module.finrank K L ∣ n) (u : Kˣ) :
    (QuotientGroup.mk' (localNormSubgroup K L) u) ^ n = 1 := by
  rcases hn with ⟨m, rfl⟩
  rw [pow_mul, fieldNormQuotient_mk_pow_finrank_eq_one K L u, one_pow]

/-- Establishes the identity `q ^ n = 1`. -/
theorem fieldNormQuotient_pow_eq_one_of_finrank_dvd
    {n : ℕ} (hn : Module.finrank K L ∣ n)
    (q : Kˣ ⧸ localNormSubgroup K L) :
    q ^ n = 1 := by
  rcases QuotientGroup.mk'_surjective (localNormSubgroup K L) q with
    ⟨u, rfl⟩
  exact fieldNormQuotient_mk_pow_eq_one_of_finrank_dvd K L hn u

/-- Establishes the identity `q = 1`. -/
theorem fieldNormQuotient_eq_one_of_finrank_eq_one
    (hfin : Module.finrank K L = 1)
    (q : Kˣ ⧸ localNormSubgroup K L) :
    q = 1 := by
  rcases QuotientGroup.mk'_surjective (localNormSubgroup K L) q with
    ⟨u, rfl⟩
  exact (QuotientGroup.eq_one_iff (N := localNormSubgroup K L) u).2
    (by simpa [hfin] using fieldNormSubgroup_pow_finrank_mem K L u)

/-- Establishes the identity `q = r`. -/
theorem fieldNormQuotient_eq_of_finrank_eq_one
    (hfin : Module.finrank K L = 1)
    (q r : Kˣ ⧸ localNormSubgroup K L) :
    q = r := by
  rw [fieldNormQuotient_eq_one_of_finrank_eq_one K L hfin q,
    fieldNormQuotient_eq_one_of_finrank_eq_one K L hfin r]

/-- Package a field norm as a `ValuedNorm` once the valuation formula has been
proved for the concrete extension.  The natural-number argument is not a
second source of extension-invariant data: `hformula` certifies it as the
valuation multiplier (and a source uniformizer makes that multiplier unique). -/
@[reducible] noncomputable def valuedFieldNorm
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    ValuedNorm vK vL where
  toHom := normUnits K L
  residueDegree := residueDegree
  valuation_formula := hformula

/--
Establishes the identity `(valuedFieldNorm K L vK vL residueDegree hformula).toHom =
normUnits K L`.
-/
@[simp] theorem valuedFieldNorm_toHom
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    (valuedFieldNorm K L vK vL residueDegree hformula).toHom =
      normUnits K L :=
  rfl

/--
Establishes the identity `(valuedFieldNorm K L vK vL residueDegree hformula).normSubgroup =
localNormSubgroup K L`.
-/
theorem valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    (valuedFieldNorm K L vK vL residueDegree hformula).normSubgroup =
      localNormSubgroup K L := by
  ext x
  rfl

/-- Concrete cyclic description of the field-norm quotient.  The assumptions
are the valuation formula for the field norm and the assertion that every
target valuation-zero element is already a field norm. -/
noncomputable def fieldNormQuotientEquivZMod
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L) :
    Kˣ ⧸ localNormSubgroup K L ≃* Multiplicative (ZMod residueDegree) :=
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = localNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  have hzero' : vK.zeroSubgroup ≤ N.normSubgroup := by
    rw [hnorm]
    exact hzero
  (QuotientGroup.quotientMulEquivOfEq hnorm.symm).trans
    (N.normQuotientEquivZMod hϖK hϖL hzero')

/--
Establishes the identity `fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL
hzero (QuotientGroup.mk' (localNormSubgroup K L) x) = Multiplicative.ofAdd ((vK.val x : ℤ) : ZMod
residueDegree)`.
-/
@[simp] theorem fieldNormQuotientEquivZMod_mk
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (x : Kˣ) :
    fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero
        (QuotientGroup.mk' (localNormSubgroup K L) x) =
      Multiplicative.ofAdd ((vK.val x : ℤ) : ZMod residueDegree) := by
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = localNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  have hzero' : vK.zeroSubgroup ≤ N.normSubgroup := by
    rw [hnorm]
    exact hzero
  unfold fieldNormQuotientEquivZMod
  rw [MulEquiv.trans_apply, QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  simpa [N, valuedFieldNorm] using
    N.normQuotientEquivZMod_mk hϖK hϖL hzero' x

/--
`fieldNormQuotientEquivZMod_uniformizer` satisfies the integer-power formula
`fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL hzero (QuotientGroup.mk'
(localNormSubgroup K L) (ϖK ^ n)) = Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)`.
-/
@[simp] theorem fieldNormQuotientEquivZMod_uniformizer_zpow
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (n : ℤ) :
    fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero
        (QuotientGroup.mk' (localNormSubgroup K L) (ϖK ^ n)) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree) := by
  rw [fieldNormQuotientEquivZMod_mk K L vK vL residueDegree
      hformula hϖK hϖL hzero (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK n]

/--
`fieldNormQuotientEquivZMod_uniformizerClass` satisfies the integer-power formula
`fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL hzero ((QuotientGroup.mk'
(localNormSubgroup K L) ϖK) ^ n) = Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)`.
-/
@[simp] theorem fieldNormQuotientEquivZMod_uniformizerClass_zpow
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (n : ℤ) :
    fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero
        ((QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ n) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree) := by
  have hpow : QuotientGroup.mk' (localNormSubgroup K L) (ϖK ^ n) =
      (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ n :=
    map_zpow (QuotientGroup.mk' (localNormSubgroup K L)) ϖK n
  rw [← hpow,
    fieldNormQuotientEquivZMod_uniformizer_zpow K L vK vL
      residueDegree hformula hϖK hϖL hzero n]

/--
Establishes the identity `(fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL
hzero).symm (Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)) = QuotientGroup.mk'
(localNormSubgroup K L) (ϖK ^ n)`.
-/
@[simp] theorem fieldNormQuotientEquivZMod_symm_mk_ofAdd
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (n : ℤ) :
    (fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero).symm
        (Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)) =
      QuotientGroup.mk' (localNormSubgroup K L) (ϖK ^ n) := by
  apply (fieldNormQuotientEquivZMod K L vK vL residueDegree
    hformula hϖK hϖL hzero).injective
  rw [MulEquiv.apply_symm_apply,
    fieldNormQuotientEquivZMod_uniformizer_zpow K L vK vL
      residueDegree hformula hϖK hϖL hzero n]

/-- Cardinality form of the concrete field-norm quotient computation. -/
theorem cardinalMk_fieldNormQuotient_eq_residueDegree
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    [NeZero residueDegree] :
    Cardinal.mk (Kˣ ⧸ localNormSubgroup K L) = residueDegree := by
  let e := fieldNormQuotientEquivZMod K L vK vL residueDegree
    hformula hϖK hϖL hzero
  calc
    Cardinal.mk (Kˣ ⧸ localNormSubgroup K L) =
        Cardinal.lift (Cardinal.mk (Multiplicative (ZMod residueDegree))) :=
      by simpa only [Cardinal.lift_id'] using Cardinal.mk_congr_lift e.toEquiv
    _ = residueDegree := by
      simp only [Cardinal.mk_fintype, Cardinal.lift_natCast]
      rw [← Nat.card_eq_fintype_card,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod residueDegree) ≃
          ZMod residueDegree), Nat.card_zmod]

/-- Field-norm value-image criterion: an integer is attained as the valuation
of a field norm exactly when it is divisible by the residue degree. -/
theorem exists_mem_fieldNormSubgroup_val_eq_iff_residueDegree_dvd
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL) (n : ℤ) :
    (∃ x : Kˣ, x ∈ localNormSubgroup K L ∧ vK.val x = n) ↔
      (residueDegree : ℤ) ∣ n := by
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = localNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  simpa [N, valuedFieldNorm, hnorm] using
    (N.exists_normSubgroup_val_eq_iff_residueDegree_dvd_of_uniformizer
      hϖL n)

/-- The value image of the field-norm subgroup is exactly `fℤ`. -/
theorem fieldNormSubgroup_valueImage_eq_residueDegree
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL) :
    vK.subgroupValueSubgroup (localNormSubgroup K L) =
      integerMultipleSubgroup (residueDegree : ℤ) := by
  apply le_antisymm
  · refine
      (MultiplicativeIntegerValuation.subgroupValueSubgroup_le_integerMultipleSubgroup_iff
        vK (localNormSubgroup K L) (residueDegree : ℤ)).2 ?_
    intro x hx
    let N := valuedFieldNorm K L vK vL residueDegree hformula
    have hnorm : N.normSubgroup = localNormSubgroup K L := by
      simpa [N] using
        valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
          K L vK vL residueDegree hformula
    have hx' : x ∈ N.normSubgroup := by
      simpa [hnorm] using hx
    simpa [N, valuedFieldNorm] using
      N.residueDegree_dvd_valuation_of_mem_normSubgroup hx'
  · intro n hn
    rw [mem_integerMultipleSubgroup_iff] at hn
    rcases
      (exists_mem_fieldNormSubgroup_val_eq_iff_residueDegree_dvd
        K L vK vL residueDegree hformula hϖL (Multiplicative.toAdd n)).2
        hn with
      ⟨x, hx, hval⟩
    rw [vK.mem_subgroupValueSubgroup_iff]
    exact ⟨x, hx, by rw [vK.valuationHom_apply, hval, ofAdd_toAdd]⟩

/--
Characterizes `x ∈ localNormSubgroup K L` by the equivalent condition `(residueDegree : ℤ) ∣
vK.val x`.
-/
theorem mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L) (x : Kˣ) :
    x ∈ localNormSubgroup K L ↔ (residueDegree : ℤ) ∣ vK.val x := by
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = localNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  have hzero' : vK.zeroSubgroup ≤ N.normSubgroup := by
    rw [hnorm]
    exact hzero
  simpa [N, valuedFieldNorm, hnorm] using
    (N.mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖL hzero' x)

/-- Establishes the divisibility statement `(residueDegree : ℤ) ∣ vK.val x`. -/
theorem fieldNormSubgroup_residueDegree_dvd_val_of_mem
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {x : Kˣ} (hx : x ∈ localNormSubgroup K L) :
    (residueDegree : ℤ) ∣ vK.val x := by
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = localNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  have hx' : x ∈ N.normSubgroup := by
    simpa [hnorm] using hx
  simpa [N, valuedFieldNorm] using
    N.residueDegree_dvd_valuation_of_mem_normSubgroup hx'

/-- Establishes the membership statement `x ∈ localNormSubgroup K L`. -/
theorem fieldNormSubgroup_mem_of_residueDegree_dvd_val_of_zeroSubgroup_le
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    {x : Kˣ} (hx : (residueDegree : ℤ) ∣ vK.val x) :
    x ∈ localNormSubgroup K L :=
  (mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
    K L vK vL residueDegree hformula hϖL hzero x).2 hx

/--
Characterizes `x / y ∈ localNormSubgroup K L` by the equivalent condition `(residueDegree : ℤ) ∣
vK.val x - vK.val y`.
-/
theorem fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (x y : Kˣ) :
    x / y ∈ localNormSubgroup K L ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      K L vK vL residueDegree hformula hϖL hzero (x / y),
    vK.val_div]

/--
Characterizes `y⁻¹ * x ∈ localNormSubgroup K L` by the equivalent condition `(residueDegree : ℤ) ∣
vK.val x - vK.val y`.
-/
theorem fieldNormSubgroup_inv_mul_mem_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (x y : Kˣ) :
    y⁻¹ * x ∈ localNormSubgroup K L ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [fieldNormSubgroup_inv_mul_mem_iff_div_mem K L x y,
    fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero x y]

/-- Under the standard valuation formula and valuation-zero norm-surjectivity,
the norm equation `N z = x` is solvable exactly when `f` divides `v(x)`. -/
theorem exists_fieldNormUnits_eq_iff_residueDegree_dvd_val
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L) (x : Kˣ) :
    (∃ z : Lˣ, normUnits K L z = x) ↔
      (residueDegree : ℤ) ∣ vK.val x := by
  rw [← (MonoidHom.mem_range (f := normUnits K L))]
  change x ∈ localNormSubgroup K L ↔ (residueDegree : ℤ) ∣ vK.val x
  exact mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
    K L vK vL residueDegree hformula hϖL hzero x

/-- Establishes the identity `∃ z : Lˣ, normUnits K L z = x`. -/
theorem exists_fieldNormUnits_eq_of_residueDegree_dvd_val
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    {x : Kˣ} (hx : (residueDegree : ℤ) ∣ vK.val x) :
    ∃ z : Lˣ, normUnits K L z = x :=
  (exists_fieldNormUnits_eq_iff_residueDegree_dvd_val
    K L vK vL residueDegree hformula hϖL hzero x).2 hx

/-- Difference form of the concrete norm equation criterion. -/
theorem exists_fieldNormUnits_eq_div_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (x y : Kˣ) :
    (∃ z : Lˣ, normUnits K L z = x / y) ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [← (MonoidHom.mem_range (f := normUnits K L))]
  change x / y ∈ localNormSubgroup K L ↔
    (residueDegree : ℤ) ∣ vK.val x - vK.val y
  exact fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
    K L vK vL residueDegree hformula hϖL hzero x y

/-- Multiplicative equation form of the concrete norm-lift criterion. -/
theorem exists_fieldNormUnits_mul_eq_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (x y : Kˣ) :
    (∃ z : Lˣ, normUnits K L z * y = x) ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [← fieldNormSubgroup_div_mem_iff_exists_norm_mul_eq K L x y,
    fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero x y]

/-- Left-multiplicative equation form of the concrete norm-lift criterion. -/
theorem exists_mul_fieldNormUnits_eq_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (x y : Kˣ) :
    (∃ z : Lˣ, y * normUnits K L z = x) ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [← fieldNormSubgroup_inv_mul_mem_iff_exists_mul_norm_eq K L x y,
    fieldNormSubgroup_inv_mul_mem_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero x y]

/--
Characterizes `QuotientGroup.mk' (localNormSubgroup K L) x = 1` by the equivalent condition
`(residueDegree : ℤ) ∣ vK.val x`.
-/
theorem fieldNormQuotient_mk_eq_one_iff_residueDegree_dvd_val
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (x : Kˣ) :
    QuotientGroup.mk' (localNormSubgroup K L) x = 1 ↔
      (residueDegree : ℤ) ∣ vK.val x := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      K L vK vL residueDegree hformula hϖL hzero x]

/--
Characterizes `QuotientGroup.mk' (localNormSubgroup K L) x = QuotientGroup.mk' (localNormSubgroup
K L) y` by the equivalent condition `(residueDegree : ℤ) ∣ vK.val x - vK.val y`.
-/
theorem fieldNormQuotient_mk_eq_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (x y : Kˣ) :
    QuotientGroup.mk' (localNormSubgroup K L) x =
        QuotientGroup.mk' (localNormSubgroup K L) y ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
    fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero x y]

/--
Characterizes `ϖK ^ n ∈ localNormSubgroup K L` by the equivalent condition `(residueDegree : ℤ) ∣
n`.
-/
theorem fieldNormSubgroup_uniformizer_zpow_mem_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (n : ℤ) :
    ϖK ^ n ∈ localNormSubgroup K L ↔
      (residueDegree : ℤ) ∣ n := by
  rw [mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      K L vK vL residueDegree hformula hϖL hzero (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK n]

/--
Characterizes `ϖK ^ m / ϖK ^ n ∈ localNormSubgroup K L` by the equivalent condition
`(residueDegree : ℤ) ∣ m - n`.
-/
theorem fieldNormSubgroup_uniformizer_zpow_div_mem_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (m n : ℤ) :
    ϖK ^ m / ϖK ^ n ∈ localNormSubgroup K L ↔
      (residueDegree : ℤ) ∣ m - n := by
  rw [fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero (ϖK ^ m) (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK m,
    vK.val_uniformizer_zpow hϖK n]

/--
Establishes the identity `QuotientGroup.mk' (localNormSubgroup K L) x = QuotientGroup.mk'
(localNormSubgroup K L) (ϖK ^ vK.val x)`.
-/
theorem fieldNormQuotient_mk_eq_uniformizer_zpow_val
    (vK : MultiplicativeIntegerValuation Kˣ)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L) (x : Kˣ) :
    QuotientGroup.mk' (localNormSubgroup K L) x =
      QuotientGroup.mk' (localNormSubgroup K L) (ϖK ^ vK.val x) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
  exact hzero ((vK.div_mem_zeroSubgroup_iff x (ϖK ^ vK.val x)).2
    (by rw [vK.val_uniformizer_zpow hϖK (vK.val x)]))

/--
Establishes the identity `QuotientGroup.mk' (localNormSubgroup K L) x = (QuotientGroup.mk'
(localNormSubgroup K L) ϖK) ^ vK.val x`.
-/
theorem fieldNormQuotient_mk_eq_uniformizerClass_zpow_val
    (vK : MultiplicativeIntegerValuation Kˣ)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L) (x : Kˣ) :
    QuotientGroup.mk' (localNormSubgroup K L) x =
      (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ vK.val x := by
  exact (fieldNormQuotient_mk_eq_uniformizer_zpow_val
    K L vK hϖK hzero x).trans
      (map_zpow (QuotientGroup.mk' (localNormSubgroup K L)) ϖK (vK.val x))

/--
Characterizes `QuotientGroup.mk' (localNormSubgroup K L) x = QuotientGroup.mk' (localNormSubgroup
K L) (ϖK ^ n)` by the equivalent condition `(residueDegree : ℤ) ∣ vK.val x - n`.
-/
theorem fieldNormQuotient_mk_eq_uniformizer_zpow_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (x : Kˣ) (n : ℤ) :
    QuotientGroup.mk' (localNormSubgroup K L) x =
        QuotientGroup.mk' (localNormSubgroup K L) (ϖK ^ n) ↔
      (residueDegree : ℤ) ∣ vK.val x - n := by
  rw [fieldNormQuotient_mk_eq_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero x (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK n]

/--
Characterizes `QuotientGroup.mk' (localNormSubgroup K L) x = (QuotientGroup.mk' (localNormSubgroup
K L) ϖK) ^ n` by the equivalent condition `(residueDegree : ℤ) ∣ vK.val x - n`.
-/
theorem fieldNormQuotient_mk_eq_uniformizerClass_zpow_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (x : Kˣ) (n : ℤ) :
    QuotientGroup.mk' (localNormSubgroup K L) x =
        (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ n ↔
      (residueDegree : ℤ) ∣ vK.val x - n := by
  have hpow : QuotientGroup.mk' (localNormSubgroup K L) (ϖK ^ n) =
      (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ n :=
    map_zpow (QuotientGroup.mk' (localNormSubgroup K L)) ϖK n
  rw [← hpow]
  exact fieldNormQuotient_mk_eq_uniformizer_zpow_iff
    K L vK vL residueDegree hformula hϖK hϖL hzero x n

/--
Characterizes `(QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ m = (QuotientGroup.mk'
(localNormSubgroup K L) ϖK) ^ n` by the equivalent condition `(residueDegree : ℤ) ∣ m - n`.
-/
theorem fieldNormQuotient_uniformizerClass_zpow_eq_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (m n : ℤ) :
    (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ m =
        (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ n ↔
      (residueDegree : ℤ) ∣ m - n := by
  have hpow (k : ℤ) : QuotientGroup.mk' (localNormSubgroup K L) (ϖK ^ k) =
      (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ k :=
    map_zpow (QuotientGroup.mk' (localNormSubgroup K L)) ϖK k
  rw [← hpow m, ← hpow n,
    fieldNormQuotient_mk_eq_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero (ϖK ^ m) (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK m,
    vK.val_uniformizer_zpow hϖK n]

/--
Characterizes `(QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ n = 1` by the equivalent condition
`(residueDegree : ℤ) ∣ n`.
-/
theorem fieldNormQuotient_uniformizerClass_zpow_eq_one_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (n : ℤ) :
    (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ n = 1 ↔
      (residueDegree : ℤ) ∣ n := by
  have hpow : QuotientGroup.mk' (localNormSubgroup K L) (ϖK ^ n) =
      (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ n :=
    map_zpow (QuotientGroup.mk' (localNormSubgroup K L)) ϖK n
  rw [← hpow,
    fieldNormQuotient_mk_eq_one_iff_residueDegree_dvd_val
      K L vK vL residueDegree hformula hϖL hzero (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK n]

/--
Establishes the identity `(QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ (residueDegree : ℤ) =
1`.
-/
theorem fieldNormQuotient_uniformizerClass_zpow_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L) :
    (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^
        (residueDegree : ℤ) = 1 := by
  rw [fieldNormQuotient_uniformizerClass_zpow_eq_one_iff
      K L vK vL residueDegree hformula hϖK hϖL hzero
      (residueDegree : ℤ)]

/-- The concrete field-norm quotient is generated by the class of any target
uniformizer under the standard valuation-zero norm-surjectivity hypothesis. -/
theorem fieldNormQuotient_generated_by_uniformizerClass
    (vK : MultiplicativeIntegerValuation Kˣ)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (q : Kˣ ⧸ localNormSubgroup K L) :
    ∃ n : ℤ,
      q = (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ n := by
  refine QuotientGroup.induction_on q ?_
  intro x
  change ∃ n : ℤ,
    QuotientGroup.mk' (localNormSubgroup K L) x =
      (QuotientGroup.mk' (localNormSubgroup K L) ϖK) ^ n
  exact ⟨vK.val x,
    fieldNormQuotient_mk_eq_uniformizerClass_zpow_val
      K L vK hϖK hzero x⟩

/--
Establishes the identity `Subgroup.closure ({QuotientGroup.mk' (localNormSubgroup K L) ϖK} : Set
(Kˣ ⧸ localNormSubgroup K L)) = ⊤`.
-/
theorem fieldNormQuotient_closure_uniformizerClass_eq_top
    (vK : MultiplicativeIntegerValuation Kˣ)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L) :
    Subgroup.closure
        ({QuotientGroup.mk' (localNormSubgroup K L) ϖK} :
          Set (Kˣ ⧸ localNormSubgroup K L)) =
      ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro q hq
    rcases fieldNormQuotient_generated_by_uniformizerClass
        K L vK hϖK hzero q with
      ⟨n, hqpow⟩
    rw [hqpow]
    exact Subgroup.zpow_mem
      (Subgroup.closure
        ({QuotientGroup.mk' (localNormSubgroup K L) ϖK} :
          Set (Kˣ ⧸ localNormSubgroup K L)))
      (Subgroup.subset_closure (Set.mem_singleton _)) n

/-- Establishes the identity `localNormSubgroup K L = ⊤`. -/
theorem fieldNormSubgroup_eq_top_of_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (hres : residueDegree = 1) :
    localNormSubgroup K L = ⊤ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact
      fieldNormSubgroup_mem_of_residueDegree_dvd_val_of_zeroSubgroup_le
        K L vK vL residueDegree hformula hϖL hzero
        (by rw [hres]; exact one_dvd (vK.val x))

/-- The specified map is surjective: `Function.Surjective (normUnits K L)`. -/
theorem fieldNormUnits_surjective_of_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (hres : residueDegree = 1) :
    Function.Surjective (normUnits K L) := by
  exact MonoidHom.range_eq_top.mp
    (fieldNormSubgroup_eq_top_of_residueDegree_eq_one
      K L vK vL residueDegree hformula hϖL hzero hres)

/-- Under the standard valuation formula and valuation-zero norm-surjectivity,
the field norm on units is surjective exactly in residue degree one. -/
theorem fieldNormUnits_surjective_iff_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L) :
    Function.Surjective (normUnits K L) ↔ residueDegree = 1 := by
  constructor
  · intro hsurj
    have hvalϖK : vK.val ϖK = 1 := hϖK
    rcases hsurj ϖK with ⟨z, hz⟩
    have hmem : ϖK ∈ localNormSubgroup K L := ⟨z, hz⟩
    have hdiv : (residueDegree : ℤ) ∣ (1 : ℤ) := by
      simpa [hvalϖK] using
        fieldNormSubgroup_residueDegree_dvd_val_of_mem
          K L vK vL residueDegree hformula hmem
    have hInt : (residueDegree : ℤ) = 1 :=
      Int.eq_one_of_dvd_one (by exact_mod_cast Nat.zero_le residueDegree) hdiv
    exact_mod_cast hInt
  · intro hres
    exact fieldNormUnits_surjective_of_residueDegree_eq_one
      K L vK vL residueDegree hformula hϖL hzero hres

/-- Subgroup form of the residue-degree-one norm-surjectivity criterion. -/
theorem fieldNormSubgroup_eq_top_iff_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L) :
    localNormSubgroup K L = ⊤ ↔ residueDegree = 1 := by
  exact (MonoidHom.range_eq_top (f := normUnits K L)).trans
    (fieldNormUnits_surjective_iff_residueDegree_eq_one
      K L vK vL residueDegree hformula hϖK hϖL hzero)

/-- Establishes the identity `q = 1`. -/
theorem fieldNormQuotient_eq_one_of_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (hres : residueDegree = 1)
    (q : Kˣ ⧸ localNormSubgroup K L) :
    q = 1 := by
  rcases QuotientGroup.mk'_surjective (localNormSubgroup K L) q with
    ⟨x, rfl⟩
  exact (fieldNormQuotient_mk_eq_one_iff_residueDegree_dvd_val
    K L vK vL residueDegree hformula hϖL hzero x).2
      (by rw [hres]; exact one_dvd (vK.val x))

/-- Establishes the identity `q = r`. -/
theorem fieldNormQuotient_eq_of_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L)
    (hres : residueDegree = 1)
    (q r : Kˣ ⧸ localNormSubgroup K L) :
    q = r := by
  rw [fieldNormQuotient_eq_one_of_residueDegree_eq_one
      K L vK vL residueDegree hformula hϖL hzero hres q,
    fieldNormQuotient_eq_one_of_residueDegree_eq_one
      K L vK vL residueDegree hformula hϖL hzero hres r]

/-- Quotient form of the residue-degree-one norm-surjectivity criterion. -/
theorem fieldNormQuotient_forall_eq_one_iff_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ localNormSubgroup K L) :
    (∀ q : Kˣ ⧸ localNormSubgroup K L, q = 1) ↔ residueDegree = 1 := by
  constructor
  · intro hq
    have hvalϖK : vK.val ϖK = 1 := hϖK
    have hclass :
        QuotientGroup.mk' (localNormSubgroup K L) ϖK = 1 :=
      hq (QuotientGroup.mk' (localNormSubgroup K L) ϖK)
    have hdiv : (residueDegree : ℤ) ∣ (1 : ℤ) := by
      simpa [hvalϖK] using
        (fieldNormQuotient_mk_eq_one_iff_residueDegree_dvd_val
          K L vK vL residueDegree hformula hϖL hzero ϖK).1 hclass
    have hInt : (residueDegree : ℤ) = 1 :=
      Int.eq_one_of_dvd_one (by exact_mod_cast Nat.zero_le residueDegree) hdiv
    exact_mod_cast hInt
  · intro hres q
    exact fieldNormQuotient_eq_one_of_residueDegree_eq_one
      K L vK vL residueDegree hformula hϖL hzero hres q

end DiscreteValuationField

end

end LocalFieldTheory
