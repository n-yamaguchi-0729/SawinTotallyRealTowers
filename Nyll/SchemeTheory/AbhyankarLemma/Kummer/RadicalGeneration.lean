/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Kummer.Definitions
import Nyll.ValuedFieldTheory.LocalField.Unramified.BasicInvariants

/-!
# Radical sources for tame extensions

For a finite tamely ramified extension, the radical-generation theorem describes the
extension over its maximal unramified subfield by finitely many radicals of
orders prime to the residue characteristic.  The definitions below state
that conclusion literally.  The first construction step is also proved:
the order of every actual value-group coset kills the value of a chosen
representative modulo the base value group, producing a base element whose
value is the value of the corresponding power.

This is source data from the actual quotient `w(Lˣ)/v(Kˣ)`, not a
certificate for the final generation statement.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

section ValueCosetAndPrincipalUnitRadicals

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-- The additive group structure is definitionally the quotient-group
structure.  Naming it here lets the order API unfold the transparent
abbreviation reliably. -/
@[reducible] local instance exponentialValueGroupQuotientAddCommGroup
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L) :
    AddCommGroup (ExponentialValueGroupQuotient v w) :=
  QuotientAddGroup.Quotient.addCommGroup _

/-- The literal radical-generation conclusion for a tame extension.

There is a concrete finite family of positive exponents, base elements and
chosen roots in `L`; every exponent is prime to `p`, every displayed root
satisfies its power equation, and those roots generate all of `L` over `T`.
-/
def GeneratedByRadicalsPrimeTo
    (T : IntermediateField K L) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (m : Fin r → ℕ) (a : Fin r → T) (α : Fin r → L),
    (∀ i, 0 < m i) ∧
      (∀ i, Nat.Coprime (m i) p) ∧
        (∀ i, α i ^ m i = algebraMap T L (a i)) ∧
          IntermediateField.adjoin T (Set.range α) = ⊤

/-- The precise radical predicate for tame generation, with `T`
the maximal unramified subextension and `p` the actual residue
characteristic. -/
def GeneratedOverMaximalUnramifiedByRadicals
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) : Prop :=
  GeneratedByRadicalsPrimeTo
    (maximalUnramifiedSubextension v w hExt)
    (residueCharacteristic v)

/-- In a finite valued extension, every element of the actual value-group
quotient has positive finite additive order. -/
theorem exponentialValueGroupQuotient_addOrderOf_pos
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (q : ExponentialValueGroupQuotient v w) :
    0 < addOrderOf q := by
  let : Finite (ExponentialValueGroupQuotient v w) :=
    exponentialValueGroupQuotient_finite_of_finiteDimensional v w hExt
  exact addOrderOf_pos q

/-- The order of an actual value-group coset divides the ramification index,
because the latter is the cardinality of that quotient. -/
theorem exponentialValueGroupQuotient_addOrderOf_dvd_ramificationIndex
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (q : ExponentialValueGroupQuotient v w) :
    addOrderOf q ∣ exponentialRamificationIndex v w := by
  let : Finite (ExponentialValueGroupQuotient v w) :=
    exponentialValueGroupQuotient_finite_of_finiteDimensional v w hExt
  let : Fintype (ExponentialValueGroupQuotient v w) := Fintype.ofFinite _
  change addOrderOf q ∣ Nat.card (ExponentialValueGroupQuotient v w)
  simpa only [Nat.card_eq_fintype_card] using
    (addOrderOf_dvd_card (x := q))

omit [Algebra K L] in
/-- Raising a nonzero element to the order of its value-group coset puts its
value in the base value subgroup.  This is the first concrete step in the
radical construction. -/
theorem exists_base_element_value_eq_pow_addOrderOf_valueCoset
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (x : L) (hx : x ≠ 0) :
    ∃ a : K, a ≠ 0 ∧
      v a = w (x ^ addOrderOf (exponentialValueCoset v w x hx)) := by
  let q := exponentialValueCoset v w x hx
  let n := addOrderOf q
  let Gamma := exponentialValueSubgroup w
  let H : AddSubgroup Gamma :=
    (exponentialValueSubgroup v).comap Gamma.subtype
  let : AddGroup (Gamma ⧸ H) :=
    (exponentialValueGroupQuotientAddCommGroup v w).toAddGroup
  let gamma : Gamma :=
    ⟨(w x).untop₀, ⟨x, hx,
      (WithTop.coe_untop₀_of_ne_top
        (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero w hx)).symm⟩⟩
  have hnsmul (r : ℕ) :
      (r • q : ExponentialValueGroupQuotient v w) =
        r • (QuotientAddGroup.mk gamma : Gamma ⧸ H) := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [succ_nsmul, succ_nsmul, ih]
        rfl
  have hq : n • q = 0 := addOrderOf_nsmul_eq_zero q
  have hq' : n • (QuotientAddGroup.mk gamma : Gamma ⧸ H) = 0 := by
    rw [← hnsmul]
    exact hq
  have hmem : n • gamma ∈ H := by
    apply (QuotientAddGroup.eq_zero_iff _).1
    change (QuotientAddGroup.mk' H) (n • gamma) = 0
    rw [map_nsmul]
    exact hq'
  change n • (w x).untop₀ ∈ exponentialValueSubgroup v at hmem
  rw [nsmul_eq_mul] at hmem
  rcases hmem with ⟨a, ha, hva⟩
  refine ⟨a, ha, ?_⟩
  have hxTop : w x ≠ ⊤ :=
    LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero w hx
  have hvaTop : v a ≠ ⊤ :=
    LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v ha
  change v a = w (x ^ n)
  have hpow : w (x ^ n) = n • w x := by
    induction n with
    | zero => simp [LubinTate.Valuations.exponentialValuation_one]
    | succ n ih =>
        rw [pow_succ, w.map_mul, ih, succ_nsmul]
  rw [hpow]
  rw [show v a = (((v a).untop₀ : ℝ) : WithTop ℝ) from
    (WithTop.coe_untop₀_of_ne_top hvaTop).symm]
  rw [show w x = (((w x).untop₀ : ℝ) : WithTop ℝ) from
    (WithTop.coe_untop₀_of_ne_top hxTop).symm]
  have hvaReal : (v a).untop₀ = (n : ℝ) * (w x).untop₀ := by
    simpa using congrArg WithTop.untop₀ hva
  apply WithTop.coe_eq_coe.mpr
  simpa [nsmul_eq_mul] using hvaReal

/-- The base element supplied by the coset order turns the corresponding
power into an actual value-zero unit after division. -/
theorem exists_base_element_and_value_zero_radical_correction
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (x : L) (hx : x ≠ 0) :
    ∃ a : K, a ≠ 0 ∧
      v a = w (x ^ addOrderOf (exponentialValueCoset v w x hx)) ∧
        w (x ^ addOrderOf (exponentialValueCoset v w x hx) /
          algebraMap K L a) = 0 := by
  obtain ⟨a, ha, hva⟩ :=
    exists_base_element_value_eq_pow_addOrderOf_valueCoset v w x hx
  refine ⟨a, ha, hva, ?_⟩
  let n := addOrderOf (exponentialValueCoset v w x hx)
  have hpow0 : x ^ n ≠ 0 := pow_ne_zero n hx
  have haMap0 : algebraMap K L a ≠ 0 :=
    (map_ne_zero (algebraMap K L)).2 ha
  obtain ⟨r, hr⟩ :=
    LubinTate.Valuations.exponentialValuation_exists_real_of_ne_zero w hpow0
  have hden : w (algebraMap K L a) = (r : WithTop ℝ) := by
    rw [hExt, hva]
    exact hr
  have hdenInv : w (algebraMap K L a)⁻¹ = ((-r : ℝ) : WithTop ℝ) :=
    LubinTate.Valuations.exponentialValuation_inv_value w haMap0 hden
  change w (x ^ n / algebraMap K L a) = 0
  rw [div_eq_mul_inv, w.map_mul, hr, hdenInv]
  simp

/-- Hensel's lemma supplies prime-to-residue-characteristic roots on the
principal-unit fibre: if a valuation-ring element reduces to `1`, then it is
an `m`-th power whenever `m` is prime to the positive residue
characteristic.

This is the root-producing step used in the forward tame-generation
implication.  The proof applies the separability criterion to the concrete
factorization
`X^m - 1 = (X - 1) * (1 + X + ... + X^(m-1))`; coprimality follows because
the second factor takes the nonzero value `m` at `1`. -/
theorem exists_pow_eq_of_residue_eq_one_of_coprime
    (v : LubinTate.Valuations.ExponentialValuation K)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (m : ℕ)
    (hcop : Nat.Coprime m (residueCharacteristic v))
    (u : LubinTate.Valuations.exponentialValuationSubring v)
    (hu : IsLocalRing.residue (LubinTate.Valuations.exponentialValuationSubring v) u = 1) :
    ∃ β : LubinTate.Valuations.exponentialValuationSubring v,
      β ^ m = u ∧
        IsLocalRing.residue (LubinTate.Valuations.exponentialValuationSubring v) β = 1 := by
  classical
  let O := LubinTate.Valuations.exponentialValuationSubring v
  let V := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let e : V ≃+* O :=
    { toFun := fun x => ⟨x.1, by
        change (0 : WithTop ℝ) ≤ v x.1
        exact
          (LubinTate.Valuations.mem_exponentialValuationSubringAsValuationSubring_iff
            v x.1).1 x.property⟩
      invFun := fun x => ⟨x.1, by
        change (0 : WithTop ℝ) ≤ v x.1
        exact
          (LubinTate.Valuations.mem_exponentialValuationSubring_iff
            v x.1).1 x.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        rfl
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl }
  let uV : V := e.symm u
  let k := IsLocalRing.ResidueField V
  let f : Polynomial V := Polynomial.X ^ m - Polynomial.C uV
  let gbar : Polynomial k := Polynomial.X - Polynomial.C 1
  let hbar : Polynomial k :=
    ∑ i ∈ Finset.range m, Polynomial.X ^ i
  have residue_eq_one_iff_not_isUnitO (z : O) :
      IsLocalRing.residue O z = 1 ↔ ¬ IsUnit (z - 1) := by
    rw [← map_one (IsLocalRing.residue O), ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
  have residue_eq_one_iff_not_isUnitV (z : V) :
      IsLocalRing.residue V z = 1 ↔ ¬ IsUnit (z - 1) := by
    rw [← map_one (IsLocalRing.residue V), ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
  have huNonunitO : ¬ IsUnit (u - 1) :=
    (residue_eq_one_iff_not_isUnitO u).1 hu
  have huNonunitV : ¬ IsUnit (uV - 1) := by
    intro hunit
    apply huNonunitO
    have hmapUnit := hunit.map e
    simpa [uV] using hmapUnit
  have huV : IsLocalRing.residue V uV = 1 :=
    (residue_eq_one_iff_not_isUnitV uV).2 huNonunitV
  have hm0 : m ≠ 0 := by
    intro hmzero
    subst m
    have hpone : residueCharacteristic v = 1 := by
      simpa using hcop
    exact (residueCharacteristic_prime v hp).ne_one hpone
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  have hf : f.Monic := by
    exact Polynomial.monic_X_pow_sub_C uV hm0
  have hgbar : gbar.Monic := Polynomial.monic_X_sub_C 1
  have hhbar : hbar.Monic := by
    have hmdecomp : m = (m - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.succ_le_iff.mpr hm)).symm
    dsimp [hbar]
    rw [hmdecomp, geom_sum_succ']
    apply Polynomial.monic_X_pow_add
    simpa only [← Fin.sum_univ_eq_sum_range, Polynomial.C_1, one_mul] using
      (Polynomial.degree_sum_fin_lt
        (fun _i : Fin (m - 1) ↦ (1 : k)))
  have hfactor :
      f.map (IsLocalRing.residue V) = gbar * hbar := by
    dsimp [f, gbar, hbar]
    rw [Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, huV, map_one,
      show (1 : Polynomial k) = Polynomial.C 1 by simp]
    simpa only [Polynomial.C_1, mul_comm] using
      (geom_sum_mul (Polynomial.X : Polynomial k) m).symm
  have hmCast : (m : k) ≠ 0 := by
    have hmCastO :
        (m : IsLocalRing.ResidueField
          (LubinTate.Valuations.exponentialValuationSubring v)) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff
        (IsLocalRing.ResidueField
          (LubinTate.Valuations.exponentialValuationSubring v))
        (residueCharacteristic v) m]
      exact (residueCharacteristic_prime v hp).coprime_iff_not_dvd.mp
        hcop.symm
    have hmUnitO : IsUnit (m : O) := by
      have hmUnit :
          IsUnit
            (m : LubinTate.Valuations.exponentialValuationSubring v) := by
        apply
          (IsLocalRing.residue_ne_zero_iff_isUnit
            (m : LubinTate.Valuations.exponentialValuationSubring v)).1
        simpa using hmCastO
      simpa only [O] using hmUnit
    have hmUnitV : IsUnit (m : V) := by
      have hmapUnit := hmUnitO.map e.symm
      simpa using hmapUnit
    simpa [k] using
      (IsLocalRing.residue_ne_zero_iff_isUnit (m : V)).2 hmUnitV
  have hhbarEval : hbar.eval (1 : k) = (m : k) := by
    simp [hbar]
  have hhbarUnit : IsUnit (hbar.eval (1 : k)) := by
    rw [hhbarEval]
    exact isUnit_iff_ne_zero.mpr hmCast
  have hcoprime : IsCoprime gbar hbar := by
    exact ValuationTheory.DiscreteValuationField.HenselianDVF.isCoprime_X_sub_C_of_isUnit_eval
      hbar 1 hhbarUnit
  have hfactorization : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty V := by
    change ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      V.valuation.valuationSubring at hhens
    rw [ValuationSubring.valuationSubring_valuation] at hhens
    exact hhens
  have hlift : DiscreteValuationField.MonicResidualCoprimeFactorLifting V :=
    DiscreteValuationField.monicResidualCoprimeFactorLifting_of_henselFactorization
      hfactorization
  change ∃ β : O, β ^ m = u ∧ IsLocalRing.residue O β = 1
  rcases hlift hf hgbar hhbar hfactor hcoprime with
    ⟨G, H, hGmonic, _hHmonic, hGH, hGmap, _hHmap⟩
  have hGdegree : G.natDegree = 1 := by
    calc
      G.natDegree = (G.map (IsLocalRing.residue V)).natDegree :=
        (hGmonic.natDegree_map (IsLocalRing.residue V)).symm
      _ = gbar.natDegree := congrArg Polynomial.natDegree hGmap
      _ = 1 := by
        simpa [gbar] using
          (Polynomial.natDegree_X_sub_C (1 : k))
  let βV : V := -G.coeff 0
  have hGform : G = Polynomial.X - Polynomial.C βV := by
    rw [hGmonic.eq_X_add_C hGdegree]
    simp [βV]
  have hβresV : IsLocalRing.residue V βV = 1 := by
    have hcoeffV : IsLocalRing.residue V (G.coeff 0) = -(1 : k) := by
      have hcoeff := congrArg (fun P : Polynomial k ↦ P.coeff 0) hGmap
      simpa [gbar, Polynomial.coeff_map] using hcoeff
    dsimp [βV]
    rw [map_neg, hcoeffV, neg_neg]
  have hroot : f.IsRoot βV := by
    apply Polynomial.dvd_iff_isRoot.mp
    refine ⟨H, ?_⟩
    simpa [hGform] using hGH
  rw [Polynomial.IsRoot.def] at hroot
  change (Polynomial.X ^ m - Polynomial.C uV).eval βV = 0 at hroot
  rw [Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C] at hroot
  have hpowV : βV ^ m = uV := sub_eq_zero.mp hroot
  let β : O := e βV
  have hpowO : β ^ m = u := by
    calc
      β ^ m = e (βV ^ m) := by simp [β]
      _ = e uV := congrArg (fun z : V ↦ e z) hpowV
      _ = u := e.apply_symm_apply u
  have hβNonunitV : ¬ IsUnit (βV - 1) :=
    (residue_eq_one_iff_not_isUnitV βV).1 hβresV
  have hβNonunitO : ¬ IsUnit (β - 1) := by
    intro hunit
    apply hβNonunitV
    have hmapUnit := hunit.map e.symm
    simpa [β] using hmapUnit
  have hβresO : IsLocalRing.residue O β = 1 :=
    (residue_eq_one_iff_not_isUnitO β).2 hβNonunitO
  exact ⟨β, hpowO, hβresO⟩

end ValueCosetAndPrincipalUnitRadicals

end Valuations
end AlgebraicNumberTheory

end
