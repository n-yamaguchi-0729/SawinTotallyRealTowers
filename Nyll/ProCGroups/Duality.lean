/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Pro C Groups / Duality

This module formalizes elementary duality constructions for profinite groups.
-/

open scoped Topology

namespace ProCGroups.Duality

universe u v

section Basic

variable (G : Type u) [CommGroup G] [TopologicalSpace G]

/-- A closed proper additive subgroup of an additive circle `AddCircle p` is finite. -/
theorem properClosedAddSubgroup_addCircle_finite
    {p : ℝ} [Fact (0 < p)] (B : AddSubgroup (AddCircle p))
    (hBclosed : IsClosed (B : Set (AddCircle p))) (hBproper : B ≠ ⊤) :
    Finite B := by
  classical
  have hBnotDense : ¬ Dense (B : Set (AddCircle p)) := by
    intro hDense
    apply hBproper
    rw [AddSubgroup.eq_top_iff']
    intro x
    change x ∈ (B : Set (AddCircle p))
    have hclosure : closure (B : Set (AddCircle p)) = Set.univ := hDense.closure_eq
    rw [← hBclosed.closure_eq]
    rw [hclosure]
    trivial
  have hnot_zmultiples :
      ¬ ∀ a : AddCircle p, addOrderOf a ≠ 0 → B ≠ AddSubgroup.zmultiples a := by
    simpa [AddCircle.dense_addSubgroup_iff_ne_zmultiples (p := p) (s := B)] using hBnotDense
  push Not at hnot_zmultiples
  rcases hnot_zmultiples with ⟨a, haorder, hBgen⟩
  have haFin : IsOfFinAddOrder a :=
    (addOrderOf_ne_zero_iff).mp haorder
  have hBfiniteSet : (B : Set (AddCircle p)).Finite := by
    rw [hBgen]
    exact Set.finite_coe_iff.mp haFin.finite_zmultiples
  exact hBfiniteSet.to_subtype

/-- Transport a multiplicative subgroup of `Circle` to the standard additive circle
`ℝ / (2π)ℤ`. This is convenient for applying `AddCircle` subgroup-classification lemmas. -/
def circleSubgroupToAddCircleSubgroup (A : Subgroup Circle) :
    AddSubgroup (AddCircle (2 * Real.pi)) := by
  refine
    { carrier := {θ | AddCircle.homeomorphCircle' θ ∈ A}
      zero_mem' := by
        change Real.Angle.toCircle 0 ∈ A
        rw [Real.Angle.toCircle_zero]
        exact A.one_mem
      add_mem' := ?_
      neg_mem' := ?_ }
  · intro a b ha hb
    change AddCircle.homeomorphCircle' (a + b) ∈ A
    rw [show AddCircle.homeomorphCircle' (a + b) =
      AddCircle.homeomorphCircle' a * AddCircle.homeomorphCircle' b by
      change Real.Angle.toCircle (a + b) = Real.Angle.toCircle a * Real.Angle.toCircle b
      exact Real.Angle.toCircle_add a b]
    exact A.mul_mem ha hb
  · intro a ha
    change AddCircle.homeomorphCircle' (-a) ∈ A
    rw [show AddCircle.homeomorphCircle' (-a) = (AddCircle.homeomorphCircle' a)⁻¹ by
      change Real.Angle.toCircle (-a) = (Real.Angle.toCircle a)⁻¹
      exact Real.Angle.toCircle_neg a]
    exact A.inv_mem ha

/-- Membership in the transported additive subgroup is detected by the circle
homeomorphism. -/
@[simp] theorem mem_circleSubgroupToAddCircleSubgroup_iff
    {A : Subgroup Circle} {θ : AddCircle (2 * Real.pi)} :
    θ ∈ circleSubgroupToAddCircleSubgroup A ↔ AddCircle.homeomorphCircle' θ ∈ A := by
  rfl

/-- Transporting a closed circle subgroup to the additive circle preserves closedness. -/
theorem isClosed_circleSubgroupToAddCircleSubgroup
    (A : Subgroup Circle) (hAclosed : IsClosed (A : Set Circle)) :
    IsClosed (circleSubgroupToAddCircleSubgroup A : Set (AddCircle (2 * Real.pi))) := by
  change IsClosed (AddCircle.homeomorphCircle' ⁻¹' (A : Set Circle))
  exact (AddCircle.homeomorphCircle'.isClosed_preimage).2 hAclosed

/-- Transporting a proper circle subgroup to the additive circle preserves properness. -/
theorem circleSubgroupToAddCircleSubgroup_ne_top
    (A : Subgroup Circle) (hAproper : A ≠ ⊤) :
    circleSubgroupToAddCircleSubgroup A ≠ ⊤ := by
  intro htop
  apply hAproper
  rw [Subgroup.eq_top_iff']
  intro z
  have hz : AddCircle.homeomorphCircle'.symm z ∈ circleSubgroupToAddCircleSubgroup A := by
    rw [htop]
    simp only [AddCircle.homeomorphCircle'_symm_apply, AddSubgroup.mem_top]
  have hz' : AddCircle.homeomorphCircle' (AddCircle.homeomorphCircle'.symm z) ∈ A :=
    mem_circleSubgroupToAddCircleSubgroup_iff.mp hz
  rw [AddCircle.homeomorphCircle'.apply_symm_apply] at hz'
  exact hz'

/-- Every proper closed subgroup of the circle is finite. -/
theorem properClosedSubgroup_circleTarget_finite
    (A : Subgroup Circle) (hAclosed : IsClosed (A : Set Circle))
    (hAproper : A ≠ ⊤) :
    Finite A := by
  let B := circleSubgroupToAddCircleSubgroup A
  have hBclosed : IsClosed (B : Set (AddCircle (2 * Real.pi))) :=
    isClosed_circleSubgroupToAddCircleSubgroup A hAclosed
  have hBproper : B ≠ ⊤ := circleSubgroupToAddCircleSubgroup_ne_top A hAproper
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hBfinite : Finite B := properClosedAddSubgroup_addCircle_finite B hBclosed hBproper
  let e : B ≃ A :=
    { toFun := fun θ => ⟨AddCircle.homeomorphCircle' θ, θ.2⟩
      invFun := fun z => ⟨AddCircle.homeomorphCircle'.symm z, by
        change AddCircle.homeomorphCircle' (AddCircle.homeomorphCircle'.symm z) ∈ A
        rw [AddCircle.homeomorphCircle'.apply_symm_apply]
        exact z.2⟩
      left_inv := by
        intro θ
        apply Subtype.ext
        exact AddCircle.homeomorphCircle'.symm_apply_apply θ.1
      right_inv := by
        intro z
        apply Subtype.ext
        exact AddCircle.homeomorphCircle'.apply_symm_apply z.1 }
  exact Finite.of_equiv B e

variable {G}

/-- The circle target contains two distinct points. -/
theorem circleTarget_one_ne_exp_pi :
    (1 : Circle) ≠ Circle.exp Real.pi := by
  simpa [eq_comm] using Circle.exp_pi_ne_one

/-- The circle target is not totally disconnected. -/
theorem not_totallyDisconnectedSpace_circleTarget :
    ¬ TotallyDisconnectedSpace Circle := by
  intro htd
  have hEq : (1 : Circle) = Circle.exp Real.pi :=
    TotallyDisconnectedSpace.eq_of_continuous
      (f := fun z : Circle => z) continuous_id 1 (Circle.exp Real.pi)
  exact circleTarget_one_ne_exp_pi hEq

/-- A compact subgroup of `T` contained in the open right half-plane is trivial. -/
theorem subgroup_eq_bot_of_isCompact_subset_rightHalfPlane
    (A : Subgroup Circle) (hAcompact : IsCompact (A : Set Circle))
    (hApos : ∀ z ∈ A, 0 < Complex.re (z : ℂ)) :
    A = ⊥ := by
  classical
  by_cases hAbot : A = ⊥
  · exact hAbot
  have hAproper : A ≠ ⊤ := by
    intro hAtop
    have hneg : Circle.exp Real.pi ∈ A := by
      simp only [hAtop, Subgroup.mem_top]
    have hneg' : ¬ 0 < Complex.re ((Circle.exp Real.pi : Circle) : ℂ) := by
      simp only [Circle.coe_exp, Complex.exp_pi_mul_I, Complex.neg_re, Complex.one_re,
          Left.neg_pos_iff, not_lt,
  zero_le_one]
    exact hneg' (hApos (Circle.exp Real.pi) hneg)
  have hAfinite : Finite A :=
    properClosedSubgroup_circleTarget_finite A hAcompact.isClosed hAproper
  let : Fintype A := Fintype.ofFinite A
  have hCircleToUnits_injective :
      Function.Injective (Circle.toUnits : Circle →* Units ℂ) := by
    intro x y hxy
    apply Circle.ext
    exact congrArg (fun z : Units ℂ => (z : ℂ)) hxy
  let B : Subgroup (Units ℂ) := A.map Circle.toUnits
  let e : A ≃* B := A.equivMapOfInjective Circle.toUnits hCircleToUnits_injective
  have hBfinite : Finite B := Finite.of_equiv A e
  let : Fintype B := Fintype.ofFinite B
  have hBnebot : B ≠ ⊥ := by
    intro hBbot
    apply hAbot
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := A) (f := Circle.toUnits) hCircleToUnits_injective).mp (by simpa [B] using hBbot)
  have hsumB : ∑ x : B, ((x : Units ℂ) : ℂ) = 0 :=
    FiniteField.sum_subgroup_units_eq_zero hBnebot
  have hsumA : ∑ x : A, (x : ℂ) = 0 := by
    calc
      ∑ x : A, (x : ℂ) = ∑ x : A, (((e x : B) : Units ℂ) : ℂ) := by
        exact Fintype.sum_congr _ _ fun x => by
          simp only [Subgroup.coe_equivMapOfInjective_apply, Circle.toUnits_apply,
              Units.val_mk0, B, e]
      _ = ∑ y : B, ((y : Units ℂ) : ℂ) := by
        simpa using (e.toEquiv.sum_comp fun y : B => ((y : Units ℂ) : ℂ))
      _ = 0 := hsumB
  have hsumRePos : 0 < Complex.re (∑ x : A, (x : ℂ)) := by
    rw [Complex.re_sum]
    simpa using
      (Finset.sum_pos' (s := (Finset.univ : Finset A))
        (f := fun x : A => Complex.re (x : ℂ))
        (fun x hx => le_of_lt (hApos x x.2))
        ⟨1, by simp only [Finset.mem_univ], hApos (1 : Circle) A.one_mem⟩)
  exfalso
  rw [hsumA] at hsumRePos
  simp only [Complex.zero_re, lt_self_iff_false] at hsumRePos

/-- The Pontryagin dual of a compact abelian group is discrete. -/
theorem dualGroup_discrete_of_compact [CompactSpace G] :
    DiscreteTopology (PontryaginDual G) := by
  let U : Set Circle := {z | 0 < Complex.re (z : ℂ)}
  let V : Set (PontryaginDual G) := {χ | Set.MapsTo χ Set.univ U}
  have hUopen : IsOpen U := by
    change IsOpen {z : Circle | 0 < Complex.re (z : ℂ)}
    exact isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
  have hVopen : IsOpen V := by
    let W : Set C(G, Circle) := {f | Set.MapsTo f Set.univ U}
    have hWopen : IsOpen W := by
      simpa [W] using
        (ContinuousMap.isOpen_setOfPred_mapsTo
          (X := G) (Y := Circle) (K := Set.univ) (U := U) isCompact_univ hUopen)
    exact (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).isOpen_iff.mpr
      ⟨W, hWopen, by ext χ; rfl⟩
  have hVeq : V = ({1} : Set (PontryaginDual G)) := by
    ext χ
    constructor
    · intro hχ
      rw [Set.mem_singleton_iff]
      let A : Subgroup Circle := χ.toMonoidHom.range
      have hAcompact : IsCompact (A : Set Circle) := by
        simpa [A] using isCompact_range χ.continuous_toFun
      have hApos : ∀ z ∈ A, 0 < Complex.re (z : ℂ) := by
        intro z hz
        rcases hz with ⟨g, rfl⟩
        exact hχ (by simp only [Set.mem_univ])
      have hAbot : A = ⊥ :=
        subgroup_eq_bot_of_isCompact_subset_rightHalfPlane A hAcompact hApos
      apply ContinuousMonoidHom.ext
      intro g
      have hg : χ g ∈ A := ⟨g, rfl⟩
      have hg' : χ g ∈ (⊥ : Subgroup Circle) := by
        simpa [hAbot] using hg
      change χ g = (1 : Circle)
      exact Subgroup.mem_bot.mp hg'
    · intro hχ
      rw [Set.mem_singleton_iff] at hχ
      subst hχ
      intro _g _hg
      change 0 < Complex.re ((1 : Circle) : ℂ)
      norm_num
  have hOneOpen : IsOpen ({1} : Set (PontryaginDual G)) := by
    rw [hVeq] at hVopen
    exact hVopen
  exact discreteTopology_of_isOpen_singleton_one hOneOpen

/-- A discrete abelian group has compact Pontryagin dual. -/
instance dualCompactSpaceOfDiscreteTopology [DiscreteTopology G] :
    CompactSpace (PontryaginDual G) := by
  infer_instance

/-- The Pontryagin dual of a discrete abelian group is compact. -/
theorem dualGroup_compact_of_discrete [DiscreteTopology G] :
    CompactSpace (PontryaginDual G) := by
  infer_instance

private noncomputable def torsionPowerWitnessOfElement
    {G : Type u} [CommGroup G] (htors : IsMulTorsion G) (g : G) :
    {n : ℕ // 0 < n ∧ g ^ n = 1} := by
  let h := (isOfFinOrder_iff_pow_eq_one).mp (htors g)
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- The Pontryagin dual of a discrete torsion abelian group is totally disconnected. -/
theorem dualGroup_totallyDisconnected_of_discrete_torsion
    (G : Type u) [CommGroup G] [TopologicalSpace G]
    [DiscreteTopology G] (htors : IsMulTorsion G) :
    TotallyDisconnectedSpace (PontryaginDual G) := by
  let n : G → ℕ := fun g => (torsionPowerWitnessOfElement htors g).1
  let Ω : G → Type := fun g => { z : Circle // (z : ℂ) ^ n g = 1 }
  have hΩfinite : ∀ g : G, Finite (Ω g) := by
    intro g
    classical
    have hcomplexFinite :
        Finite {z : ℂ // z ∈ Polynomial.nthRoots (n g) (1 : ℂ)} := by
      simpa using
        (((Polynomial.nthRoots (n g) (1 : ℂ)).toFinset.finite_toSet).to_subtype)
    refine Finite.of_injective
      (f := fun z : Ω g =>
        (⟨(z : ℂ),
          (Polynomial.mem_nthRoots (torsionPowerWitnessOfElement htors g).2.1).2 z.2⟩ :
          {z : ℂ // z ∈ Polynomial.nthRoots (n g) (1 : ℂ)})) ?_
    intro x y hxy
    have hxyComplex : ((x : Ω g) : ℂ) = ((y : Ω g) : ℂ) := by
      exact congrArg
        (fun w : {z : ℂ // z ∈ Polynomial.nthRoots (n g) (1 : ℂ)} => (w : ℂ)) hxy
    have hxyCircle : ((x : Ω g) : Circle) = ((y : Ω g) : Circle) := by
      apply Subtype.ext
      exact hxyComplex
    exact Subtype.ext hxyCircle
  let F : PontryaginDual G → ∀ g : G, Ω g := fun χ g =>
    ⟨χ g, by
      have hgpow : g ^ n g = 1 := (torsionPowerWitnessOfElement htors g).2.2
      have hpow : χ g ^ n g = 1 := by
        calc
          χ g ^ n g = χ (g ^ n g) := by simp only [map_pow]
          _ = 1 := by rw [hgpow, map_one]
      exact congrArg (fun z : Circle => (z : ℂ)) hpow⟩
  have hFcont : Continuous F := by
    refine continuous_pi ?_
    intro g
    exact
      ((continuous_eval_const (F := C(G, Circle)) g).comp
        (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous).subtype_mk
        fun χ => (F χ g).2
  have hFinj : Function.Injective F := by
    intro χ ψ hχψ
    apply ContinuousMonoidHom.ext
    intro g
    exact congrArg (fun z : Ω g => (z : Circle)) (congrFun hχψ g)
  let FRange : PontryaginDual G → Set.range F := fun χ => ⟨F χ, ⟨χ, rfl⟩⟩
  have hFRange_continuous : Continuous FRange := hFcont.subtype_mk fun _ => ⟨_, rfl⟩
  have hFRange_bij : Function.Bijective FRange := by
    refine ⟨?_, ?_⟩
    · intro χ ψ hχψ
      exact hFinj <| congrArg Subtype.val hχψ
    · rintro ⟨y, χ, rfl⟩
      exact ⟨χ, rfl⟩
  let eTop : PontryaginDual G ≃ₜ Set.range F :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective FRange hFRange_bij) hFRange_continuous
  exact Homeomorph.totallyDisconnectedSpace eTop.symm

/-- For a discrete abelian group, multiplicative characters to the circle are the same as
additive characters on the additive type synonym. -/
noncomputable def dualGroupEquivAddCharCircle
    (A : Type u) [CommGroup A] [TopologicalSpace A] [DiscreteTopology A] :
    PontryaginDual A ≃ AddChar (Additive A) Circle where
  toFun := fun χ =>
    { toFun := fun a => χ a.toMul
      map_zero_eq_one' := by simp only [toMul_zero, map_one]
      map_add_eq_mul' := by
        intro a b
        exact map_mul χ a.toMul b.toMul }
  invFun := fun χ =>
    { toFun := fun a => χ (Additive.ofMul a)
      map_one' := by simp only [ofMul_one, AddChar.map_zero_eq_one]
      map_mul' := by
        intro a b
        exact χ.map_add_eq_mul (Additive.ofMul a) (Additive.ofMul b)
      continuous_toFun := continuous_of_discreteTopology }
  left_inv := by
    intro χ
    apply ContinuousMonoidHom.ext
    intro a
    rfl
  right_inv := by
    intro χ
    ext a
    rfl

/-- The Pontryagin dual of a finite discrete abelian group is finite. -/
theorem dualGroup_finite_of_finite_discrete
    (A : Type u) [CommGroup A] [TopologicalSpace A] [Finite A] [DiscreteTopology A] :
    Finite (PontryaginDual A) := by
  exact Finite.of_equiv (AddChar (Additive A) ℂ)
    ((AddChar.circleEquivComplex (α := Additive A)).toEquiv.symm.trans
      (dualGroupEquivAddCharCircle A).symm)

/-- A finite discrete abelian group and its Pontryagin dual have the same cardinality. -/
theorem card_dualGroup_eq_card_of_finite_discrete
    (A : Type u) [CommGroup A] [TopologicalSpace A] [Finite A] [DiscreteTopology A] :
    Nat.card (PontryaginDual A) = Nat.card A := by
  classical
  let : Fintype A := Fintype.ofFinite A
  calc
    Nat.card (PontryaginDual A) = Nat.card (AddChar (Additive A) Circle) :=
      Nat.card_congr (dualGroupEquivAddCharCircle A)
    _ = Nat.card (AddChar (Additive A) ℂ) :=
      Nat.card_congr (AddChar.circleEquivComplex (α := Additive A)).toEquiv
    _ = Fintype.card (AddChar (Additive A) ℂ) :=
      Nat.card_eq_fintype_card (α := AddChar (Additive A) ℂ)
    _ = Fintype.card (Additive A) := AddChar.card_eq (α := Additive A)
    _ = Fintype.card A := Fintype.card_additive A
    _ = Nat.card A := (Nat.card_eq_fintype_card (α := A)).symm

/-- A topological group equivalence induces an equivalence on Pontryagin duals. -/
noncomputable def dualGroupEquiv
    {H : Type v} [CommGroup H] [TopologicalSpace H]
    (e : G ≃ₜ* H) :
    PontryaginDual H ≃* PontryaginDual G :=
{ toFun := PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e)
  invFun := PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
  left_inv := by
    intro χ
    apply ContinuousMonoidHom.ext
    intro g
    change χ (e (e.symm g)) = χ g
    rw [e.apply_symm_apply]
  right_inv := by
    intro χ
    apply ContinuousMonoidHom.ext
    intro g
    change χ (e.symm (e g)) = χ g
    rw [e.symm_apply_apply]
  map_mul' := by
    intro χ ψ
    exact (PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e)).map_mul χ ψ }

/-- A topological group equivalence induces a continuous equivalence on Pontryagin duals. -/
noncomputable def dualGroupContinuousMulEquiv
    {H : Type v} [CommGroup H] [TopologicalSpace H]
    (e : G ≃ₜ* H) :
    PontryaginDual H ≃ₜ* PontryaginDual G :=
  ContinuousMulEquiv.ofHomInv
    (PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e))
    (PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e.symm))
    (by
      intro χ
      apply ContinuousMonoidHom.ext
      intro h
      change χ (e (e.symm h)) = χ h
      rw [e.apply_symm_apply])
    (by
      intro χ
      apply ContinuousMonoidHom.ext
      intro g
      change χ (e.symm (e g)) = χ g
      rw [e.symm_apply_apply])

/-- Forgetting topology from the dual homeomorphism gives the algebraic dual-group
equivalence. -/
@[simp] theorem dualGroupContinuousMulEquiv_toMulEquiv
    {H : Type v} [CommGroup H] [TopologicalSpace H]
    (e : G ≃ₜ* H) :
    (dualGroupContinuousMulEquiv (G := G) e).toMulEquiv = dualGroupEquiv (G := G) e :=
  rfl

end Basic

end ProCGroups.Duality
