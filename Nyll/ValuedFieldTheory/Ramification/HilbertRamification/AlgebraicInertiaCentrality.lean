/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaRestriction
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaCentrality
import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionHenselian
import Nyll.ValuedFieldTheory.Valuation.ComapResidueCharacteristic
import Nyll.ProCGroups.GroupTheory.FinitePGroupLifts
import Nyll.ProCGroups.Profinite.CentralLifts

/-!
# Central Galois elements from finite inertia

Over a Henselian base of residue characteristic zero containing all p-power
roots, finite p-group inertia yields central restrictions at larger finite
layers and a nonidentity central element of the absolute Galois group.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- A p-power-order finite inertia lift gives a central Galois automorphism at
any larger finite layer, with the prescribed restriction downstairs. -/
theorem exists_inertia_with_finite_central_restriction
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation]
    [CharZero (IsLocalRing.ResidueField A)]
    (p : ℕ) [Fact p.Prime]
    (hroots : ∀ n : ℕ, ∃ ζ : K, IsPrimitiveRoot ζ (p ^ n))
    (E F : FiniteGaloisIntermediateField K L) (hEF : E ≤ F)
    (hE : IsPGroup p (inertiaGroup K (A.comap E.toIntermediateField.val.toRingHom)))
    (τ : inertiaGroup K (A.comap E.toIntermediateField.val.toRingHom)) :
    ∃ σ : inertiaGroup K A, finiteInertiaRestriction A E σ = τ ∧
      ∀ g : Gal(F/K), Commute g
        ((inertiaGroupToAut (K := K) A σ).restrictNormal F) := by
  let B := A.comap F.toIntermediateField.val.toRingHom
  have : V.valuation.HasExtension B.valuation := by
    apply _root_.Valuation.HasExtension.ofComapInteger
    ext a
    change B.valuation (algebraMap K F a) ≤ 1 ↔ V.valuation a ≤ 1
    rw [_root_.ValuationSubring.valuation_le_one_iff,
      _root_.ValuationSubring.valuation_le_one_iff]
    change (algebraMap K L a) ∈ A ↔ a ∈ V
    simpa only [_root_.ValuationSubring.valuation_le_one_iff] using
      _root_.Valuation.HasExtension.val_map_le_one_iff V.valuation A.valuation a
  have : HenselianRing B (IsLocalRing.maximalIdeal B) :=
    ValuationTheory.Henselian.henselianRing_of_algebraic_extension V B
  have : CharZero (IsLocalRing.ResidueField B) :=
    _root_.ValuationSubring.charZero_residueField_comap A F.toIntermediateField.val.toRingHom
  let f := finiteInertiaTransition A E F hEF
  have hf : Function.Surjective f :=
    finiteInertiaTransition_surjective_of_henselianRing V A E F hEF
  obtain ⟨t, ht, n, htn⟩ :=
    ProCGroups.exists_prime_power_order_lift_of_surjective p f hf hE τ
  obtain ⟨ζ, hζ⟩ := hroots n
  obtain ⟨σ, hσ⟩ :=
    galoisPullback_inertiaGroupMap_surjective_of_henselianRing V A F.toIntermediateField t
  refine ⟨σ, ?_, ?_⟩
  · rw [← finiteInertiaTransition_comp A E F hEF σ, show finiteInertiaRestriction A F σ = t from hσ]
    exact ht
  · intro g
    let gD : decompositionGroup K B := ⟨g, by
      rw [decompositionGroup_eq_top_of_henselianRing V B]
      exact Subgroup.mem_top g⟩
    have hc := inertia_commutes_of_primitiveRoot_of_henselianRing
      B (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) ζ hζ t htn gD
    have hc' : Commute g (inertiaGroupToAut (K := K) B t) :=
      congrArg (fun z : decompositionGroup K B => (z : Gal(F/K))) hc
    change Commute g (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F
      (inertiaGroupToAut (K := K) A σ))
    rw [← finiteInertiaRestriction_coe A F σ, show finiteInertiaRestriction A F σ = t from hσ]
    exact hc'


/-- If a finite inertia quotient is a nontrivial p-group and all p-power roots
belong to the base, the absolute Galois group has a nonidentity central element. -/
theorem exists_ne_one_mem_center_of_finite_inertia_pGroup
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation]
    [CharZero (IsLocalRing.ResidueField A)]
    (p : ℕ) [Fact p.Prime]
    (hroots : ∀ n : ℕ, ∃ ζ : K, IsPrimitiveRoot ζ (p ^ n))
    (E : FiniteGaloisIntermediateField K L)
    (hE : IsPGroup p (inertiaGroup K (A.comap E.toIntermediateField.val.toRingHom)))
    (τ : inertiaGroup K (A.comap E.toIntermediateField.val.toRingHom)) (hτ : τ ≠ 1) :
    ∃ σ : Gal(L/K), σ ∈ Subgroup.center Gal(L/K) ∧ σ ≠ 1 := by
  let M : OpenNormalSubgroup Gal(L/K) :=
    { toSubgroup := E.toIntermediateField.fixingSubgroup
      isOpen' := IntermediateField.fixingSubgroup_isOpen E.toIntermediateField }
  apply ProCGroups.ProfiniteGrp.exists_ne_one_mem_center_of_quotient_central_lifts M
  intro N
  let NF : IntermediateField K L :=
    IntermediateField.fixedField (N : Subgroup Gal(L/K))
  have hfix : NF.fixingSubgroup = (N : Subgroup Gal(L/K)) :=
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨N.toSubgroup, N.isClosed⟩ : ClosedSubgroup Gal(L/K))
  have : FiniteDimensional K NF := (InfiniteGalois.isOpen_iff_finite NF).mp
    (by rw [hfix]; exact N.isOpen)
  let NFg : FiniteGaloisIntermediateField K L := ⟨NF⟩
  let F := NFg ⊔ E
  obtain ⟨σ, hσE, hσF⟩ :=
    exists_inertia_with_finite_central_restriction V A p hroots E F le_sup_right hE τ
  let s : Gal(L/K) := inertiaGroupToAut (K := K) A σ
  refine ⟨s, ?_, ?_⟩
  · intro hs
    have hsE : AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E s = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [E.toIntermediateField.restrictNormalHom_ker]
      exact hs
    apply hτ
    apply Subtype.ext
    apply Subtype.ext
    change inertiaGroupToAut (K := K) (A.comap E.toIntermediateField.val.toRingHom) τ = 1
    rw [← hσE, finiteInertiaRestriction_coe A E σ]
    exact hsE
  · intro g
    let c : Gal(L/K) := (g * s) * (s * g)⁻¹
    have hc : c.restrictNormal F = 1 := by
      change AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F ((g * s) * (s * g)⁻¹) = 1
      rw [map_mul, map_inv, map_mul, map_mul]
      exact mul_inv_eq_one.mpr (hσF (g.restrictNormal F)).eq
    rw [← hfix]
    apply (IntermediateField.mem_fixingSubgroup_iff NF c).mpr
    intro x hx
    let xF : F := ⟨x, (show NFg ≤ F from le_sup_left) hx⟩
    calc
      c x = F.toIntermediateField.val ((c.restrictNormal F) xF) :=
        (AlgEquiv.restrictNormal_commutes c F xF).symm
      _ = x := by rw [hc]; rfl

end RamificationTheory.HilbertRamification.ValuationSubring
