/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.SepClosedResidueInertia
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Henselian
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Commutators.Basic
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Closed derived terms over a separably closed residue field

Finite Galois restrictions of each positive closed derived term land in
finite p-group commutators. The Krull neighborhood basis therefore supplies
an open-normal p-group basis on the derived term itself.
-/

open scoped Topology
namespace ValuationTheory.DiscreteValuationField
open ProCGroups.ProC ProCGroups.FiniteStepSolvableQuotients
open RamificationTheory.HilbertRamification.ValuationSubring
noncomputable section
universe u v

/-- Every closed derived term after the first is pro-p over separably closed residue. -/
theorem HenselianDVF.topDerived_hasOpenNormalBasisInClass_of_separablyClosedResidue
    {K : Type u} [Field K] [CharZero K]
    (base : HenselianDVF.{u, v} K) (p : ℕ) [Fact p.Prime]
    [CharP base.residueField p] [IsSepClosed base.residueField]
    (m : ℕ) (hm : 1 ≤ m) :
    HasOpenNormalBasisInClass (ProCGroups.FiniteGroupClass.pGroup p)
      (topDerivedTop Gal(AlgebraicClosure K/K) m) := by
  let Ω := AlgebraicClosure K
  let D := topDerivedTop Gal(Ω/K) m
  intro W hW h1W
  obtain ⟨W₀, hW₀, hW₀W⟩ :=
    (mem_nhds_subtype (D : Set Gal(Ω/K)) (1 : D) W).mp (hW.mem_nhds h1W)
  obtain ⟨E, hE⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
      (k := K) (K := Ω) W₀).mp hW₀
  let res : Gal(Ω/K) →ₜ* Gal(E/K) :=
    { toMonoidHom := AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) E
      continuous_toFun := InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField }
  let f : D →ₜ* Gal(E/K) :=
    { toMonoidHom := res.toMonoidHom.comp D.subtype
      continuous_toFun := res.continuous_toFun.comp continuous_subtype_val }
  let U : OpenNormalSubgroup D := ProCGroups.ProC.OpenNormalSubgroup.ker f
  refine ⟨U, ?_, ?_⟩
  · intro σ hσ
    have hfix : (σ : Gal(Ω/K)) ∈ E.fixingSubgroup :=
      (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff (σ : Gal(Ω/K)) E).mpr hσ
    exact hW₀W (hE hfix)
  · let target := FiniteExtensionLocalization.henselianDVF (L := E) base
    have : base.toDVF.valuation.HasExtension target.toDVF.valuation :=
      FiniteExtensionLocalization.henselianDVF_hasExtension base
    have : CharP target.residueField p :=
      (Algebra.charP_iff base.residueField target.residueField p).mp inferInstance
    have hP : IsPGroup p (commutator Gal(E/K)) :=
      commutator_isPGroup_of_henselian_separablyClosedResidue
        base.toDVF.valuation target.toDVF.valuation p
    have hle : f.toMonoidHom.range ≤ commutator Gal(E/K) := by
      rintro σ ⟨τ, rfl⟩
      have hτ := (topDerivedTop_le_comap (f := res) 1)
        (topDerivedTop_antitone hm τ.property)
      change res (τ : Gal(Ω/K)) ∈ topDerivedTop Gal(E/K) 1 at hτ
      rw [topDerivedTop_one_eq_topologicalCommutator,
        topologicalCommutator_eq_commutator_of_isClosed _ (isClosed_discrete _)] at hτ
      exact hτ
    change ProCGroups.FiniteGroupClass.pGroup p (D ⧸ f.toMonoidHom.ker)
    exact (ProCGroups.FiniteGroupClass.pGroup p).mem_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange f.toMonoidHom).symm
      ⟨inferInstance, hP.to_le hle⟩

end
end ValuationTheory.DiscreteValuationField
