/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.HilbertElementaryLayerInMaximal
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.MaximalEverywhereUnramifiedProPGroup
import ProCGroups.ProP.GeneratorRank
import ProCGroups.ProP.PowerCommutatorUniversal

set_option autoImplicit false
/-!
# The Frattini quotient and the elementary Hilbert class field

This file identifies the power--commutator quotient of the maximal everywhere-
unramified pro-`p` Galois group with the elementary Hilbert class-field layer.
For odd `p`, it then identifies the topological generator rank with the
`p`-class rank.
-/

open scoped NumberField IsMulCommutative

noncomputable section

open Set
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields

namespace ClassFieldTower.Martinet

open ClassFieldTower.ProP
open ProCGroups.Generation
open ProCGroups.FiniteGeneration

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

private abbrev M := maximalEverywhereUnramifiedProP F p

private abbrev H := hilbertElementaryLayerInMaximal F p

local instance :
    (closedPowerCommutator p
      (MaxEverywhereUnramifiedProPGaloisGroup F p)).Normal :=
  closedPowerCommutator_normal p
    (MaxEverywhereUnramifiedProPGaloisGroup F p)

/-- Restriction to the elementary Hilbert layer, factored through the
power--commutator quotient. -/
noncomputable def maxPowerCommutatorToHilbert :
    powerCommutatorQuotient p
        (MaxEverywhereUnramifiedProPGaloisGroup F p) →ₜ*
      Gal((H F p) / F) :=
  powerCommutatorQuotientLift
    { toMonoidHom := AlgEquiv.restrictNormalHom (H F p)
      continuous_toFun :=
        InfiniteGalois.restrictNormalHom_continuous (H F p) }
    (hilbertElementaryLayerInMaximal_galois_pow_eq_one F p)

/-- Every automorphism of the elementary Hilbert layer extends to the maximal
everywhere-unramified pro-`p` extension. -/
theorem maxPowerCommutatorToHilbert_surjective :
    Function.Surjective (maxPowerCommutatorToHilbert F p) := by
  intro τ
  obtain ⟨σ, hσ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (M F p) τ
  refine ⟨powerCommutatorQuotientMk p
    (MaxEverywhereUnramifiedProPGaloisGroup F p) σ, ?_⟩
  change (AlgEquiv.restrictNormalHom (H F p)) σ = τ
  exact hσ

private abbrev powerCommutatorClosed : ClosedSubgroup
    Gal((M F p) / F) where
  toSubgroup := closedPowerCommutator p Gal((M F p) / F)
  isClosed' := isClosed_closedPowerCommutator p Gal((M F p) / F)

local instance : (powerCommutatorClosed F p :
    Subgroup Gal((M F p) / F)).Normal := by
  change (closedPowerCommutator p Gal((M F p) / F)).Normal
  exact closedPowerCommutator_normal p Gal((M F p) / F)

private abbrev powerCommutatorFixedField : IntermediateField F (M F p) :=
  IntermediateField.fixedField (powerCommutatorClosed F p).toSubgroup

local instance : IsGalois F (powerCommutatorFixedField F p) :=
  IsGalois.of_fixedField_normal_subgroup
    (powerCommutatorClosed F p).toSubgroup

local instance : IsAbelianGalois F (powerCommutatorFixedField F p) where
  is_comm.comm σ τ := by
    let e := InfiniteGalois.normalAutEquivQuotient
      (powerCommutatorClosed F p)
    calc
      σ * τ = e (e.symm σ * e.symm τ) := by simp
      _ = e (e.symm τ * e.symm σ) := by
        congr 1
        exact powerCommutatorQuotient_mul_comm p
          Gal((M F p) / F) _ _
      _ = τ * σ := by simp

-- The local group instance must be reducible so that quotient operations agree
-- definitionally with those used by `normalAutEquivQuotient`.
set_option linter.style.haveILetI false in
private theorem powerCommutatorFixedField_galois_pow_eq_one
    (σ : Gal((powerCommutatorFixedField F p) / F)) : σ ^ p = 1 := by
  let e := InfiniteGalois.normalAutEquivQuotient
    (powerCommutatorClosed F p)
  letI : CommGroup (powerCommutatorQuotient p Gal((M F p) / F)) :=
    { (inferInstance : Group (powerCommutatorQuotient p Gal((M F p) / F))) with
      mul_comm := powerCommutatorQuotient_mul_comm p Gal((M F p) / F) }
  apply e.symm.injective
  calc
    e.symm (σ ^ p) = (e.symm σ) ^ p := map_pow e.symm σ p
    _ = 1 := powerCommutatorQuotient_pow_eq_one p
      Gal((M F p) / F) (e.symm σ)
    _ = e.symm 1 := (map_one e.symm).symm

private abbrev liftedPowerCommutatorFixedField :
    IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.lift (powerCommutatorFixedField F p)

local instance : IsAbelianGalois F (liftedPowerCommutatorFixedField F p) :=
  IsAbelianGalois.of_algHom
    (IntermediateField.liftAlgEquiv
      (powerCommutatorFixedField F p)).symm.toAlgHom

private theorem liftedPowerCommutatorFixedField_galois_pow_eq_one
    (σ : Gal((liftedPowerCommutatorFixedField F p) / F)) : σ ^ p = 1 := by
  let e : Gal((powerCommutatorFixedField F p) / F) ≃*
      Gal((liftedPowerCommutatorFixedField F p) / F) :=
    AlgEquiv.autCongr
      (IntermediateField.liftAlgEquiv (powerCommutatorFixedField F p))
  let τ := e.symm σ
  calc
    σ ^ p = (e τ) ^ p := congrArg
      (fun z : Gal((liftedPowerCommutatorFixedField F p) / F) ↦ z ^ p)
      (e.apply_symm_apply σ).symm
    _ = e (τ ^ p) := (map_pow e τ p).symm
    _ = e 1 := congrArg e
      (powerCommutatorFixedField_galois_pow_eq_one F p τ)
    _ = 1 := map_one e

private theorem liftedPowerCommutatorFixedField_le_hilbert
    (hpOdd : Odd p) :
    liftedPowerCommutatorFixedField F p ≤
      hilbertElementaryLayerInAlgebraicClosure F p := by
  intro x hxD
  have hxM : x ∈ M F p :=
    IntermediateField.lift_le (powerCommutatorFixedField F p) hxD
  obtain ⟨C, hxC⟩ :=
    mem_maximalEverywhereUnramifiedProP_exists_extension F p hpOdd hxM
  let L : IntermediateField F (AlgebraicClosure F) :=
    C.field ⊓ liftedPowerCommutatorFixedField F p
  let : Algebra L C.field :=
    (IntermediateField.inclusion inf_le_left).toRingHom.toAlgebra
  let : IsScalarTower F L C.field := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional F L :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion
        (show L ≤ C.field from inf_le_left)).toLinearMap
      (IntermediateField.inclusion
        (show L ≤ C.field from inf_le_left)).injective
  let : NumberField L := NumberField.of_module_finite F L
  let : Algebra L (liftedPowerCommutatorFixedField F p) :=
    (IntermediateField.inclusion inf_le_right).toRingHom.toAlgebra
  let : IsScalarTower F L (liftedPowerCommutatorFixedField F p) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsAbelianGalois F L :=
    IsAbelianGalois.tower_bot F L
      (liftedPowerCommutatorFixedField F p)
  have hLunramified : IsEverywhereUnramified F L :=
    IsEverywhereUnramified.bot C.everywhereUnramified
  have hLexp : ∀ σ : Gal(L / F), σ ^ p = 1 := by
    intro σ
    obtain ⟨τ, rfl⟩ :=
      AlgEquiv.restrictNormalHom_surjective
        (liftedPowerCommutatorFixedField F p) σ
    calc
      (AlgEquiv.restrictNormalHom L τ) ^ p =
          AlgEquiv.restrictNormalHom L (τ ^ p) :=
        (map_pow (AlgEquiv.restrictNormalHom L) τ p).symm
      _ = AlgEquiv.restrictNormalHom L 1 := congrArg
        (AlgEquiv.restrictNormalHom L)
        (liftedPowerCommutatorFixedField_galois_pow_eq_one F p τ)
      _ = 1 := map_one (AlgEquiv.restrictNormalHom L)
  have hLH : L ≤ hilbertElementaryLayerInAlgebraicClosure F p :=
    finiteElementaryUnramified_le_hilbertElementaryLayer F p L
      hLunramified hLexp
  exact hLH ⟨hxC, hxD⟩

private theorem powerCommutatorFixedField_le_hilbertInMaximal
    (hpOdd : Odd p) :
    powerCommutatorFixedField F p ≤ H F p := by
  intro x hx
  change x.1 ∈ hilbertElementaryLayerInAlgebraicClosure F p
  exact liftedPowerCommutatorFixedField_le_hilbert F p hpOdd
    ((IntermediateField.mem_lift x).2 hx)

/-- For odd `p`, restriction to the elementary Hilbert layer is injective on
the power--commutator quotient. -/
theorem maxPowerCommutatorToHilbert_injective (hpOdd : Odd p) :
    Function.Injective (maxPowerCommutatorToHilbert F p) := by
  apply (MonoidHom.ker_eq_bot_iff
    (maxPowerCommutatorToHilbert F p).toMonoidHom).mp
  apply le_antisymm
  · intro q hq
    obtain ⟨σ, rfl⟩ := powerCommutatorQuotientMk_surjective p
      (MaxEverywhereUnramifiedProPGaloisGroup F p) q
    change maxPowerCommutatorToHilbert F p
      (powerCommutatorQuotientMk p
        (MaxEverywhereUnramifiedProPGaloisGroup F p) σ) = 1 at hq
    change (AlgEquiv.restrictNormalHom (H F p)) σ = 1 at hq
    have hfix : (H F p).fixingSubgroup ≤
        (powerCommutatorFixedField F p).fixingSubgroup := by
      intro τ hτ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
      intro x hx
      exact hτ x
        (powerCommutatorFixedField_le_hilbertInMaximal F p hpOdd hx)
    have hσH : σ ∈ (H F p).fixingSubgroup := by
      rw [← (H F p).restrictNormalHom_ker]
      exact hq
    have hσD : σ ∈
        (powerCommutatorFixedField F p).fixingSubgroup := hfix hσH
    rw [show (powerCommutatorFixedField F p).fixingSubgroup =
      (powerCommutatorClosed F p).toSubgroup from
        InfiniteGalois.fixingSubgroup_fixedField
          (powerCommutatorClosed F p)] at hσD
    exact (QuotientGroup.eq_one_iff σ).2 hσD
  · exact bot_le

/-- The Frattini quotient of the maximal unramified pro-`p` Galois group is
the Galois group of the elementary Hilbert layer. -/
noncomputable def maxPowerCommutatorEquivHilbert (hpOdd : Odd p) :
    powerCommutatorQuotient p
        (MaxEverywhereUnramifiedProPGaloisGroup F p) ≃*
      Gal((H F p) / F) :=
  MulEquiv.ofBijective (maxPowerCommutatorToHilbert F p)
    ⟨maxPowerCommutatorToHilbert_injective F p hpOdd,
      maxPowerCommutatorToHilbert_surjective F p⟩

private theorem topologicallyFinitelyGenerated_of_finite_powerCommutatorQuotient
    {q : ℕ} {G : Type*}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Fact q.Prime]
    (hqG : ProCGroups.ProC.HasPGroupOpenNormalBasis q G)
    [Finite (powerCommutatorQuotient q G)] :
    TopologicallyFinitelyGenerated G := by
  classical
  let : (closedPowerCommutator q G).Normal :=
    closedPowerCommutator_normal q G
  let : Fintype (powerCommutatorQuotient q G) := Fintype.ofFinite _
  let liftQ : powerCommutatorQuotient q G → G :=
    Function.surjInv (powerCommutatorQuotientMk_surjective q G)
  let s : Finset G := Finset.univ.image liftQ
  refine ⟨s, (topologicallyGenerates_iff_powerCommutatorQuotient_image hqG).2 ?_⟩
  have himage :
      (powerCommutatorQuotientMk q G) '' (s : Set G) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    refine ⟨liftQ z, ?_, ?_⟩
    · simp [s]
    · exact Function.surjInv_eq
        (powerCommutatorQuotientMk_surjective q G) z
  rw [himage]
  apply top_unique
  rw [Subgroup.closure_univ]
  exact Subgroup.le_topologicalClosure _

/-- For odd `p`, the generator rank of the maximal everywhere-unramified
pro-`p` Galois group is the `p`-class rank. -/
theorem generatorRank_maxUnramified_eq_pClassRank (hpOdd : Odd p) :
    topologicalGeneratorRank
        (MaxEverywhereUnramifiedProPGaloisGroup F p) =
      pClassRank F p := by
  let G := MaxEverywhereUnramifiedProPGaloisGroup F p
  let E := H F p
  let e : powerCommutatorQuotient p G ≃* Gal(E / F) :=
    maxPowerCommutatorEquivHilbert F p hpOdd
  let : Finite (powerCommutatorQuotient p G) :=
    Finite.of_equiv Gal(E / F) e.symm.toEquiv
  have hpG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G :=
    maxEverywhereUnramifiedProPGaloisGroup_hasPGroupOpenNormalBasis
      F p hpOdd
  have hfg : TopologicallyFinitelyGenerated G :=
    topologicallyFinitelyGenerated_of_finite_powerCommutatorQuotient hpG
  let : IsMulCommutative (powerCommutatorQuotient p G) :=
    powerCommutatorQuotient_isMulCommutative p G
  let : Module (ZMod p)
      (Additive (powerCommutatorQuotient p G)) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact powerCommutatorQuotient_pow_eq_one p G (Additive.toMul x))
  let : Module (ZMod p) (Additive Gal(E / F)) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact hilbertElementaryLayerInMaximal_galois_pow_eq_one
        F p (Additive.toMul x))
  let eAdd : Additive (powerCommutatorQuotient p G) ≃+
      Additive Gal(E / F) := e.toAdditive
  let eLin : Additive (powerCommutatorQuotient p G) ≃ₗ[ZMod p]
      Additive Gal(E / F) :=
    LinearEquiv.ofBijective
      (eAdd.toAddMonoidHom.toZModLinearMap p) eAdd.bijective
  calc
    topologicalGeneratorRank G =
        Module.finrank (ZMod p)
          (Additive (powerCommutatorQuotient p G)) :=
      topologicalGeneratorRank_eq_powerCommutatorQuotient_finrank hpG hfg
    _ = Module.finrank (ZMod p) (Additive Gal(E / F)) :=
      eLin.finrank_eq
    _ = pClassRank F p :=
      finrank_hilbertElementaryLayerInMaximal_galois_eq_pClassRank F p

end ClassFieldTower.Martinet
