/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.InflationTransgressionRange
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic

/-!
# Primitives for continuous inflation--transgression exactness

This file extracts the normalized degree-one primitive of an inflated degree-two cocycle and
uses its restriction to the open normal subgroup to reconstruct the invariant continuous
character occurring in transgression.
-/

open CategoryTheory TopRep ContRepresentation
open scoped Topology

namespace ClassFieldTower.Cohomology

open ProCGroups ProCGroups.ProC
open ClassFieldTower.ProP
open ClassFieldTower.ProP.FreeProPH2Cocycle

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Normalize a homogeneous degree-one cochain at the identity. -/
def normalizedInflationPrimitiveValue
    (c : (trivialZModPCochainsLifted p G).X 1) :
    C(G, ULift.{u} (ZMod p)) where
  toFun g := c.1 1 g - c.1 1 1
  continuous_toFun := (c.1 1).continuous.sub continuous_const

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem normalizedInflationPrimitiveValue_one
    (c : (trivialZModPCochainsLifted p G).X 1) :
    normalizedInflationPrimitiveValue c 1 = 0 := by
  exact sub_self _

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem normalizedInflationPrimitive_boundary
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (z : trivialZModPCocyclesLifted p (G ⧸ (U.1 : Subgroup G)) 2)
    (c : (trivialZModPCochainsLifted p G).X 1)
    (hc : ((trivialZModPCochainsLifted p G).d 1 2).hom c =
      (((trivialZModPCochainsMapLifted p
        (OpenNormalSubgroupInClass.quotientProj U)).f 2).hom
          (((trivialZModPCochainsLifted p
            (G ⧸ (U.1 : Subgroup G))).iCycles 2).hom z)))
    (g h : G) :
    normalizedInflationPrimitiveValue c h -
        normalizedInflationPrimitiveValue c (g * h) +
          normalizedInflationPrimitiveValue c g =
      normalizedCocycle z
        (OpenNormalSubgroupInClass.quotientProj U g)
        (OpenNormalSubgroupInClass.quotientProj U h) := by
  have hd := TopRep.homogeneousCochains.d_apply
    (trivialZModPLifted p G) 1 c
  have hdpoint := congrArg (fun tau => tau 1 g (g * h)) hd
  have hcpoint := congrArg (fun tau => tau.1 1 g (g * h)) hc
  rw [hdpoint] at hcpoint
  simp only [Nat.reduceAdd, TopRep.hom_d_succ, TopRep.d_zero,
    TopRep.hom_ofHom, ContIntertwiningMap.sub_apply,
    ContRepresentation.coind₁ι_toFun, ContRepresentation.coind₁Map_toFun,
    ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk] at hcpoint
  have hinv := c.2 g
  have hinvpoint := congrArg (fun tau => tau g (g * h)) hinv
  have hinv' : c.1 g (g * h) = c.1 1 h := by
    have hinvAction :
        ((TopRep.resolutionX (trivialZModPLifted p G) 0).ρ g)
            (c.1 1 h) = c.1 g (g * h) := by
      simpa only [ContRepresentation.coind₁_apply_apply, ← mul_assoc,
        inv_mul_cancel, one_mul] using hinvpoint
    have htriv :
        ((TopRep.resolutionX (trivialZModPLifted p G) 0).ρ g)
            (c.1 1 h) = c.1 1 h := by
      change (trivialZModPLifted p G).ρ g (c.1 1 h) = c.1 1 h
      exact trivialZModPLifted_action p G g _
    exact hinvAction.symm.trans htriv
  rw [hinv'] at hcpoint
  change c.1 1 h - (c.1 1 (g * h) - c.1 1 g) =
    (((trivialZModPCochainsLifted p
      (G ⧸ (U.1 : Subgroup G))).iCycles 2).hom z).1
        (OpenNormalSubgroupInClass.quotientProj U 1)
        (OpenNormalSubgroupInClass.quotientProj U g)
        (OpenNormalSubgroupInClass.quotientProj U (g * h)) at hcpoint
  simp only [map_one, map_mul] at hcpoint
  have hcbase := congrArg (fun tau => tau.1 1 1 1) hc
  have hdbase := congrArg (fun tau => tau 1 1 1) hd
  rw [hdbase] at hcbase
  simp only [Nat.reduceAdd, TopRep.hom_d_succ, TopRep.d_zero,
    TopRep.hom_ofHom, ContIntertwiningMap.sub_apply,
    ContRepresentation.coind₁ι_toFun, ContRepresentation.coind₁Map_toFun,
    ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, sub_self, sub_zero] at hcbase
  change c.1 1 1 =
    (((trivialZModPCochainsLifted p
      (G ⧸ (U.1 : Subgroup G))).iCycles 2).hom z).1 1 1 1 at hcbase
  have hcpoint' : c.1 1 h - c.1 1 (g * h) + c.1 1 g =
      (((trivialZModPCochainsLifted p
        (G ⧸ (U.1 : Subgroup G))).iCycles 2).hom z).1 1
          (OpenNormalSubgroupInClass.quotientProj U g)
          (OpenNormalSubgroupInClass.quotientProj U g *
            OpenNormalSubgroupInClass.quotientProj U h) := by
    have hleft :
        c.1 1 h - c.1 1 (g * h) + c.1 1 g =
          c.1 1 h - (c.1 1 (g * h) - c.1 1 g) := by
      abel
    rw [hleft]
    exact hcpoint
  unfold normalizedInflationPrimitiveValue normalizedCocycle
  calc
    (c.1 1 h - c.1 1 1) - (c.1 1 (g * h) - c.1 1 1) +
          (c.1 1 g - c.1 1 1) =
        (c.1 1 h - c.1 1 (g * h) + c.1 1 g) - c.1 1 1 := by abel
    _ = _ := by
      rw [hcpoint', hcbase]
      rfl

/-- Restrict the negative normalized primitive to the open normal subgroup.  The boundary
identity makes it a continuous character, and makes that character invariant under ambient
conjugation. -/
noncomputable def invariantContinuousH1OfInflationPrimitive
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (z : trivialZModPCocyclesLifted p (G ⧸ (U.1 : Subgroup G)) 2)
    (c : (trivialZModPCochainsLifted p G).X 1)
    (hc : ((trivialZModPCochainsLifted p G).d 1 2).hom c =
      (((trivialZModPCochainsMapLifted p
        (OpenNormalSubgroupInClass.quotientProj U)).f 2).hom
          (((trivialZModPCochainsLifted p
            (G ⧸ (U.1 : Subgroup G))).iCycles 2).hom z))) :
    InvariantContinuousH1 U := by
  let f := normalizedInflationPrimitiveValue c
  let chi : ContinuousH1ZMod (p := p) (G := (U.1 : Subgroup G)) :=
    { toFun := fun n => -(f n.toMul).down
      map_zero' := by
        change -(f (1 : G)).down = 0
        rw [normalizedInflationPrimitiveValue_one]
        change -(0 : ZMod p) = 0
        abel
      map_add' := by
        intro n m
        have hn : OpenNormalSubgroupInClass.quotientProj U n.toMul = 1 :=
          (QuotientGroup.eq_one_iff (N := (U.1 : Subgroup G)) (x := n.toMul.1)).2
            n.toMul.2
        have hm : OpenNormalSubgroupInClass.quotientProj U m.toMul = 1 :=
          (QuotientGroup.eq_one_iff (N := (U.1 : Subgroup G)) (x := m.toMul.1)).2
            m.toMul.2
        have hb := normalizedInflationPrimitive_boundary U z c hc n.toMul m.toMul
        rw [hn, hm, normalizedCocycle_one_left] at hb
        have hbdown := congrArg (fun a : ULift.{u} (ZMod p) => a.down) hb
        change (f m.toMul).down - (f (n.toMul * m.toMul)).down +
            (f n.toMul).down = 0 at hbdown
        have hsum : (f (n.toMul * m.toMul)).down =
            (f n.toMul).down + (f m.toMul).down := by
          rw [← sub_eq_zero]
          calc
            (f (n.toMul * m.toMul)).down -
                ((f n.toMul).down + (f m.toMul).down) =
              -((f m.toMul).down - (f (n.toMul * m.toMul)).down +
                (f n.toMul).down) := by abel
            _ = 0 := by rw [hbdown]; abel
        change -(f (n.toMul * m.toMul)).down =
          -(f n.toMul).down + -(f m.toMul).down
        rw [hsum]
        abel
      continuous_toFun := by
        have hsub : Continuous
            (fun n : Additive (U.1 : Subgroup G) => (n.toMul.1 : G)) :=
          continuous_subtype_val
        exact (((ContinuousLinearEquiv.ulift :
          ULift.{u} (ZMod p) ≃L[ZMod p] ZMod p).continuous.comp
            (f.continuous.comp hsub)).neg) }
  refine ⟨chi, ?_⟩
  intro g n
  have hn : OpenNormalSubgroupInClass.quotientProj U n.1 = 1 :=
    (QuotientGroup.eq_one_iff (N := (U.1 : Subgroup G)) (x := n.1)).2 n.2
  have hgn := normalizedInflationPrimitive_boundary U z c hc g n.1
  rw [hn, normalizedCocycle_one_right] at hgn
  have hgn' : f (g * n.1) = f g + f n.1 := by
    rw [add_comm, ← sub_eq_zero]
    calc
      f (g * n.1) - (f n.1 + f g) =
          -(f n.1 - f (g * n.1) + f g) := by abel
      _ = 0 := by rw [show f n.1 - f (g * n.1) + f g = 0 from hgn]; abel
  have hconj := normalizedInflationPrimitive_boundary U z c hc
    (g * n.1) (g⁻¹)
  have hbase := normalizedInflationPrimitive_boundary U z c hc g (g⁻¹)
  have hqgn : OpenNormalSubgroupInClass.quotientProj U (g * n.1) =
      OpenNormalSubgroupInClass.quotientProj U g := by
    rw [map_mul, hn, mul_one]
  have hqinv : OpenNormalSubgroupInClass.quotientProj U (g⁻¹) =
      (OpenNormalSubgroupInClass.quotientProj U g)⁻¹ :=
    map_inv (OpenNormalSubgroupInClass.quotientProj U) g
  rw [hqgn, hqinv] at hconj
  rw [hqinv, show g * g⁻¹ = 1 by simp,
    normalizedInflationPrimitiveValue_one] at hbase
  have hfconj : f (g * n.1 * g⁻¹) = f n.1 := by
    rw [hgn'] at hconj
    have heq := hconj.trans hbase.symm
    change f (g⁻¹) - f (g * n.1 * g⁻¹) + (f g + f n.1) =
      f (g⁻¹) - 0 + f g at heq
    rw [← sub_eq_zero]
    calc
      f (g * n.1 * g⁻¹) - f n.1 =
          -((f (g⁻¹) - f (g * n.1 * g⁻¹) + (f g + f n.1)) -
            (f (g⁻¹) - 0 + f g)) := by abel
      _ = 0 := by rw [heq]; abel
  change -(f (g * n.1 * g⁻¹)).down = -(f n.1).down
  rw [hfconj]

/-- The quotient correction obtained by evaluating the normalized primitive on chosen quotient
representatives. -/
noncomputable def inflationPrimitiveQuotientCorrection
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (c : (trivialZModPCochainsLifted p G).X 1) :
    C(G ⧸ (U.1 : Subgroup G), ULift.{u} (ZMod p)) where
  toFun q := normalizedInflationPrimitiveValue c (Quotient.out q) -
    normalizedInflationPrimitiveValue c
      (Quotient.out (1 : G ⧸ (U.1 : Subgroup G)))
  continuous_toFun := continuous_of_discreteTopology

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem reconstructed_transgressionFactor
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (z : trivialZModPCocyclesLifted p (G ⧸ (U.1 : Subgroup G)) 2)
    (c : (trivialZModPCochainsLifted p G).X 1)
    (hc : ((trivialZModPCochainsLifted p G).d 1 2).hom c =
      (((trivialZModPCochainsMapLifted p
        (OpenNormalSubgroupInClass.quotientProj U)).f 2).hom
          (((trivialZModPCochainsLifted p
            (G ⧸ (U.1 : Subgroup G))).iCycles 2).hom z)))
    (q r : G ⧸ (U.1 : Subgroup G)) :
    ULift.up (transgressionFactor (U.1 : Subgroup G)
        (characterOfH1
          (invariantContinuousH1OfInflationPrimitive U z c hc).1).toMonoidHom q r) =
      normalizedCocycle z q r -
        normalizedInflationPrimitiveValue c (Quotient.out q) -
        normalizedInflationPrimitiveValue c (Quotient.out r) +
        normalizedInflationPrimitiveValue c (Quotient.out (q * r)) := by
  let f := normalizedInflationPrimitiveValue c
  have hs (a : G ⧸ (U.1 : Subgroup G)) :
      OpenNormalSubgroupInClass.quotientProj U (Quotient.out a) = a :=
    QuotientGroup.out_eq' a
  have hqr := normalizedInflationPrimitive_boundary U z c hc
    (Quotient.out q) (Quotient.out r)
  rw [hs q, hs r] at hqr
  have hmul : f (Quotient.out q * Quotient.out r) =
      f (Quotient.out q) + f (Quotient.out r) - normalizedCocycle z q r := by
    rw [← sub_eq_zero]
    calc
      f (Quotient.out q * Quotient.out r) -
          (f (Quotient.out q) + f (Quotient.out r) - normalizedCocycle z q r) =
        -(f (Quotient.out r) - f (Quotient.out q * Quotient.out r) +
          f (Quotient.out q) - normalizedCocycle z q r) := by abel
      _ = 0 := by rw [show f (Quotient.out r) -
        f (Quotient.out q * Quotient.out r) + f (Quotient.out q) =
          normalizedCocycle z q r from hqr]; abel
  have hfactor := normalizedInflationPrimitive_boundary U z c hc
    (Quotient.out q * Quotient.out r) ((Quotient.out (q * r))⁻¹)
  have hbase := normalizedInflationPrimitive_boundary U z c hc
    (Quotient.out (q * r)) ((Quotient.out (q * r))⁻¹)
  have hsMul : OpenNormalSubgroupInClass.quotientProj U
      (Quotient.out q * Quotient.out r) = q * r := by rw [map_mul, hs q, hs r]
  have hsInv : OpenNormalSubgroupInClass.quotientProj U
      ((Quotient.out (q * r))⁻¹) = (q * r)⁻¹ := by
    rw [map_inv, hs]
  rw [hsMul, hsInv] at hfactor
  rw [hs (q * r), hsInv, mul_inv_cancel,
    normalizedInflationPrimitiveValue_one] at hbase
  have hk : f (quotientSectionFactor (U.1 : Subgroup G) q r) =
      f (Quotient.out q * Quotient.out r) - f (Quotient.out (q * r)) := by
    have heq := hfactor.trans hbase.symm
    change f ((Quotient.out (q * r))⁻¹) -
        f ((Quotient.out q * Quotient.out r) * (Quotient.out (q * r))⁻¹) +
          f (Quotient.out q * Quotient.out r) =
      f ((Quotient.out (q * r))⁻¹) - 0 + f (Quotient.out (q * r)) at heq
    change f ((Quotient.out q * Quotient.out r) * (Quotient.out (q * r))⁻¹) =
      f (Quotient.out q * Quotient.out r) - f (Quotient.out (q * r))
    rw [← sub_eq_zero]
    calc
      f ((Quotient.out q * Quotient.out r) * (Quotient.out (q * r))⁻¹) -
          (f (Quotient.out q * Quotient.out r) - f (Quotient.out (q * r))) =
        -((f ((Quotient.out (q * r))⁻¹) -
            f ((Quotient.out q * Quotient.out r) * (Quotient.out (q * r))⁻¹) +
              f (Quotient.out q * Quotient.out r)) -
          (f ((Quotient.out (q * r))⁻¹) - 0 +
            f (Quotient.out (q * r)))) := by abel
      _ = 0 := by rw [heq]; abel
  apply ULift.ext
  change (-(f (quotientSectionFactor (U.1 : Subgroup G) q r : G)).down) = _
  rw [hk, hmul]
  change -((f (Quotient.out q)).down + (f (Quotient.out r)).down -
      (normalizedCocycle z q r).down - (f (Quotient.out (q * r))).down) =
    (normalizedCocycle z q r).down - (f (Quotient.out q)).down -
      (f (Quotient.out r)).down + (f (Quotient.out (q * r))).down
  abel

end

end ClassFieldTower.Cohomology
