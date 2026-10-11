/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.ContinuousTransgression
import Nyll.GaloisCohomology.ProP.FiniteTransgressionExact
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Defs

/-!
# Exactness of continuous transgression

For an open normal subgroup, restriction of an ambient continuous mod-`p` character lands in
the conjugation-invariant continuous characters.  Its range is exactly the kernel of the
continuous factor-set transgression.
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

local instance continuousExactZModAddCommGroup : AddCommGroup (ZMod p) :=
  (ZMod.instField p).toDivisionRing.toAddCommGroup

local instance continuousExactH1Module
    {q : ℕ} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := H)) :=
  continuousH1ZModModule

/-- Restriction of an ambient continuous character to an open normal subgroup. -/
def continuousCharacterRestrictionAddHom
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    ContinuousH1ZMod (p := p) (G := G) →+ InvariantContinuousH1 U where
  toFun psi := by
    let restricted : ContinuousH1ZMod (p := p) (G := (U.1 : Subgroup G)) :=
      { toFun := fun n ↦ psi (Additive.ofMul n.1)
        map_zero' := psi.map_zero
        map_add' := fun n m ↦ psi.map_add (Additive.ofMul n.1) (Additive.ofMul m.1)
        continuous_toFun := psi.continuous_toFun.comp continuous_subtype_val }
    exact ⟨restricted, by
      intro g n
      change psi (Additive.ofMul (g * n.1 * g⁻¹)) = psi (Additive.ofMul n.1)
      rw [show Additive.ofMul (g * n.1 * g⁻¹) =
          Additive.ofMul g + Additive.ofMul n.1 + Additive.ofMul g⁻¹ by rfl,
        map_add, map_add,
        show Additive.ofMul g⁻¹ = -(Additive.ofMul g) by rfl, map_neg]
      abel⟩
  map_zero' := by
    apply Subtype.ext
    ext n
    rfl
  map_add' := by
    intro psi phi
    apply Subtype.ext
    ext n
    rfl

/-- Linear restriction of ambient continuous degree-one classes. -/
noncomputable def continuousCharacterRestrictionLinearMap
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    ContinuousH1ZMod (p := p) (G := G) →ₗ[ZMod p] InvariantContinuousH1 U :=
  (continuousCharacterRestrictionAddHom U).toZModLinearMap p

/-- The normalized inhomogeneous value of a continuous homogeneous one-cochain. -/
def continuousHomogeneousOneCochainNormalizedValue
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (c : (trivialZModPCochainsLifted p (G ⧸ (U.1 : Subgroup G))).X 1)
    (q : G ⧸ (U.1 : Subgroup G)) : ZMod p :=
  (c.1 1 q).down

/-- Continuous homogeneous one-cochains are invariant under simultaneous left translation. -/
theorem continuousHomogeneousOneCochain_invariant
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (c : (trivialZModPCochainsLifted p (G ⧸ (U.1 : Subgroup G))).X 1)
    (a q r : G ⧸ (U.1 : Subgroup G)) :
    c.1 (a⁻¹ * q) (a⁻¹ * r) = c.1 q r := by
  have hc := c.2 a
  have hcr := congrArg (fun tau ↦ tau q r) hc
  have hcr' :
      (trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))).ρ a
          (c.1 (a⁻¹ * q) (a⁻¹ * r)) = c.1 q r := by
    simpa only [ContRepresentation.coind₁_apply_apply] using hcr
  exact (trivialZModPLifted_action p (G ⧸ (U.1 : Subgroup G)) a _).symm.trans hcr'

/-- A continuous homogeneous primitive gives the inhomogeneous factor-set coboundary. -/
theorem continuousHomogeneousOneCochainNormalizedValue_primitive
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U)
    (c : (trivialZModPCochainsLifted p (G ⧸ (U.1 : Subgroup G))).X 1)
    (hc : ((trivialZModPCochainsLifted p
      (G ⧸ (U.1 : Subgroup G))).d 1 2).hom c =
        continuousTransgressionHomogeneousCochain U chi)
    (q r : G ⧸ (U.1 : Subgroup G)) :
    continuousHomogeneousOneCochainNormalizedValue U c r -
        continuousHomogeneousOneCochainNormalizedValue U c (q * r) +
          continuousHomogeneousOneCochainNormalizedValue U c q =
      transgressionFactor (U.1 : Subgroup G)
        (characterOfH1 chi.1).toMonoidHom q r := by
  let A := trivialZModPLifted p (G ⧸ (U.1 : Subgroup G))
  have hd := TopRep.homogeneousCochains.d_apply A 1 c
  have hdpoint := congrArg (fun tau ↦ tau 1 q (q * r)) hd
  have hcpoint := congrArg (fun tau ↦ tau.1 1 q (q * r)) hc
  rw [hdpoint] at hcpoint
  simp only [Nat.reduceAdd, TopRep.hom_d_succ, TopRep.d_zero,
    TopRep.hom_ofHom, ContIntertwiningMap.sub_apply,
    ContRepresentation.coind₁ι_toFun, ContRepresentation.coind₁Map_toFun,
    ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk] at hcpoint
  have hinv := continuousHomogeneousOneCochain_invariant U c q q (q * r)
  have hinv' : c.1 q (q * r) = c.1 1 r := by
    convert hinv.symm using 1
    all_goals group
  rw [hinv'] at hcpoint
  have htrans : (continuousTransgressionHomogeneousCochain U chi).1 1 q (q * r) =
      ULift.up (transgressionFactor (U.1 : Subgroup G)
        (characterOfH1 chi.1).toMonoidHom q r) := by
    change ULift.up (transgressionFactor (U.1 : Subgroup G)
      (characterOfH1 chi.1).toMonoidHom (1⁻¹ * q) (q⁻¹ * (q * r))) = _
    congr 1
    all_goals group
  rw [htrans] at hcpoint
  let e : ULift.{u} (ZMod p) ≃ₗ[ZMod p] ZMod p := ULift.moduleEquiv
  change e (c.1 1 r) - e (c.1 1 (q * r)) + e (c.1 1 q) = _
  calc
    e (c.1 1 r) - e (c.1 1 (q * r)) + e (c.1 1 q) =
        e (c.1 1 r) - (e (c.1 1 (q * r)) - e (c.1 1 q)) := by abel
    _ = e (c.1 1 r) - e (c.1 1 (q * r) - c.1 1 q) :=
      congrArg (fun t ↦ e (c.1 1 r) - t)
        (e.map_sub (c.1 1 (q * r)) (c.1 1 q)).symm
    _ = e (c.1 1 r - (c.1 1 (q * r) - c.1 1 q)) :=
      (e.map_sub (c.1 1 r) (c.1 1 (q * r) - c.1 1 q)).symm
    _ = e (ULift.up (transgressionFactor (U.1 : Subgroup G)
        (characterOfH1 chi.1).toMonoidHom q r)) := congrArg e hcpoint
    _ = transgressionFactor (U.1 : Subgroup G)
        (characterOfH1 chi.1).toMonoidHom q r := rfl

/-- An invariant continuous character extending abstractly to the ambient group has zero
continuous transgression. -/
theorem continuousTransgressionLinearMap_eq_zero_of_extendsToAmbient
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U)
    (psi : MonoidHom G (Multiplicative (ZMod p)))
    (hpsi : psi.comp (U.1 : Subgroup G).subtype =
      (characterOfH1 chi.1).toMonoidHom) :
    continuousTransgressionLinearMap U chi = 0 := by
  let N : Subgroup G := (U.1 : Subgroup G)
  let : Finite (G ⧸ N) := U.2.1
  let z := continuousTransgressionHomogeneousCocycle U chi
  let s : G ⧸ N → ZMod p := fun q ↦ (psi (Quotient.out q)).toAdd
  let b : C(G ⧸ N, ULift.{u} (ZMod p)) :=
    ⟨fun q ↦ ULift.up (-s q + s 1), continuous_of_discreteTopology⟩
  have hnormalized (q r : G ⧸ N) :
      normalizedCocycle z q r = ULift.up
        (transgressionFactor N (characterOfH1 chi.1).toMonoidHom q r -
          transgressionFactor N (characterOfH1 chi.1).toMonoidHom 1 1) := by
    unfold normalizedCocycle
    change (((trivialZModPCochainsLifted p (G ⧸ N)).iCycles 2).hom z).1
          1 q (q * r) -
        (((trivialZModPCochainsLifted p (G ⧸ N)).iCycles 2).hom z).1 1 1 1 = _
    rw [show ((trivialZModPCochainsLifted p (G ⧸ N)).iCycles 2).hom z =
        continuousTransgressionHomogeneousCochain U chi by
      exact iCycles_continuousTransgressionHomogeneousCocycle U chi]
    change ULift.up (transgressionFactor N (characterOfH1 chi.1).toMonoidHom
        (1⁻¹ * q) (q⁻¹ * (q * r))) -
      ULift.up (transgressionFactor N (characterOfH1 chi.1).toMonoidHom
        (1⁻¹ * 1) (1⁻¹ * 1)) = _
    simp only [inv_one, one_mul, inv_mul_cancel_left]
    rfl
  have hb : ∀ q r : G ⧸ N,
      b (q * r) = b q + b r + normalizedCocycle z q r := by
    intro q r
    rw [hnormalized]
    apply ULift.ext
    change -s (q * r) + s 1 =
      (-s q + s 1) + (-s r + s 1) +
        (transgressionFactor N (characterOfH1 chi.1).toMonoidHom q r -
          transgressionFactor N (characterOfH1 chi.1).toMonoidHom 1 1)
    rw [transgressionFactor_eq_extension_coboundary N
        (characterOfH1 chi.1).toMonoidHom psi hpsi,
      transgressionFactor_one_one_eq_extension_value N
        (characterOfH1 chi.1).toMonoidHom psi hpsi]
    dsimp only [s]
    abel
  let K := trivialZModPCochainsLifted p (G ⧸ N)
  let c : K.X 1 := homogeneousPrimitive z b
  have hc : (K.d 1 2).hom c = (K.iCycles 2).hom z :=
    homogeneousPrimitive_boundary z b hb
  have hzc : (K.toCycles 1 2).hom c = z := by
    apply topModule_mono_injective_lifted (K.iCycles 2)
    calc
      (K.iCycles 2).hom ((K.toCycles 1 2).hom c) = (K.d 1 2).hom c := by
        exact ConcreteCategory.congr_hom (K.toCycles_i 1 2) c
      _ = (K.iCycles 2).hom z := hc
  change ContinuousCohomology.π (trivialZModPLifted p (G ⧸ N)) 2 z = 0
  rw [← hzc]
  exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ 1 2) c

/-- Vanishing continuous transgression gives an ambient continuous extension. -/
theorem exists_continuous_extension_of_continuousTransgression_eq_zero
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G)
    (chi : InvariantContinuousH1 U)
    (hzero : continuousTransgressionLinearMap U chi = 0) :
    ∃ psi : ContinuousH1ZMod (p := p) (G := G),
      continuousCharacterRestrictionLinearMap U psi = chi := by
  let N : Subgroup G := (U.1 : Subgroup G)
  let : Finite (G ⧸ N) := U.2.1
  let z := continuousTransgressionHomogeneousCocycle U chi
  have hzero' : ContinuousCohomology.π
      (trivialZModPLifted p (G ⧸ N)) 2 z = 0 := by
    exact hzero
  obtain ⟨c, hc⟩ := exists_boundary_of_homologyπ_apply_eq_zero
    (trivialZModPLifted p (G ⧸ N)) 1 z hzero'
  have hc' : ((trivialZModPCochainsLifted p (G ⧸ N)).d 1 2).hom c =
      continuousTransgressionHomogeneousCochain U chi := by
    rw [hc, iCycles_continuousTransgressionHomogeneousCocycle]
  let b : G ⧸ N → ZMod p := continuousHomogeneousOneCochainNormalizedValue U c
  have hb : ∀ q r, b r - b (q * r) + b q =
      transgressionFactor N (characterOfH1 chi.1).toMonoidHom q r := by
    exact continuousHomogeneousOneCochainNormalizedValue_primitive U chi c hc'
  let psi : MonoidHom G (Multiplicative (ZMod p)) :=
    transgressionKernelExtension N (characterOfH1 chi.1).toMonoidHom
      (fun g n ↦ congrArg Multiplicative.ofAdd (chi.2 g n)) b hb
  have hrestrict : psi.comp N.subtype = (characterOfH1 chi.1).toMonoidHom :=
    transgressionKernelExtension_restrict N (characterOfH1 chi.1).toMonoidHom
      (fun g n ↦ congrArg Multiplicative.ofAdd (chi.2 g n)) b hb
  let K : Subgroup N := (characterOfH1 chi.1).toMonoidHom.ker
  have hKopenN : IsOpen ((K : Subgroup N) : Set N) := by
    change IsOpen ((characterOfH1 chi.1) ⁻¹' ({1} : Set (Multiplicative (ZMod p))))
    exact (isOpen_discrete _).preimage (characterOfH1 chi.1).continuous_toFun
  have hmapKopen : IsOpen (((K.map N.subtype : Subgroup G) : Set G)) := by
    change IsOpen (N.subtype '' ((K : Subgroup N) : Set N))
    exact (openNormalSubgroup_isOpen (G := G) U.1).isOpenMap_subtype_val _ hKopenN
  have hmapKle : K.map N.subtype ≤ psi.ker := by
    rintro _ ⟨n, hn, rfl⟩
    change psi n.1 = 1
    have hnres := DFunLike.congr_fun hrestrict n
    exact hnres.trans hn
  have hpsiKerOpen : IsOpen ((psi.ker : Subgroup G) : Set G) :=
    Subgroup.isOpen_mono hmapKle hmapKopen
  have hpsiContinuous : Continuous psi :=
    ProCGroups.MonoidHom.continuous_of_isOpen_ker_to_discrete psi hpsiKerOpen
  let psiContinuous : G →ₜ* Multiplicative (ZMod p) :=
    { toMonoidHom := psi
      continuous_toFun := hpsiContinuous }
  refine ⟨h1OfCharacter psiContinuous, ?_⟩
  apply Subtype.ext
  ext n
  change (psi (Additive.toMul n).1).toAdd = chi.1 n
  have hnres := DFunLike.congr_fun hrestrict (Additive.toMul n)
  exact congrArg Multiplicative.toAdd hnres

/-- The continuous low-degree transgression sequence is exact at invariant subgroup
characters. -/
theorem continuousCharacterRestriction_range_eq_transgression_ker
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) G) :
    LinearMap.range (continuousCharacterRestrictionLinearMap U) =
      LinearMap.ker (continuousTransgressionLinearMap U) := by
  ext chi
  constructor
  · rintro ⟨psi, rfl⟩
    rw [LinearMap.mem_ker]
    apply continuousTransgressionLinearMap_eq_zero_of_extendsToAmbient
      U (continuousCharacterRestrictionLinearMap U psi)
      (characterOfH1 psi).toMonoidHom
    ext n
    rfl
  · intro hchi
    rw [LinearMap.mem_ker] at hchi
    obtain ⟨psi, hpsi⟩ :=
      exists_continuous_extension_of_continuousTransgression_eq_zero U chi hchi
    exact ⟨psi, hpsi⟩

end

end ClassFieldTower.Cohomology
