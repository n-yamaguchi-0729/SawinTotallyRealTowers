/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPKummerComparison
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.LocalIntrinsicUnramifiedH1Line
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceInertiaTransport
import GaloisCohomology.Kummer.Concrete.SimpleExtension

set_option autoImplicit false
/-!
# Intrinsic inertia and local Kummer characters

The standard algebraic-closure Kummer character is transported to the local
separable-closure model. Its kernel is the stabilizer of the chosen simple
Kummer root, without imposing a residue-characteristic restriction.
-/

open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP KummerTheory LocalClassFieldTheory

variable (p : ℕ) [Fact p.Prime]

local instance localKummerInertiaTopology : TopologicalSpace (ZMod p) := ⊥
local instance localKummerInertiaDiscreteTopology : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _
local instance localKummerInertiaZModAddCommGroup : AddCommGroup (ZMod p) :=
  (ZMod.commRing p).toAddCommGroup
local instance localKummerInertiaH1Module
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) :=
  continuousH1ZModModule

/-- Continuous `H¹` is transported covariantly along a topological group equivalence. -/
noncomputable def continuousH1ZModCongr
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) :
    ContinuousH1ZMod (p := p) (G := G) ≃ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := H) := by
  let f : G →ₜ* H :=
    { toMonoidHom := e.toMulEquiv.toMonoidHom
      continuous_toFun := e.continuous }
  let g : H →ₜ* G :=
    { toMonoidHom := e.symm.toMulEquiv.toMonoidHom
      continuous_toFun := e.symm.continuous }
  let E : ContinuousH1ZMod (p := p) (G := G) ≃+
      ContinuousH1ZMod (p := p) (G := H) :=
    { toFun := fun chi ↦ h1OfCharacter ((characterOfH1 chi).comp g)
      invFun := fun chi ↦ h1OfCharacter ((characterOfH1 chi).comp f)
      left_inv := by
        intro chi
        apply ContinuousAddMonoidHom.ext
        intro sigma
        change chi (Additive.ofMul (e.symm (e sigma.toMul))) = chi sigma
        simp only [e.symm_apply_apply, ofMul_toMul]
      right_inv := by
        intro chi
        apply ContinuousAddMonoidHom.ext
        intro sigma
        change chi (Additive.ofMul (e (e.symm sigma.toMul))) = chi sigma
        simp only [e.apply_symm_apply, ofMul_toMul]
      map_add' := by intro chi psi; ext sigma; rfl }
  exact { E with map_smul' := ZMod.map_smul E }

@[simp]
theorem continuousH1ZModCongr_apply
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (chi : ContinuousH1ZMod (p := p) (G := G)) (sigma : H) :
    continuousH1ZModCongr p e chi (Additive.ofMul sigma) =
      chi (Additive.ofMul (e.symm sigma)) := rfl

/-- Change from the algebraic-closure model to the intrinsic separable-closure model. -/
noncomputable def localStandardH1LinearEquivSeparable
    (K : Type) [Field K] :
    ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K) ≃ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := Gal(SeparableClosure K / K)) :=
  continuousH1ZModCongr p
    (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv K)

@[simp]
theorem localStandardH1LinearEquivSeparable_apply
    (K : Type) [Field K]
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup K))
    (sigma : Gal(SeparableClosure K / K)) :
    localStandardH1LinearEquivSeparable p K chi (Additive.ofMul sigma) =
      chi (Additive.ofMul
        ((RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv
          K).symm sigma)) := rfl

private theorem rootQuotient_eq_of_same_pow
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (u u' : Lˣ)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a)
    (hu' : u' ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a)
    (sigma : Gal(L / K)) :
    rootQuotient (K := K) (L := L) u sigma =
      rootQuotient (K := K) (L := L) u' sigma := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := L) n
  let delta : D.carrier := ⟨a, u, hu⟩
  let hfixed := nthRootsOfUnity_fixed (K := K) (L := L) n
    (nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := L) n hmu)
  exact (D.rootCharacter_eq_of_same_pow hfixed delta hu sigma).trans
    (D.rootCharacter_eq_of_same_pow hfixed delta hu' sigma).symm

/-- The kernel of a Kummer character is precisely the stabilizer of any root
with the prescribed power. -/
theorem absoluteKummerH1_mk_eq_zero_iff_root_fixed
    (K : Type) [Field K] [CharZero K]
    (hmu : (primitiveRoots p K).Nonempty) (a : Kˣ)
    (u : (AlgebraicClosure K)ˣ)
    (hu : u ^ p = Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a)
    (sigma : Field.absoluteGaloisGroup K) :
    absoluteKummerContinuousH1LinearEquiv K p hmu
        (Additive.ofMul
          (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a))
        (Additive.ofMul sigma) = 0 ↔
      absoluteGaloisGroupContinuousMulEquiv K sigma • u = u := by
  rw [absoluteKummerContinuousH1LinearEquiv_mk_apply]
  let e := absoluteMuPLinearEquivZMod K p hmu
  have hq : rootQuotient (K := K) (L := AlgebraicClosure K)
      (absoluteKummerChosenRoot K p a) sigma =
        rootQuotient (K := K) (L := AlgebraicClosure K) u sigma :=
    rootQuotient_eq_of_same_pow (p.toPNat (Fact.out : p.Prime).pos) hmu a
      (absoluteKummerChosenRoot K p a) u (absoluteKummerChosenRoot_pow K p a) hu sigma
  constructor
  · intro h
    have hz : absoluteKummerMuPRootCocycle K p a sigma = 0 := by
      apply e.injective
      exact h.trans e.map_zero.symm
    have hr : rootQuotient (K := K) (L := AlgebraicClosure K)
        (absoluteKummerChosenRoot K p a) sigma = 1 :=
      congrArg (fun x : AbsoluteMuP K p ↦ x.toMul.1) hz
    rw [hq] at hr
    exact (rootQuotient_eq_one_iff (K := K) (L := AlgebraicClosure K) u sigma).1 hr
  · intro h
    have hz : absoluteKummerMuPRootCocycle K p a sigma = 0 := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change rootQuotient (K := K) (L := AlgebraicClosure K)
        (absoluteKummerChosenRoot K p a) sigma = 1
      rw [hq]
      exact (rootQuotient_eq_one_iff (K := K) (L := AlgebraicClosure K) u sigma).2 h
    rw [hz]
    exact e.map_zero

/-- In the separable-closure model the Kummer character vanishes exactly on
automorphisms fixing the chosen simple Kummer root. -/
theorem localStandardH1LinearEquivSeparable_kummer_eq_zero_iff
    (K : Type) [Field K] [CharZero K]
    (hmu : (primitiveRoots p K).Nonempty) (a : Kˣ)
    (sigma : Gal(SeparableClosure K / K)) :
    localStandardH1LinearEquivSeparable p K
        (absoluteKummerContinuousH1LinearEquiv K p hmu
          (Additive.ofMul
            (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a)))
        (Additive.ofMul sigma) = 0 ↔
      sigma (chosenSimpleKummerRoot K ⟨p, (Fact.out : p.Prime).pos⟩
          (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) a) =
        chosenSimpleKummerRoot K ⟨p, (Fact.out : p.Prime).pos⟩
          (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) a := by
  let n : ℕ+ := (p.toPNat (Fact.out : p.Prime).pos)
  let hnK : ((n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  let E := chosenSimpleKummerExtension K n hnK a
  let f := algebraicClosureAlgEquivSeparableClosure K
  let e :=
    RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv K
  let betaS : (SeparableClosure K)ˣ :=
    Units.map (algebraMap E (SeparableClosure K)).toMonoidHom
      (chosenSimpleKummerRootUnit K n hnK a)
  let betaA : (AlgebraicClosure K)ˣ := Units.map f.symm.toMonoidHom betaS
  have hbetaS : betaS ^ p =
      Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a := by
    apply Units.ext
    exact chosenSimpleKummerRoot_pow K n hnK a
  have hbetaA : betaA ^ p =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a := by
    rw [show betaA = Units.map f.symm.toMonoidHom betaS from rfl, ← map_pow, hbetaS]
    apply Units.ext
    exact f.symm.commutes a.1
  have hequiv : AlgEquiv.autCongr f (e.symm sigma) = sigma := by
    rw [show AlgEquiv.autCongr f = e.toMulEquiv from
      autCongr_algebraicClosureAlgEquivSeparableClosure K]
    exact e.apply_symm_apply sigma
  have htransport (x : AlgebraicClosure K) :
      f ((e.symm sigma) x) = sigma (f x) := by
    have h := DFunLike.congr_fun hequiv (f x)
    simpa only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      f.symm_apply_apply] using h
  rw [localStandardH1LinearEquivSeparable_apply]
  change
    absoluteKummerContinuousH1LinearEquiv K p hmu
        (Additive.ofMul
          (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a))
        (Additive.ofMul (e.symm sigma)) = 0 ↔ _
  constructor
  · intro hzero
    have hfix :=
      (absoluteKummerH1_mk_eq_zero_iff_root_fixed
        p K hmu a betaA hbetaA (e.symm sigma)).1 hzero
    have h := congrArg (fun u : (AlgebraicClosure K)ˣ ↦ f (u : AlgebraicClosure K)) hfix
    change f ((e.symm sigma) (f.symm (betaS : SeparableClosure K))) =
      f (f.symm (betaS : SeparableClosure K)) at h
    rw [htransport, f.apply_symm_apply] at h
    exact h
  · intro hfix
    apply (absoluteKummerH1_mk_eq_zero_iff_root_fixed
      p K hmu a betaA hbetaA (e.symm sigma)).2
    apply Units.ext
    apply f.injective
    change f ((e.symm sigma) (f.symm (betaS : SeparableClosure K))) =
      f (f.symm (betaS : SeparableClosure K))
    rw [htransport, f.apply_symm_apply]
    exact hfix

/-- The intrinsic unramified condition on a Kummer class says exactly that
local inertia fixes its simple Kummer extension. -/
theorem localKummerH1_mem_unramified_iff_inertia_le
    (K : Type) [Field K] [CharZero K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (hmu : (primitiveRoots p K).Nonempty) (a : Kˣ) :
    localStandardH1LinearEquivSeparable p K
        (absoluteKummerContinuousH1LinearEquiv K p hmu
          (Additive.ofMul
            (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a))) ∈
        localIntrinsicUnramifiedH1 K p ↔
      localIntrinsicInertiaSubgroup K ≤
        (chosenSimpleKummerExtension K ⟨p, (Fact.out : p.Prime).pos⟩
          (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) a).fixingSubgroup := by
  let n : ℕ+ := (p.toPNat (Fact.out : p.Prime).pos)
  let hnK : ((n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  let beta := chosenSimpleKummerRoot K n hnK a
  constructor
  · intro ha sigma hsigma
    rw [LinearMap.mem_ker] at ha
    have hz := DFunLike.congr_fun ha
      (Additive.ofMul (⟨sigma, hsigma⟩ : localIntrinsicInertiaSubgroup K))
    have hfix : sigma beta = beta :=
      (localStandardH1LinearEquivSeparable_kummer_eq_zero_iff p K hmu a sigma).1 hz
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change x ∈ IntermediateField.adjoin K {beta} at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
        simpa only [Set.mem_singleton_iff.mp hy] using hfix
    | algebraMap y => exact sigma.commutes y
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
  · intro hI
    rw [LinearMap.mem_ker]
    apply ContinuousAddMonoidHom.ext
    intro sigma
    apply (localStandardH1LinearEquivSeparable_kummer_eq_zero_iff
      p K hmu a sigma.toMul.1).2
    exact ((IntermediateField.mem_fixingSubgroup_iff _ _).1
      (hI sigma.toMul.property)) beta
        (IntermediateField.subset_adjoin K {beta} (Set.mem_singleton beta))

end ClassFieldTower.Martinet.Shafarevich
