/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.LocalUnramifiedH2Vanishing
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.ProfiniteIntegerFree
import ProCGroups.ProP.ContinuousH1
import ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField
import ProCGroups.Topologies.QuotientMaps

set_option autoImplicit false
open scoped Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP
open ClassFieldTower.Cohomology.ProfiniteInteger
open ClassFormation LocalClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (p : ℕ) [Fact p.Prime]

local instance localUnramifiedH1LineTopology : TopologicalSpace (ZMod p) := ⊥

local instance localUnramifiedH1LineDiscreteTopology : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _

local instance localUnramifiedH1LineModule
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) :=
  continuousH1ZModModule

private theorem continuousH1_smul_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (a : ZMod p) (chi : ContinuousH1ZMod (p := p) (G := G))
    (sigma : Additive G) :
    (a • chi) sigma = a * chi sigma := by
  let ev : ContinuousH1ZMod (p := p) (G := G) →+ ZMod p :=
    { toFun := fun psi ↦ psi sigma
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have h := ZMod.map_smul ev a chi
  change (a • chi) sigma = a • chi sigma at h
  simpa only [smul_eq_mul] using h

/-- Intrinsic local inertia, the kernel of the local residue-degree map. -/
abbrev localIntrinsicInertiaSubgroup :
    Subgroup Gal(SeparableClosure K / K) :=
  MonoidHom.ker (localResidueDegree K).toMonoidHom

/-- Restriction of additive continuous characters to intrinsic local inertia. -/
def localIntrinsicH1InertiaRestrictionAddHom :
    ContinuousH1ZMod (p := p) (G := Gal(SeparableClosure K / K)) →+
      ContinuousH1ZMod (p := p) (G := localIntrinsicInertiaSubgroup K) where
  toFun chi :=
    { toFun := fun sigma ↦ chi (Additive.ofMul sigma.1)
      map_zero' := chi.map_zero
      map_add' := fun _ _ ↦ chi.map_add _ _
      continuous_toFun := chi.continuous_toFun.comp continuous_subtype_val }
  map_zero' := by ext sigma; rfl
  map_add' := by intro chi psi; ext sigma; rfl

/-- Linear restriction of additive continuous characters to local inertia. -/
noncomputable def localIntrinsicH1InertiaRestriction :
    ContinuousH1ZMod (p := p) (G := Gal(SeparableClosure K / K)) →ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := localIntrinsicInertiaSubgroup K) :=
  (localIntrinsicH1InertiaRestrictionAddHom K p).toZModLinearMap p

/-- Intrinsic unramified local `H¹`: continuous characters trivial on inertia. -/
abbrev localIntrinsicUnramifiedH1 :
    Submodule (ZMod p)
      (ContinuousH1ZMod (p := p) (G := Gal(SeparableClosure K / K))) :=
  LinearMap.ker (localIntrinsicH1InertiaRestriction K p)

/-- The reduction modulo `p` of local residue degree, in additive `H¹` form. -/
noncomputable def localResidueDegreeModPH1 :
    ContinuousH1ZMod (p := p) (G := Gal(SeparableClosure K / K)) :=
  h1OfCharacter
    ((zHatReductionMul p (Fact.out : p.Prime).pos).comp (localResidueDegree K))

@[simp]
theorem localResidueDegreeModPH1_apply
    (sigma : Gal(SeparableClosure K / K)) :
    localResidueDegreeModPH1 K p (Additive.ofMul sigma) =
      zHatReduction p (Fact.out : p.Prime).pos
        (localResidueDegree K sigma).toAdd :=
  rfl

/-- The reduced residue-degree character is unramified. -/
theorem localResidueDegreeModPH1_mem_unramified :
    localResidueDegreeModPH1 K p ∈ localIntrinsicUnramifiedH1 K p := by
  rw [LinearMap.mem_ker]
  apply ContinuousAddMonoidHom.ext
  intro sigma
  change zHatReduction p (Fact.out : p.Prime).pos
      (localResidueDegree K sigma.1).toAdd = 0
  rw [show localResidueDegree K sigma.1 = 1 from sigma.property]
  rfl

/-- The reduced residue-degree character spans the intrinsic unramified line. -/
noncomputable def localResidueDegreeModPH1Line :
    ZMod p →ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := Gal(SeparableClosure K / K)) where
  toFun a := a • localResidueDegreeModPH1 K p
  map_add' a b := by rw [add_smul]
  map_smul' a b := by simp [smul_smul]

private noncomputable def scaledZHatReductionCharacter (a : ZMod p) :
    ZHatMul →ₜ* Multiplicative (ZMod p) where
  toFun z := Multiplicative.ofAdd
    (a * zHatReduction p (Fact.out : p.Prime).pos z.toAdd)
  map_one' := by
    apply Multiplicative.ext
    simp
  map_mul' x y := by
    apply Multiplicative.ext
    simp [mul_add]
  continuous_toFun := by
    let scale : Multiplicative (ZMod p) → Multiplicative (ZMod p) :=
      fun x ↦ Multiplicative.ofAdd (a * x.toAdd)
    have hscale : Continuous scale := continuous_of_discreteTopology
    exact hscale.comp
      (zHatReductionMul p (Fact.out : p.Prime).pos).continuous_toFun

private theorem continuousCharacter_zHat_eq_scaledReduction
    (f : ZHatMul →ₜ* Multiplicative (ZMod p)) :
    f = scaledZHatReductionCharacter p (f generator).toAdd := by
  apply ContinuousMonoidHom.toMonoidHom_injective
  apply MonoidHom.ext
  intro z
  have hEqFun :
      (fun x : ZHatMul ↦ f x) =
        fun x : ZHatMul ↦
          scaledZHatReductionCharacter p (f generator).toAdd x := by
    apply DenseRange.equalizer
      (f := integersMap) denseRange_integersMap
    · exact f.continuous_toFun
    · exact (scaledZHatReductionCharacter p (f generator).toAdd).continuous_toFun
    · funext m
      cases m
      rename_i n
      change f (integersMap (Multiplicative.ofAdd n)) =
        scaledZHatReductionCharacter p (f generator).toAdd
          (integersMap (Multiplicative.ofAdd n))
      rw [integersMap_apply, map_zpow, map_zpow]
      congr 1
      change f generator = Multiplicative.ofAdd
        ((f generator).toAdd *
          zHatReduction p (Fact.out : p.Prime).pos (1 : ZHat))
      apply Multiplicative.ext
      simp
  exact congrFun hEqFun z

/-- Every intrinsic unramified local character is a scalar multiple of
reduced residue degree. -/
theorem localIntrinsicUnramifiedH1_eq_smul
    (chi : ContinuousH1ZMod (p := p) (G := Gal(SeparableClosure K / K)))
    (hchi : chi ∈ localIntrinsicUnramifiedH1 K p) :
    ∃ a : ZMod p, chi = a • localResidueDegreeModPH1 K p := by
  let J := localIntrinsicInertiaSubgroup K
  let f : Gal(SeparableClosure K / K) →ₜ* Multiplicative (ZMod p) :=
    characterOfH1 chi
  have hJ : J ≤ f.toMonoidHom.ker := by
    intro sigma hsigma
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    change chi (Additive.ofMul sigma) = 0
    rw [LinearMap.mem_ker] at hchi
    have hv := DFunLike.congr_fun hchi (Additive.ofMul ⟨sigma, hsigma⟩)
    exact hv
  let fbar : (Gal(SeparableClosure K / K) ⧸ J) →ₜ* Multiplicative (ZMod p) :=
    ProCGroups.QuotientGroup.liftₜ J f hJ
  let e := localUnramifiedQuotientContinuousMulEquiv K
  let einv : ZHatMul →ₜ* (Gal(SeparableClosure K / K) ⧸ J) :=
    { toMonoidHom := e.symm.toMulEquiv.toMonoidHom
      continuous_toFun := e.symm.continuous }
  let g : ZHatMul →ₜ* Multiplicative (ZMod p) :=
    fbar.comp einv
  refine ⟨(g generator).toAdd, ?_⟩
  apply ContinuousAddMonoidHom.ext
  intro sigma
  rw [continuousH1_smul_apply]
  apply Multiplicative.ofAdd.injective
  change f sigma.toMul = Multiplicative.ofAdd
    ((g generator).toAdd *
      zHatReduction p (Fact.out : p.Prime).pos
        (localResidueDegree K sigma.toMul).toAdd)
  have hg := continuousCharacter_zHat_eq_scaledReduction p g
  have hgeval := DFunLike.congr_fun hg (localResidueDegree K sigma.toMul)
  calc
    f sigma.toMul = g (localResidueDegree K sigma.toMul) := by
      change f sigma.toMul =
        fbar (e.symm (localResidueDegree K sigma.toMul))
      rw [show e.symm (localResidueDegree K sigma.toMul) =
          QuotientGroup.mk' J sigma.toMul by
        apply e.injective
        rw [e.apply_symm_apply]
        rfl]
      rfl
    _ = scaledZHatReductionCharacter p (g generator).toAdd
        (localResidueDegree K sigma.toMul) := hgeval
    _ = _ := rfl

/-- The intrinsic unramified local `H¹` submodule is exactly the residue-degree line. -/
theorem localResidueDegreeModPH1Line_range :
    LinearMap.range (localResidueDegreeModPH1Line K p) =
      localIntrinsicUnramifiedH1 K p := by
  apply le_antisymm
  · rintro chi ⟨a, rfl⟩
    exact (localIntrinsicUnramifiedH1 K p).smul_mem a
      (localResidueDegreeModPH1_mem_unramified K p)
  · intro chi hchi
    obtain ⟨a, rfl⟩ := localIntrinsicUnramifiedH1_eq_smul K p chi hchi
    exact ⟨a, rfl⟩

/-- The reduced residue-degree parametrization is injective. -/
theorem localResidueDegreeModPH1Line_injective :
    Function.Injective (localResidueDegreeModPH1Line K p) := by
  intro a b hab
  obtain ⟨sigma, hsigma⟩ := localResidueDegree_surjective K generator
  have h := DFunLike.congr_fun hab (Additive.ofMul sigma)
  change (a • localResidueDegreeModPH1 K p) (Additive.ofMul sigma) =
    (b • localResidueDegreeModPH1 K p) (Additive.ofMul sigma) at h
  rw [continuousH1_smul_apply, continuousH1_smul_apply] at h
  rw [localResidueDegreeModPH1_apply] at h
  rw [hsigma] at h
  simpa using h

end ClassFieldTower.Martinet.Shafarevich
