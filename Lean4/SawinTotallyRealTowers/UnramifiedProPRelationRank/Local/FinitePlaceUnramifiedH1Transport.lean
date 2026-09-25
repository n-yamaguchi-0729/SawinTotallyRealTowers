/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.LocalIntrinsicUnramifiedH1Line
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceInertiaTransport

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped NNReal NumberField ValuativeRel

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP
open LocalClassFieldTheory

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance finitePlaceUnramifiedH1TransportTopology :
    TopologicalSpace (ZMod p) := ⊥

local instance finitePlaceUnramifiedH1TransportDiscreteTopology :
    DiscreteTopology (ZMod p) := discreteTopology_bot _

local instance finitePlaceUnramifiedH1TransportModule
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) :=
  continuousH1ZModModule

private def continuousH1PullbackAddHom
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) :
    ContinuousH1ZMod (p := p) (G := H) →+
      ContinuousH1ZMod (p := p) (G := G) where
  toFun chi :=
    { toFun := fun sigma ↦ chi (Additive.ofMul (e sigma.toMul))
      map_zero' := by
        change chi (Additive.ofMul (e 1)) = 0
        rw [map_one]
        exact chi.map_zero
      map_add' := fun sigma tau ↦ by
        change chi (Additive.ofMul (e (sigma.toMul * tau.toMul))) =
          chi (Additive.ofMul (e sigma.toMul)) +
            chi (Additive.ofMul (e tau.toMul))
        rw [map_mul]
        exact chi.map_add _ _
      continuous_toFun := chi.continuous_toFun.comp e.continuous }
  map_zero' := by ext sigma; rfl
  map_add' := by intro chi psi; ext sigma; rfl

/-- Transport from the chosen global finite-place decomposition group to the
intrinsic separable-closure absolute Galois group of the completion. -/
noncomputable def finitePlaceDecompositionH1LinearEquivLocalSeparable
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ContinuousH1ZMod
        (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) ≃ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p)
        (G := Gal(SeparableClosure
          (NumberField.HeightOneSpectrum.adicAbv F v).Completion /
          (NumberField.HeightOneSpectrum.adicAbv F v).Completion)) := by
  let e :=
    finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup F v
  let f := (continuousH1PullbackAddHom (p := p) e.symm).toZModLinearMap p
  refine LinearEquiv.ofBijective f ?_
  constructor
  · intro chi psi h
    apply ContinuousAddMonoidHom.ext
    intro sigma
    have hv := DFunLike.congr_fun h (Additive.ofMul (e sigma.toMul))
    change chi (Additive.ofMul (e.symm (e sigma.toMul))) =
      psi (Additive.ofMul (e.symm (e sigma.toMul))) at hv
    simpa only [e.symm_apply_apply, ofMul_toMul] using hv
  · intro psi
    let chi : ContinuousH1ZMod
        (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) :=
      continuousH1PullbackAddHom (p := p) e psi
    refine ⟨chi, ?_⟩
    apply ContinuousAddMonoidHom.ext
    intro sigma
    exact congrArg psi (Additive.ext (e.apply_symm_apply sigma.toMul))

@[simp]
theorem finitePlaceDecompositionH1LinearEquivLocalSeparable_apply
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : ContinuousH1ZMod
      (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v))
    (sigma : Gal(SeparableClosure
      (NumberField.HeightOneSpectrum.adicAbv F v).Completion /
      (NumberField.HeightOneSpectrum.adicAbv F v).Completion)) :
    finitePlaceDecompositionH1LinearEquivLocalSeparable F p v chi
        (Additive.ofMul sigma) =
      chi (Additive.ofMul
        ((finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
          F v).symm sigma)) :=
  rfl

/-- Under the local--global Galois comparison, inertia-trivial characters
are exactly the intrinsic residue-degree unramified line. -/
theorem finitePlaceDecompositionH1LinearEquivLocalSeparable_mem_unramified_iff
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : ContinuousH1ZMod
      (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v)) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
    letI : Valued vF.Completion NNReal :=
      finitePlaceCompletionValued vF hvFna
    letI : ValuativeRel vF.Completion :=
      finitePlaceCompletionValuativeRel vF hvFna
    letI : IsNonarchimedeanLocalField vF.Completion :=
      finitePlaceNormCompletionIsNonarchimedeanLocalField F v
    finitePlaceDecompositionH1LinearEquivLocalSeparable F p v chi ∈
        localIntrinsicUnramifiedH1 vF.Completion p ↔
      chi ∈ finitePlaceUnramifiedH1 F p v := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  let _ : Valued vF.Completion NNReal :=
    finitePlaceCompletionValued vF hvFna
  let _ : ValuativeRel vF.Completion :=
    finitePlaceCompletionValuativeRel vF hvFna
  let _ : IsNonarchimedeanLocalField vF.Completion :=
    finitePlaceNormCompletionIsNonarchimedeanLocalField F v
  let e :=
    finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup F v
  let I := finitePlaceAbsoluteInertiaSubgroup F v
  let J := localIntrinsicInertiaSubgroup vF.Completion
  have hmap : Subgroup.map e.toMonoidHom I = J :=
    finitePlaceAbsoluteInertia_map_eq_localResidueDegree_ker F v
  change
    (localIntrinsicH1InertiaRestriction vF.Completion p)
        (finitePlaceDecompositionH1LinearEquivLocalSeparable F p v chi) = 0 ↔
      (finitePlaceH1InertiaRestriction F p v) chi = 0
  constructor
  · intro hlocal
    apply ContinuousAddMonoidHom.ext
    intro sigma
    let sigmaI : I := sigma.toMul
    have hmem : e sigmaI.1 ∈ J := by
      rw [← hmap]
      exact ⟨sigmaI.1, sigmaI.property, rfl⟩
    have hv := DFunLike.congr_fun hlocal
      (Additive.ofMul (⟨e sigmaI.1, hmem⟩ : J))
    change chi (Additive.ofMul (e.symm (e sigmaI.1))) = 0 at hv
    change chi (Additive.ofMul sigmaI.1) = 0
    simpa only [e.symm_apply_apply] using hv
  · intro hglobal
    apply ContinuousAddMonoidHom.ext
    intro tau
    have hmemMap : tau.toMul.1 ∈ Subgroup.map e.toMonoidHom I := by
      rw [hmap]
      exact tau.toMul.property
    obtain ⟨sigma, hsigma, heq⟩ := hmemMap
    let sigmaI : I := ⟨sigma, hsigma⟩
    have hv := DFunLike.congr_fun hglobal (Additive.ofMul sigmaI)
    have heq' : e.symm tau.toMul.1 = sigma := by
      rw [← heq]
      exact e.symm_apply_apply sigma
    change chi (Additive.ofMul sigmaI.1) = 0 at hv
    change chi (Additive.ofMul (e.symm tau.toMul.1)) = 0
    rw [heq']
    exact hv

end ClassFieldTower.Martinet.Shafarevich
