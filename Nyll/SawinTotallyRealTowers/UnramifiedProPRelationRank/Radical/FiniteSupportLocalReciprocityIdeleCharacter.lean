/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.Instances.ZMod
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalReciprocityCharacterPairing
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceCyclotomicMuPKummerComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology

/-!
# Idele characters from finitely many local reciprocity characters

A finite family of continuous local mod-`p` characters evaluates on actual
idele coordinates.  The finite product is continuous, and its value on a
principal idele is the sum of the localized power-class pairings.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField Topology BigOperators

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

attribute [local instance]
  ClassFieldTower.Martinet.Shafarevich.finitePlaceAdicCompletionValuativeRel
attribute [local instance]
  ClassFieldTower.Martinet.Shafarevich.finitePlaceAdicCompletionIsNonarchimedeanLocalField
attribute [local instance] ClassFieldTower.ProP.continuousH1ZModModule

variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (chi : ∀ v : ↥S, ContinuousH1ZMod (p := p)
  (G := Field.absoluteGaloisGroup (v.1.adicCompletion F)))

/-- The continuous finite product of local reciprocity characters on
the actual finite coordinates of an idele. -/
noncomputable def finiteSupportLocalReciprocityIdeleCharacter :
    IdeleGroup F →ₜ* Multiplicative (ZMod p) where
  toFun x := ∏ v : ↥S, localReciprocityUnitCharacter (v.1.adicCompletion F) p (chi v)
    (IdeleGroup.finiteComponent v.1 x)
  map_one' := by simp only [map_one, Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]
  continuous_toFun := continuous_finsetProd Finset.univ fun v _ ↦
    (localReciprocityUnitCharacter (v.1.adicCompletion F) p (chi v)).continuous_toFun.comp
      (IdeleGroup.finiteComponentContinuous v.1).continuous_toFun

@[simp]
theorem finiteSupportLocalReciprocityIdeleCharacter_apply (x : IdeleGroup F) :
    finiteSupportLocalReciprocityIdeleCharacter F p S chi x =
      ∏ v : ↥S, localReciprocityUnitCharacter (v.1.adicCompletion F) p (chi v)
        (IdeleGroup.finiteComponent v.1 x) := rfl

/-- The corresponding functional on global power classes is the finite
sum of local reciprocity pairings after localization. -/
noncomputable def finiteSupportLocalReciprocityPowerClassFunctional :
    Module.Dual (ZMod p) (absolutePowerClassModP F p) :=
  ∑ v : ↥S, (localReciprocityH1PowerClassPairing (v.1.adicCompletion F) p (chi v)).comp
    (finitePlacePowerClassLocalization F p v.1)

@[simp]
theorem finiteSupportLocalReciprocityPowerClassFunctional_apply
    (x : absolutePowerClassModP F p) :
    finiteSupportLocalReciprocityPowerClassFunctional F p S chi x =
      ∑ v : ↥S, localReciprocityH1PowerClassPairing (v.1.adicCompletion F) p (chi v)
        (finitePlacePowerClassLocalization F p v.1 x) := by
  simp only [finiteSupportLocalReciprocityPowerClassFunctional, LinearMap.sum_apply,
    LinearMap.comp_apply]

/-- Principal idele evaluation is the finite sum of actual localized
power-class pairings.  No coefficient-root hypothesis is used. -/
theorem finiteSupportLocalReciprocityIdeleCharacter_principal
    (a : Fˣ) :
    (finiteSupportLocalReciprocityIdeleCharacter F p S chi
      (IdeleGroup.principalIdele F a)).toAdd =
      ∑ v : ↥S, localReciprocityH1PowerClassPairing (v.1.adicCompletion F) p (chi v)
        (finitePlacePowerClassLocalization F p v.1
          (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : Fˣ →* Fˣ).range a))) := by
  rw [finiteSupportLocalReciprocityIdeleCharacter_apply, toAdd_prod]
  apply Finset.sum_congr rfl
  intro v _
  rw [finitePlacePowerClassLocalization_mk]
  have hcoord : IdeleGroup.finiteComponent v.1 (IdeleGroup.principalIdele F a) =
      Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom a := by
    apply Units.ext
    rfl
  rw [hcoord]
  rfl

/-- The principal evaluation formula as one global power-class functional. -/
theorem finiteSupportLocalReciprocityIdeleCharacter_principal_functional
    (a : Fˣ) :
    (finiteSupportLocalReciprocityIdeleCharacter F p S chi
      (IdeleGroup.principalIdele F a)).toAdd =
      finiteSupportLocalReciprocityPowerClassFunctional F p S chi
        (Additive.ofMul (QuotientGroup.mk' (powMonoidHom p : Fˣ →* Fˣ).range a)) := by
  let qa : absolutePowerClassModP F p :=
    Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom p : Fˣ →* Fˣ).range a)
  change
    (finiteSupportLocalReciprocityIdeleCharacter F p S chi
      (IdeleGroup.principalIdele F a)).toAdd =
      finiteSupportLocalReciprocityPowerClassFunctional F p S chi qa
  rw [finiteSupportLocalReciprocityPowerClassFunctional_apply]
  exact finiteSupportLocalReciprocityIdeleCharacter_principal F p S chi a

/-- A supporting finite-place embedding recovers its prescribed local
reciprocity character. -/
theorem finiteSupportLocalReciprocityIdeleCharacter_finitePlace_mem
    (v : ↥S) (a : (v.1.adicCompletion F)ˣ) :
    finiteSupportLocalReciprocityIdeleCharacter F p S chi (IdeleGroup.finitePlaceIdele v.1 a) =
      localReciprocityUnitCharacter (v.1.adicCompletion F) p (chi v) a := by
  rw [finiteSupportLocalReciprocityIdeleCharacter_apply, Finset.prod_eq_single v]
  · rw [IdeleGroup.finitePlaceIdele_finiteComponent_same]
  · intro w _ hw
    rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v.1 w.1 a
      (fun h ↦ hw (Subtype.ext h)), map_one]
  · intro hv
    exact (hv (Finset.mem_univ v)).elim

/-- Outside the finite support, every finite-place idele has value one. -/
theorem finiteSupportLocalReciprocityIdeleCharacter_finitePlace_notMem
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) (a : (v.adicCompletion F)ˣ) :
    finiteSupportLocalReciprocityIdeleCharacter F p S chi (IdeleGroup.finitePlaceIdele v a) =
      1 := by
  rw [finiteSupportLocalReciprocityIdeleCharacter_apply]
  apply Finset.prod_eq_one
  intro w _
  have hw : w.1 ≠ v := by
    intro h
    exact hv (h ▸ w.property)
  rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w.1 a hw, map_one]

open scoped Classical in
/-- Evaluation at an arbitrary finite-place embedding, with its actual
support test. -/
theorem finiteSupportLocalReciprocityIdeleCharacter_finitePlace
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    finiteSupportLocalReciprocityIdeleCharacter F p S chi (IdeleGroup.finitePlaceIdele v a) =
      if hv : v ∈ S then localReciprocityUnitCharacter (v.adicCompletion F) p (chi ⟨v, hv⟩) a
      else 1 := by
  classical
  split
  · rename_i hv
    let w : (↥S) := ⟨v, hv⟩
    rw [finiteSupportLocalReciprocityIdeleCharacter_apply, Finset.prod_eq_single w]
    · rw [IdeleGroup.finitePlaceIdele_finiteComponent_same]
    · intro t _ ht
      rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v t.1 a
        (fun h ↦ ht (Subtype.ext h)), map_one]
    · intro hw
      exact (hw (Finset.mem_univ w)).elim
  · rename_i hv
    exact finiteSupportLocalReciprocityIdeleCharacter_finitePlace_notMem F p S chi v hv a

/-- Every archimedean-place embedding is killed by a family supported at
finite places. -/
theorem finiteSupportLocalReciprocityIdeleCharacter_infinitePlace
    (v : InfinitePlace F) (a : v.Completionˣ) :
    finiteSupportLocalReciprocityIdeleCharacter F p S chi (IdeleGroup.infinitePlaceIdele v a) =
      1 := by
  rw [finiteSupportLocalReciprocityIdeleCharacter_apply]
  apply Finset.prod_eq_one
  intro w _
  rw [IdeleGroup.infinitePlaceIdele_finiteComponent, map_one]

end ClassFieldTower.Martinet.Shafarevich
