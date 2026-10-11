/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.QuotientPadicContinuity
import Mathlib.Algebra.Module.MinimalAxioms

/-!
# P-adic scalars on the principal-unit prodiscrete limit

The compatible quotient actions define an action on the actual inverse-limit
carrier. Its module laws and joint continuity follow coordinate by coordinate,
without a finiteness assumption on the residue field.
-/

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
namespace PrincipalUnitProdiscreteLimit

universe u v

variable {K : Type u} [Field K]
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
variable (p : ℕ) [Fact p.Prime] [CharP F.residueField p]

/-- Coordinatewise scalar multiplication is a compatible family. -/
@[instance_reducible] private noncomputable def padicSMulOfResidueChar :
    SMul ℤ_[p] (PrincipalUnitProdiscreteLimit F) where
  smul a x := ⟨Additive.ofMul ⟨fun n => Additive.toMul
    (((DiscretePrincipalUnitQuotient.padicModule F p n).toSMul.smul
      a (coordinate F n x)).val), by
    intro m n hmn
    have hcompat : DiscretePrincipalUnitQuotient.transition F hmn (coordinate F n x) =
        coordinate F m x := by
      apply DiscretePrincipalUnitQuotient.ext
      exact congrArg Additive.ofMul ((Additive.toMul x.val).2 hmn)
    have h := DiscretePrincipalUnitQuotient.transition_padic_smul F p hmn a
      (coordinate F n x)
    rw [hcompat] at h
    exact congrArg
      (fun y : DiscretePrincipalUnitQuotient F m => Additive.toMul y.val) h⟩⟩

/-- The principal-unit prodiscrete limit is a p-adic module for any residue
field of characteristic `p`. The structure is explicit, not a global instance. -/
@[instance_reducible] noncomputable def padicModuleOfResidueChar :
    Module ℤ_[p] (PrincipalUnitProdiscreteLimit F) := by
  let : SMul ℤ_[p] (PrincipalUnitProdiscreteLimit F) := padicSMulOfResidueChar F p
  have hcoord (n : ℕ) (a : ℤ_[p]) (x : PrincipalUnitProdiscreteLimit F) :
      coordinate F n (a • x) =
        (DiscretePrincipalUnitQuotient.padicModule F p n).toSMul.smul
          a (coordinate F n x) := rfl
  have hext : Function.Injective
      (fun x : PrincipalUnitProdiscreteLimit F => fun n : ℕ => coordinate F n x) := by
    intro x y h
    apply (equiv F).injective
    apply Additive.toMul.injective
    apply Subtype.ext
    funext n
    exact congrArg (fun q : DiscretePrincipalUnitQuotient F n => Additive.toMul q.val)
      (congrFun h n)
  apply Module.ofMinimalAxioms
  · intro a x y
    apply hext
    funext n
    simp only [hcoord, map_add]
    exact (DiscretePrincipalUnitQuotient.padicModule F p n).smul_add a
      (coordinate F n x) (coordinate F n y)
  · intro a b x
    apply hext
    funext n
    simp only [hcoord, map_add]
    exact (DiscretePrincipalUnitQuotient.padicModule F p n).add_smul a b (coordinate F n x)
  · intro a b x
    apply hext
    funext n
    simp only [hcoord]
    exact (DiscretePrincipalUnitQuotient.padicModule F p n).mul_smul a b (coordinate F n x)
  · intro x
    apply hext
    funext n
    simp only [hcoord]
    exact (DiscretePrincipalUnitQuotient.padicModule F p n).one_smul (coordinate F n x)

/-- The constructed scalar multiplication has the specified quotient coordinates. -/
theorem coordinate_padic_smulOfResidueChar (n : ℕ) (a : ℤ_[p])
    (x : PrincipalUnitProdiscreteLimit F) :
    coordinate F n ((padicModuleOfResidueChar F p).toSMul.smul a x) =
      (DiscretePrincipalUnitQuotient.padicModule F p n).toSMul.smul
        a (coordinate F n x) := rfl

/-- The actual coordinatewise p-adic action is jointly continuous. -/
theorem padicContinuousSMulOfResidueChar :
    @ContinuousSMul ℤ_[p] (PrincipalUnitProdiscreteLimit F)
      (padicModuleOfResidueChar F p).toSMul inferInstance inferInstance := by
  let : Module ℤ_[p] (PrincipalUnitProdiscreteLimit F) := padicModuleOfResidueChar F p
  let : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun n => ⊥
  let : (n : ℕ) → DiscreteTopology (Internal.principalUnitQuotientCarrier F n) :=
    fun n => ⟨rfl⟩
  have hcoordinates : Continuous (fun x : PrincipalUnitProdiscreteLimit F =>
      (Additive.toMul x.val).val) :=
    continuous_subtype_val.comp
      (show Continuous (fun x : PrincipalUnitProdiscreteLimit F => x.val) from
        continuous_induced_dom)
  have hc (n : ℕ) : Continuous (coordinate F n) :=
    (continuous_of_discreteTopology : Continuous
      (fun q : Internal.principalUnitQuotientCarrier F n =>
        DiscretePrincipalUnitQuotient.of F n (Additive.ofMul q))).comp
      ((continuous_apply n).comp hcoordinates)
  refine ⟨?_⟩
  apply continuous_induced_rng.2
  apply continuous_induced_rng.2
  apply continuous_pi
  intro n
  change Continuous (fun z : ℤ_[p] × PrincipalUnitProdiscreteLimit F =>
    Additive.toMul (coordinate F n
      ((padicModuleOfResidueChar F p).toSMul.smul z.1 z.2)).val)
  simp_rw [coordinate_padic_smulOfResidueChar]
  have hs : Continuous (fun z : ℤ_[p] × PrincipalUnitProdiscreteLimit F =>
      (DiscretePrincipalUnitQuotient.padicModule F p n).toSMul.smul
        z.1 (coordinate F n z.2)) :=
    (DiscretePrincipalUnitQuotient.padicContinuousSMul F p n).continuous_smul.comp
      (continuous_fst.prodMk ((hc n).comp continuous_snd))
  exact (continuous_of_discreteTopology : Continuous
    (fun q : DiscretePrincipalUnitQuotient F n => Additive.toMul q.val)).comp hs

end PrincipalUnitProdiscreteLimit
end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
