/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.CyclotomicArithmeticStage

set_option autoImplicit false
/-!
# The cyclotomic stage in a synchronized algebraic closure

Mapping the actual compositum along a supplied algebraic-closure
equivalence gives a finite everywhere-unramified p-extension in the
cyclotomic base's standard algebraic closure. The equivalence is the
concrete closure comparison used by absolute-Galois restriction; no
new choice of closure comparison is made here.

The mapped field is named separately from its arithmetic bundle so that
the coefficient and embedding interfaces do not unfold the bundle's
finite-dimensionality and unramifiedness proofs during type synthesis.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime] (hpOdd : Odd p)
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))

local notation "Cyclo" => IdealRadicalCyclotomicBase F p (Fact.out : p.Prime)
local notation "TopStage" => cyclotomicArithmeticStageField F p hpOdd U
local notation "OriginalStage" => FiniteEverywhereUnramifiedProPExtension.field
  (openNormalArithmeticStage F p hpOdd U)

local instance mappedCyclotomicBaseFinite : FiniteDimensional F Cyclo :=
  finiteDimensional_idealRadicalCyclotomicBase F p Fact.out

local instance mappedCyclotomicBaseNumber : NumberField Cyclo :=
  NumberField.of_module_finite F Cyclo

local instance mappedCyclotomicSourceFinite : FiniteDimensional Cyclo TopStage :=
  cyclotomicArithmeticStage_finiteDimensional F p hpOdd U

local instance mappedCyclotomicSourceNumber : NumberField TopStage :=
  cyclotomicArithmeticStage_numberField F p hpOdd U

local instance mappedCyclotomicSourceGalois : IsGalois Cyclo TopStage :=
  cyclotomicArithmeticStage_isGalois F p hpOdd U

/-- The actual image of the compositum in the synchronized closure. -/
def cyclotomicArithmeticStageMappedField
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F) :
    IntermediateField Cyclo (AlgebraicClosure Cyclo) :=
  (TopStage).map e.symm.toAlgHom

/-- The compositum is equivalent to its actual image over the cyclotomic base. -/
def cyclotomicArithmeticStageMappedEquiv
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F) :
    TopStage ≃ₐ[Cyclo] cyclotomicArithmeticStageMappedField F p hpOdd U e :=
  IntermediateField.equivMap TopStage e.symm.toAlgHom

/-- All finite, Galois, p-group, and unramified certificates transported
to the actual mapped field inside the standard algebraic closure. -/
def cyclotomicArithmeticStageMappedExtension
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F) :
    FiniteEverywhereUnramifiedProPExtension Cyclo p := by
  let T := cyclotomicArithmeticStageMappedField F p hpOdd U e
  let i := cyclotomicArithmeticStageMappedEquiv F p hpOdd U e
  letI hfinite : FiniteDimensional Cyclo T := i.toLinearEquiv.finiteDimensional
  letI hnumber : NumberField T := NumberField.of_module_finite Cyclo T
  exact
    { field := T
      finiteDimensional := hfinite
      isGalois := IsGalois.of_algEquiv i
      numberField := hnumber
      isPGroup := (cyclotomicArithmeticStage_isPGroup F p hpOdd U).of_equiv (AlgEquiv.autCongr i)
      everywhereUnramified := everywhereUnramified_congrTop i
        (cyclotomicArithmeticStage_everywhereUnramified F p hpOdd U) }

@[simp] theorem cyclotomicArithmeticStageMappedExtension_field
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F) :
    (cyclotomicArithmeticStageMappedExtension F p hpOdd U e).field =
      cyclotomicArithmeticStageMappedField F p hpOdd U e := rfl

@[simp] theorem cyclotomicArithmeticStageMappedEquiv_apply
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F) (x : TopStage) :
    ((cyclotomicArithmeticStageMappedEquiv F p hpOdd U e x :
      cyclotomicArithmeticStageMappedField F p hpOdd U e) : AlgebraicClosure Cyclo) =
        e.symm x := rfl

/-- The original arithmetic stage embeds into the mapped compositum. -/
def cyclotomicArithmeticStageMappedOriginalAlgHom
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F) :
    OriginalStage →ₐ[F] cyclotomicArithmeticStageMappedField F p hpOdd U e :=
  ((cyclotomicArithmeticStageMappedEquiv F p hpOdd U e).toAlgHom.restrictScalars F).comp
    (cyclotomicArithmeticStageOriginalAlgHom F p hpOdd U)

@[simp] theorem cyclotomicArithmeticStageMappedOriginalAlgHom_apply
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F) (x : OriginalStage) :
    ((cyclotomicArithmeticStageMappedOriginalAlgHom F p hpOdd U e x :
      cyclotomicArithmeticStageMappedField F p hpOdd U e) : AlgebraicClosure Cyclo) =
        e.symm (x : AlgebraicClosure F) := rfl

end ClassFieldTower.Martinet.Shafarevich
