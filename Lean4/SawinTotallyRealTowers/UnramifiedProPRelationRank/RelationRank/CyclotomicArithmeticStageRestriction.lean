/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.CyclotomicArithmeticStageMapped

set_option autoImplicit false
/-!
# Restriction from the synchronized cyclotomic stage

The actual embedding of the original stage in the mapped compositum
defines restriction of automorphisms. Its evaluation law is expressed in
the same closure equivalence used to form the mapped field, supplying
the finite part of the absolute-restriction comparison diagram.

Only the original-stage algebra and its matching F-tower are introduced
locally; the cyclotomic tower is inherited from the mapped intermediate
field, and no alternative algebra on that tower is installed.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime] (hpOdd : Odd p)
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))

local notation "Cyclo" => IdealRadicalCyclotomicBase F p (Fact.out : p.Prime)
local notation "OriginalStage" => FiniteEverywhereUnramifiedProPExtension.field
  (openNormalArithmeticStage F p hpOdd U)

local instance mappedCyclotomicOriginalAlgebra
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F) :
    Algebra OriginalStage (cyclotomicArithmeticStageMappedField F p hpOdd U e) :=
  (cyclotomicArithmeticStageMappedOriginalAlgHom F p hpOdd U e).toAlgebra

local instance mappedCyclotomicOriginalTower
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F) :
    IsScalarTower F OriginalStage (cyclotomicArithmeticStageMappedField F p hpOdd U e) :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    exact ((cyclotomicArithmeticStageMappedOriginalAlgHom F p hpOdd U e).commutes x).symm)

/-- Actual restriction of automorphisms from the mapped cyclotomic stage
to the original arithmetic stage. -/
def cyclotomicArithmeticStageMappedRestriction
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F) :
    Gal(cyclotomicArithmeticStageMappedField F p hpOdd U e / Cyclo) →* Gal(OriginalStage / F) :=
  IntermediateField.restrictRestrictAlgEquivMapHom F OriginalStage Cyclo
    (cyclotomicArithmeticStageMappedField F p hpOdd U e)

/-- Restriction commutes with the actual original-stage embedding. -/
theorem cyclotomicArithmeticStageMappedRestriction_commutes
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F)
    (σ : Gal(cyclotomicArithmeticStageMappedField F p hpOdd U e / Cyclo))
    (x : OriginalStage) :
    cyclotomicArithmeticStageMappedOriginalAlgHom F p hpOdd U e
        (cyclotomicArithmeticStageMappedRestriction F p hpOdd U e σ x) =
      σ (cyclotomicArithmeticStageMappedOriginalAlgHom F p hpOdd U e x) :=
  AlgEquiv.restrictNormal_commutes (σ.restrictScalars F) OriginalStage x

/-- Pointwise compatibility of finite restriction with the synchronized
algebraic-closure equivalence. -/
theorem cyclotomicArithmeticStageMappedRestriction_apply
    (e : AlgebraicClosure Cyclo ≃ₐ[Cyclo] AlgebraicClosure F)
    (σ : Gal(cyclotomicArithmeticStageMappedField F p hpOdd U e / Cyclo))
    (x : OriginalStage) :
    e.symm (cyclotomicArithmeticStageMappedRestriction F p hpOdd U e σ x : AlgebraicClosure F) =
      (σ (cyclotomicArithmeticStageMappedOriginalAlgHom F p hpOdd U e x) : AlgebraicClosure Cyclo) :=
  congrArg Subtype.val (cyclotomicArithmeticStageMappedRestriction_commutes F p hpOdd U e σ x)

end ClassFieldTower.Martinet.Shafarevich
