/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealRadicalCyclotomicBase
import GaloisCohomology.ProP.H2PrimeToIndexRestriction
import ClassFieldTheory.KummerTheory.Concrete.CyclotomicPrimeBaseChange
import Mathlib.FieldTheory.AbsoluteGaloisGroup

set_option autoImplicit false
/-!
# Detecting absolute H² after adjoining the p-th roots of unity

The named cyclotomic base has degree strictly below `p`. Its fixing
subgroup in the absolute Galois group is therefore open of index prime to
`p`, and continuous degree-two restriction is injective by the proved
transfer argument. This applies to the absolute Galois group, not to an
open subgroup of the maximal unramified pro-p quotient.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

variable (F : Type*) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance cyclotomicAbsoluteFiniteDimensional :
    FiniteDimensional F (IdealRadicalCyclotomicBase F p Fact.out) :=
  finiteDimensional_idealRadicalCyclotomicBase F p Fact.out

/-- The concrete named cyclotomic base has degree strictly less than `p`. -/
theorem idealRadicalCyclotomicBase_finrank_lt :
    Module.finrank F (IdealRadicalCyclotomicBase F p Fact.out) < p := by
  let C := IdealRadicalCyclotomicBase F p Fact.out
  let : IsCyclotomicExtension {p} F C :=
    (idealRadicalPrimitiveRoot_isPrimitiveRoot F p Fact.out).intermediateField_adjoin_isCyclotomicExtension
      (K := F)
  let e : C ≃ₐ[F] CyclotomicField p F := IsCyclotomicExtension.algEquiv {p} F C _
  exact e.toLinearEquiv.finrank_eq ▸
    KummerTheory.primeCyclotomicBase_finrank_lt (K := F) p Fact.out

/-- The actual absolute-Galois subgroup fixing the named cyclotomic base. -/
def idealRadicalCyclotomicOpenSubgroup : OpenSubgroup (Field.absoluteGaloisGroup F) where
  toSubgroup := (IdealRadicalCyclotomicBase F p Fact.out).fixingSubgroup
  isOpen' := (IdealRadicalCyclotomicBase F p Fact.out).fixingSubgroup_isOpen

/-- The index of the fixing subgroup is the actual cyclotomic field degree. -/
theorem idealRadicalCyclotomicOpenSubgroup_index :
    (idealRadicalCyclotomicOpenSubgroup F p).toSubgroup.index =
      Module.finrank F (IdealRadicalCyclotomicBase F p Fact.out) :=
  (IntermediateField.finrank_eq_fixingSubgroup_index
    (F := F) (AlgebraicClosure F)
    (IdealRadicalCyclotomicBase F p Fact.out)).symm

/-- The cyclotomic fixing subgroup has index prime to `p`. -/
theorem idealRadicalCyclotomicOpenSubgroup_index_not_dvd :
    ¬ p ∣ (idealRadicalCyclotomicOpenSubgroup F p).toSubgroup.index := by
  rw [idealRadicalCyclotomicOpenSubgroup_index]
  intro hdiv
  exact (Nat.not_le_of_gt (idealRadicalCyclotomicBase_finrank_lt F p))
    (Nat.le_of_dvd Module.finrank_pos hdiv)

/-- Restriction of absolute trivial-coefficient `H²` to the cyclotomic
fixing subgroup is injective. Thus an actual primitive after cyclotomic
base change detects vanishing of the original absolute class. -/
theorem cyclotomicAbsoluteH2Restriction_injective :
    Function.Injective (ClassFieldTower.Cohomology.continuousCohomologyZModPMapLifted p
      (ClassFieldTower.Cohomology.subgroupInclusion
        (idealRadicalCyclotomicOpenSubgroup F p).toSubgroup) 2).hom := by
  let : LocallyCompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (LocallyCompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  exact ClassFieldTower.ProP.continuousH2Restriction_injective_of_index_not_dvd
    (idealRadicalCyclotomicOpenSubgroup F p)
    (idealRadicalCyclotomicOpenSubgroup_index_not_dvd F p)

end ClassFieldTower.Martinet.Shafarevich

end
