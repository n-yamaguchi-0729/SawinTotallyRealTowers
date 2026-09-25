/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.CyclotomicAbsoluteH2Restriction
import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence

set_option autoImplicit false
/-!
# Absolute H² restriction along actual finite-field embeddings

The existing finite-extension identification realizes the absolute Galois
group of the top field as its open fixing subgroup in the bottom absolute
Galois group. Transporting prime-to-index restriction along this actual
continuous equivalence proves injectivity for the field-embedding map,
including the named cyclotomic extension.
-/

open CategoryTheory

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.ProP
open RamificationTheory.Field.absoluteGaloisGroup

universe u

variable (F : Type u) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- Restriction along a concrete embedded finite extension of degree prime
to `p` is injective on continuous absolute `H²` with trivial coefficients. -/
theorem finiteExtensionAbsoluteH2Restriction_injective
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L]
    (i : L →ₐ[F] AlgebraicClosure F)
    (hdegree : ¬ p ∣ Module.finrank F L) :
    Function.Injective (continuousCohomologyZModPMapLifted p
      (ofFiniteExtensionAbsoluteContinuous F i) 2).hom := by
  let : LocallyCompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (LocallyCompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  let H : OpenSubgroup (Field.absoluteGaloisGroup F) := openSubgroupOfFiniteExtension F i
  let e : Field.absoluteGaloisGroup L ≃ₜ* H.toSubgroup :=
    equivOpenSubgroupOfFiniteExtensionContinuousMulEquiv F i
  let k : H.toSubgroup →ₜ* Field.absoluteGaloisGroup L := e.symm
  let j := ofFiniteExtensionAbsoluteContinuous F i
  have hinj := continuousH2Restriction_injective_of_index_not_dvd (p := p) H
    (by
      change ¬ p ∣ (openSubgroupOfFiniteExtension F i).toSubgroup.index
      rw [openSubgroupOfFiniteExtension_index_eq_finrank]
      exact hdegree)
  have hj : j.comp k = subgroupInclusion H.toSubgroup := by
    ext sigma
    change (e (e.symm sigma) : Field.absoluteGaloisGroup F) = sigma.1
    rw [e.apply_symm_apply]
  have hmap := continuousCohomologyZModPMapLifted_comp p j k 2
  rw [hj] at hmap
  intro x y hxy
  apply hinj
  rw [hmap]
  exact congrArg (continuousCohomologyZModPMapLifted p k 2).hom hxy

local instance finiteExtensionCyclotomicFiniteDimensional :
    FiniteDimensional F (IdealRadicalCyclotomicBase F p Fact.out) :=
  finiteDimensional_idealRadicalCyclotomicBase F p Fact.out

/-- The concrete continuous map from the absolute Galois group of the
named cyclotomic field to that of the base field. -/
def cyclotomicAbsoluteGaloisInclusion :
    Field.absoluteGaloisGroup (IdealRadicalCyclotomicBase F p Fact.out) →ₜ*
      Field.absoluteGaloisGroup F :=
  ofFiniteExtensionAbsoluteContinuous F (IdealRadicalCyclotomicBase F p Fact.out).val

/-- The actual field-extension restriction, rather than only its
subgroup-valued form, detects absolute degree-two vanishing. -/
theorem cyclotomicFieldAbsoluteH2Restriction_injective :
    Function.Injective (continuousCohomologyZModPMapLifted p
      (cyclotomicAbsoluteGaloisInclusion F p) 2).hom := by
  apply finiteExtensionAbsoluteH2Restriction_injective F p
    (IdealRadicalCyclotomicBase F p Fact.out)
    (IdealRadicalCyclotomicBase F p Fact.out).val
  intro hdiv
  exact (Nat.not_le_of_gt (idealRadicalCyclotomicBase_finrank_lt F p))
    (Nat.le_of_dvd Module.finrank_pos hdiv)

end ClassFieldTower.Martinet.Shafarevich

end
