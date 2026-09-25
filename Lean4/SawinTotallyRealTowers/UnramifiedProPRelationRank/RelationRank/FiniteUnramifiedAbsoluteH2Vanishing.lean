/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.EverywhereUnramifiedProPCompositum
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.UnramifiedKummerFieldUnitsH2
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerAbsoluteLift
import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion

set_option autoImplicit false
/-!
# Absolute H² vanishing from any embedded unramified p-extension

The supported-idele primitive and the Hilbert-90 correction apply to an
actual finite everywhere-unramified p-extension, independently of how it
was obtained as a finite stage. This form also applies to the mapped
cyclotomic base change. No primitive or comparison assumption is added.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet ClassFieldTower.ProP

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime]
variable (E : FiniteEverywhereUnramifiedProPExtension F (n : ℕ))

/-- The same embedded field, retaining its finite Galois certificates. -/
def finiteUnramifiedExtensionFiniteGaloisField :
    FiniteGaloisIntermediateField F (AlgebraicClosure F) where
  toIntermediateField := E.field
  finiteDimensional := E.finiteDimensional
  isGalois := E.isGalois

/-- Actual absolute restriction to the embedded unramified extension. -/
def finiteUnramifiedExtensionAbsoluteRestriction :
    Field.absoluteGaloisGroup F →ₜ* Gal(E.field/F) :=
  absoluteFiniteGaloisRestriction F (finiteUnramifiedExtensionFiniteGaloisField F n E)

/-- Every degree-two class from this unramified p-extension becomes zero
on the absolute Galois group of a base containing a primitive p-th root. -/
theorem finiteUnramifiedExtension_absoluteH2Map_eq_zero
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (x : Cohomology.continuousCohomologyZModPLifted (n : ℕ) Gal(E.field/F) 2) :
    (Cohomology.continuousCohomologyZModPMapLifted (n : ℕ)
      (finiteUnramifiedExtensionAbsoluteRestriction F n E) 2).hom x = 0 := by
  let : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F/F))
  let D := finiteUnramifiedExtensionFiniteGaloisField F n E
  let z := degreeTwoCocycleRepresentative x
  let c := normalizedFiniteKummerTwoCocycle F n D z
  obtain ⟨b, hb⟩ := unramifiedFiniteKummerTwoCocycle_isFieldUnitsCoboundary
    F E.field n hmu E.isPGroup
    (fun _ => by
      apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      exact E.everywhereUnramified.finitePlaces _)
    (fun v => E.everywhereUnramified.infinitePlaces.1
      (chosenInfinitePlaceAbove (L := E.field) v)) c
  obtain ⟨s, hs⟩ := exists_absoluteLift_of_finiteKummerTwoCocycle_boundary F n D hmu z b hb
  rw [← degreeTwoCocycleRepresentative_π x]
  exact H2CocycleExtension.restriction_eq_zero_of_lift
    (finiteUnramifiedExtensionAbsoluteRestriction F n E) z s hs

end ClassFieldTower.Martinet.Shafarevich
