/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerAbsoluteLift
import GaloisCohomology.Kummer.FiniteKummerCoefficientH2
import GaloisCohomology.ProP.H2CocycleExtensionPullback
import GaloisCohomology.ProP.TrivialZModP
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Rep.Basic

set_option autoImplicit false

/-!
# Finite Kummer zero classes vanish after absolute inflation

A vanishing finite field-unit class gives an actual field-unit primitive.
The existing Hilbert-90 correction then gives a continuous lift of the
normalized central extension over the absolute Galois group. Thus its
inflated mod-p class is zero. The finite coefficient map is not asserted
to be injective. This is the representative-level kernel comparison and
uses neither a local-field nor an unramified-extension assumption.
-/

namespace ClassFieldTower.Sawin

open CategoryTheory ClassFieldTower.Cohomology ClassFieldTower.ProP
open ClassFieldTower.Martinet.Shafarevich

/-- A finite Kummer coefficient class in the kernel maps to zero under
actual absolute inflation of the original lifted class. -/
theorem absoluteInflation_eq_zero_of_finiteKummerH2_eq_zero
    (K : Type) [Field K] [CharZero K]
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (z : trivialZModPCocyclesLifted (p : ℕ) Gal(E/K) 2)
    (hZero : (finiteKummerCoefficientH2Map K E p hmu).hom
      (groupCohomology.H2π
        (Rep.trivial ℤ Gal(E/K) (ULift.{0} (ZMod (p : ℕ))))
        (normalizedFiniteKummerTwoCocycle K p E z)) = 0) :
    (continuousCohomologyZModPMapLifted (p : ℕ)
      (absoluteFiniteGaloisRestriction K E) 2).hom
      (ContinuousCohomology.π (trivialZModPLifted (p : ℕ) Gal(E/K)) 2 z) = 0 := by
  let c := normalizedFiniteKummerTwoCocycle K p E z
  let d := groupCohomology.mapCocycles₂ (MonoidHom.id Gal(E/K))
    (finiteKummerCoefficientRepHom K E p hmu) c
  have hBoundary : groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K E) d = 0 := by
    have hMap := congrArg (fun f ↦ f c)
      (groupCohomology.H2π_comp_map (MonoidHom.id Gal(E/K))
        (finiteKummerCoefficientRepHom K E p hmu))
    exact hMap.symm.trans hZero
  obtain ⟨b, hb⟩ := (groupCohomology.H2π_eq_zero_iff d).mp hBoundary
  obtain ⟨s, hs⟩ := exists_absoluteLift_of_finiteKummerTwoCocycle_boundary
    K p E hmu z b hb
  let : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))
  exact H2CocycleExtension.restriction_eq_zero_of_lift
    (absoluteFiniteGaloisRestriction K E) z s hs

end ClassFieldTower.Sawin
