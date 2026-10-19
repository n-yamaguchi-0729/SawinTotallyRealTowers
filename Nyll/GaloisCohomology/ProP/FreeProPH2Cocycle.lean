/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.ContinuousH1Bridge
import Nyll.GaloisCohomology.Topology.TrivialDegreeTwoCocycles

/-!
# Normalized cocycles and primitives for free pro-p degree-two cohomology

The lifted trivial mod-p API reuses the coefficient-independent continuous
normalization and primitive construction.
-/

open scoped Topology
namespace ClassFieldTower.ProP
open CategoryTheory TopRep ContRepresentation
namespace FreeProPH2Cocycle

noncomputable section
universe u
variable {p : ℕ} [Fact p.Prime]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- The universe-lifted coefficient module used by the cocycle formulas. -/
abbrev A (p : ℕ) := ULift.{u} (ZMod p)

/-- The normalized inhomogeneous cocycle associated to a homogeneous
degree-two cocycle. -/
def normalizedCocycle
    (z : Cohomology.trivialZModPCocyclesLifted p F 2) (g h : F) : A p :=
  TopRep.TrivialDegreeTwoCocycles.normalizedCocycle
    (Cohomology.trivialZModPLifted p F) z g h

omit [Fact p.Prime] in
/-- The normalized lifted mod-p cocycle is continuous. -/
theorem normalizedCocycle_continuous [LocallyCompactSpace F]
    (z : Cohomology.trivialZModPCocyclesLifted p F 2) :
    Continuous fun gh : F × F => normalizedCocycle z gh.1 gh.2 :=
  TopRep.TrivialDegreeTwoCocycles.normalizedCocycle_continuous
    (Cohomology.trivialZModPLifted p F) z

omit [Fact p.Prime] in
/-- The normalized lifted mod-p cocycle satisfies the cocycle identity. -/
theorem normalizedCocycle_cocycle
    (z : Cohomology.trivialZModPCocyclesLifted p F 2) (g h k : F) :
    normalizedCocycle z g h + normalizedCocycle z (g * h) k =
      normalizedCocycle z h k + normalizedCocycle z g (h * k) :=
  TopRep.TrivialDegreeTwoCocycles.normalizedCocycle_cocycle
    (Cohomology.trivialZModPLifted p F) (fun _ _ => rfl) z g h k

omit [Fact p.Prime] in
/-- The first normalization condition for lifted mod-p cocycles. -/
theorem normalizedCocycle_one_left
    (z : Cohomology.trivialZModPCocyclesLifted p F 2) (h : F) :
    normalizedCocycle z 1 h = 0 :=
  TopRep.TrivialDegreeTwoCocycles.normalizedCocycle_one_left
    (Cohomology.trivialZModPLifted p F) z h

omit [Fact p.Prime] in
/-- The second normalization condition for lifted mod-p cocycles. -/
theorem normalizedCocycle_one_right
    (z : Cohomology.trivialZModPCocyclesLifted p F 2) (g : F) :
    normalizedCocycle z g 1 = 0 :=
  TopRep.TrivialDegreeTwoCocycles.normalizedCocycle_one_right
    (Cohomology.trivialZModPLifted p F) (fun _ _ => rfl) z g

/-- The homogeneous degree-one cochain associated to a continuous primitive
of the normalized cocycle. -/
def homogeneousPrimitive [LocallyCompactSpace F]
    (z : Cohomology.trivialZModPCocyclesLifted p F 2)
    (b : C(F, A p)) :
    (Cohomology.trivialZModPCochainsLifted p F).X 1 :=
  TopRep.TrivialDegreeTwoCocycles.homogeneousPrimitive
    (Cohomology.trivialZModPLifted p F) (fun _ _ => rfl) z b

omit [Fact p.Prime] in
/-- A normalized primitive has the prescribed actual homogeneous boundary. -/
theorem homogeneousPrimitive_boundary [LocallyCompactSpace F]
    (z : Cohomology.trivialZModPCocyclesLifted p F 2)
    (b : C(F, A p))
    (hb : ∀ g h, b (g * h) = b g + b h + normalizedCocycle z g h) :
    ((Cohomology.trivialZModPCochainsLifted p F).d 1 2).hom
        (homogeneousPrimitive z b) =
      ((Cohomology.trivialZModPCochainsLifted p F).iCycles 2).hom z :=
  TopRep.TrivialDegreeTwoCocycles.homogeneousPrimitive_boundary
    (Cohomology.trivialZModPLifted p F) (fun _ _ => rfl) z b hb

end
end FreeProPH2Cocycle
end ClassFieldTower.ProP
