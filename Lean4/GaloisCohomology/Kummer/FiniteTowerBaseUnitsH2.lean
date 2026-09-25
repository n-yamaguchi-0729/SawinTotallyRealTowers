/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.FiniteCyclicBaseUnitsH2
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

set_option autoImplicit false

/-!
# Base-unit coefficients along a field tower

The inclusions Kˣ → Lˣ → Nˣ give an actual equivariant coefficient map
for Gal(N/L), starting with the trivial action on Kˣ.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K L N : Type) [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra L N]

/-- Inclusion of base units along the two given algebra maps. -/
def finiteTowerBaseUnitsRepHom :
    Rep.trivial ℤ Gal(N/L) (Additive Kˣ) ⟶ Rep.ofAlgebraAutOnUnits L N :=
  (Rep.trivialFunctor ℤ Gal(N/L)).map
    (ModuleCat.ofHom
      (Units.map (algebraMap K L).toMonoidHom).toAdditive.toIntLinearMap) ≫
    finiteGaloisBaseUnitsRepHom L N

/-- The induced degree-two coefficient map for the actual field tower. -/
def finiteTowerBaseUnitsH2Map :
    groupCohomology (Rep.trivial ℤ Gal(N/L) (Additive Kˣ)) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits L N) 2 :=
  groupCohomology.map (MonoidHom.id Gal(N/L)) (finiteTowerBaseUnitsRepHom K L N) 2

end
end ClassFieldTower.Cohomology
