/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.SetTheory.Cardinal.Finite
import Nyll.GaloisCohomology.Cyclic.TateH0.Invariants
import Nyll.GaloisCohomology.Cyclic.TateH0.NormImage
import Nyll.GaloisCohomology.Cyclic.TateH0.Main

/-! Provides the public declarations in the `CyclicCohomology.Herbrand.LowDegree` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

/-- Degree-zero Tate cohomology of field units is equipotent to the norm quotient. -/
theorem herbrand_tateCohomology_zero_units_cardinal_eq_normQuotient (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Cardinal.mk (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) =
      Cardinal.mk (Additive (NormQuotient K L)) :=
  Cardinal.mk_congr
    (H0TateUnitsIsoNormQuotient K L).toLinearEquiv.toEquiv

end
end CyclicCohomology
