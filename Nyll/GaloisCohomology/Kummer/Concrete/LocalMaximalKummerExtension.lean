/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
import Nyll.GaloisCohomology.Kummer.Concrete.MaximalKummerSubgroup
import Nyll.GaloisCohomology.Kummer.Concrete.KummerCorrespondenceFormula

/-!
# Maximal finite Kummer extensions of local fields

For a positive integer `n` that is nonzero in a nonarchimedean local field,
the Kummer extension obtained by adjoining all `n`-th roots is finite.
-/



noncomputable section

universe v

namespace KummerTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The maximal restricted radical quotient is finite when the exponent is
nonzero in the local field. -/
theorem finite_maximalRestrictedRadicalQuotient
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) :
    Finite (RestrictedRadicalQuotient n (maximalKummerSubgroup K n)) := by
  let _ : Finite (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) :=
    LocalFieldTheory.finite_nthPowerQuotient_of_natCast_ne_zero
      K (n : ℕ) hnK
  exact Finite.of_equiv
    (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
    (maximalRestrictedRadicalQuotientEquiv K n).toEquiv

variable {Omega : Type v} [Field Omega] [Algebra K Omega] [IsSepClosure K Omega]

/-- The maximal exponent-`n` Kummer extension is finite-dimensional. -/
theorem maximalKummerRadicalExtension_finiteDimensional
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    FiniteDimensional K
      (kummerRadicalExtension (K := K) (Omega := Omega) n
        (maximalKummerSubgroup K n).1) := by
  have hfinite : Finite (RestrictedRadicalQuotient n (maximalKummerSubgroup K n)) :=
    finite_maximalRestrictedRadicalQuotient K n hnK
  exact kummerRadicalExtension_finiteDimensional_of_finite_quotient
    n hnK hmu (maximalKummerSubgroup K n)

end KummerTheory

end
