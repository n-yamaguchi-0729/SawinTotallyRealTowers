/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.LocalValuationKummerDual
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality

set_option autoImplicit false
/-!
# Valuation compatibility of the two finite-place completion models

The comparison is an isometry; both valuation relations are exactly the norm
comparison relation.  This supplies the certificate for actual Artin naturality.
-/

noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich

open NumberField IsDedekindDomain LocalClassFieldTheory GlobalClassFieldTheory.Reciprocity

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (RingOfIntegers F))

local instance finitePlaceCompletionCompatibilitySourceValuativeRel :
    ValuativeRel (HeightOneSpectrum.adicAbv F v).Completion :=
  finitePlaceLocalArtinCompletionValuativeRel v

local instance finitePlaceCompletionCompatibilityTargetValuativeRel :
    ValuativeRel (v.adicCompletion F) :=
  finitePlaceAdicCompletionValuativeRel F v

/-- The canonical completion equivalence preserves the actual valuation relation. -/
theorem finitePlaceCompletion_semilinearValuationCompatible :
    SemilinearValuationCompatible (HeightOneSpectrum.adicAbv F v).Completion
      (v.adicCompletion F) (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  let C' := v.adicCompletion F
  let c := (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let _ : Algebra C C' := c.toRingHom.toAlgebra
  change (ValuativeRel.valuation C).HasExtension (ValuativeRel.valuation C')
  constructor
  intro x y
  change ValuativeRel.valuation C x ≤ ValuativeRel.valuation C y ↔
    ValuativeRel.valuation C' (c x) ≤ ValuativeRel.valuation C' (c y)
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le]
  change ‖x‖₊ ≤ ‖y‖₊ ↔
    (Valued.v : Valuation C' (WithZero (Multiplicative ℤ))) (c x) ≤ Valued.v (c y)
  rw [← Valued.toNormedField.norm_le_iff]
  change ‖x‖ ≤ ‖y‖ ↔ ‖relativeFinitePlaceCompletionRingEquiv v x‖ ≤
    ‖relativeFinitePlaceCompletionRingEquiv v y‖
  rw [relativeFinitePlaceCompletionRingEquiv_norm, relativeFinitePlaceCompletionRingEquiv_norm]

end ClassFieldTower.Martinet.Shafarevich
