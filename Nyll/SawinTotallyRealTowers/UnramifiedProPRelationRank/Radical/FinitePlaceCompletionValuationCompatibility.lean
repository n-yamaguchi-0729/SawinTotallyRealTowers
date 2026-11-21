/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceModel

public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.LocalValuationKummerDual
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality

/-!
# Valuation compatibility of the two finite-place completion models

The comparison is an isometry; both valuation relations are exactly the norm
comparison relation.  This supplies the certificate for actual Artin naturality.
-/

@[expose] public section

noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich

open NumberField IsDedekindDomain LocalClassFieldTheory GlobalClassFieldTheory.Reciprocity

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (RingOfIntegers F))

attribute [local instance]
  GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel

attribute [local instance]
  ClassFieldTower.Martinet.Shafarevich.finitePlaceAdicCompletionValuativeRel

/-- The canonical completion equivalence preserves the actual valuation relation. -/
theorem finitePlaceCompletion_semilinearValuationCompatible :
    SemilinearValuationCompatible (HeightOneSpectrum.adicAbv F v).Completion
      (v.adicCompletion F) (finitePlaceCompletionAlgEquiv v).toRingEquiv := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  let C' := v.adicCompletion F
  let c := (finitePlaceCompletionAlgEquiv v).toRingEquiv
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
  change ‖x‖ ≤ ‖y‖ ↔ ‖finitePlaceCompletionRingEquiv v x‖ ≤
    ‖finitePlaceCompletionRingEquiv v y‖
  rw [finitePlaceCompletionRingEquiv_norm, finitePlaceCompletionRingEquiv_norm]

end ClassFieldTower.Martinet.Shafarevich
