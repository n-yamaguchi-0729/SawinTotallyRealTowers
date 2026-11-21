/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntermediateFieldNormResidueNaturality

/-!
# Restriction naturality of the actual abelian local Artin map

The actual algebraic and continuous Artin maps commute with restriction
between finite abelian intermediate fields of the fixed separable closure.
-/



@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory
open RamificationTheory

variable (K : Type*) [Field K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Finite Artin homomorphisms commute with restriction along a
tower of finite abelian intermediate fields. -/
theorem abelianLocalArtinMonoidHom_restrict
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F] :
    (intermediateFieldRestrictNormalHom E F hEF).comp
        (abelianLocalArtinMonoidHom K F) =
      abelianLocalArtinMonoidHom K E := by
  let : Algebra E F := RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  change (AlgEquiv.restrictNormalHom E).comp (abelianLocalArtinMonoidHom K F) =
    abelianLocalArtinMonoidHom K E
  exact abelianLocalArtinMonoidHom_restrict_tower K E F

/-- The continuous actual finite Artin maps commute with restriction along
a tower of finite abelian intermediate fields. -/
theorem abelianLocalArtinMap_restrict
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F] :
    (RamificationTheory.intermediateFieldRestrictContinuous K E F hEF).comp
        (abelianLocalArtinMap K F) =
      abelianLocalArtinMap K E := by
  apply ContinuousMonoidHom.ext
  intro a
  change intermediateFieldRestrictNormalHom E F hEF
      (abelianLocalArtinMap K F a) =
    abelianLocalArtinMap K E a
  rw [show abelianLocalArtinMap K F a =
      abelianLocalArtinMonoidHom K F a by
        exact DFunLike.congr_fun (abelianLocalArtinMap_toMonoidHom K F) a,
    show abelianLocalArtinMap K E a =
      abelianLocalArtinMonoidHom K E a by
        exact DFunLike.congr_fun (abelianLocalArtinMap_toMonoidHom K E) a]
  exact DFunLike.congr_fun
    (abelianLocalArtinMonoidHom_restrict K E F hEF) a

end LocalClassFieldTheory
