/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence

set_option autoImplicit false
/-! # Restriction to the actual maximal abelian subextension -/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

variable (F : Type) [Field F]

/-- Restrict the standard absolute Galois group to the maximal abelian
subextension of the fixed separable closure. -/
noncomputable def globalMaximalAbelianRestriction :
    Field.absoluteGaloisGroup F →ₜ* Gal(_root_.maximalAbelianExtension F / F) :=
  ({ toMonoidHom := AlgEquiv.restrictNormalHom (_root_.maximalAbelianExtension F)
     continuous_toFun := InfiniteGalois.restrictNormalHom_continuous
       (_root_.maximalAbelianExtension F) } :
      Gal(SeparableClosure F / F) →ₜ* Gal(_root_.maximalAbelianExtension F / F)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv F))

@[simp]
theorem globalMaximalAbelianRestriction_apply (sigma : Field.absoluteGaloisGroup F) :
    globalMaximalAbelianRestriction F sigma =
      AlgEquiv.restrictNormalHom (_root_.maximalAbelianExtension F)
        (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv F sigma) :=
  rfl

/-- Absolute automorphisms surject onto the maximal abelian Galois group. -/
theorem globalMaximalAbelianRestriction_surjective :
    Function.Surjective (globalMaximalAbelianRestriction F) :=
  (AlgEquiv.restrictNormalHom_surjective
    (F := F) (K₁ := _root_.maximalAbelianExtension F) (SeparableClosure F)).comp
      (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv F).surjective

end ClassFieldTower.Martinet.Shafarevich
