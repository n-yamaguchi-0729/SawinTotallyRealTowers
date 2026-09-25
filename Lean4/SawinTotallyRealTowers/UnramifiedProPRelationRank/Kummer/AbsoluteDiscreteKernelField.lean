/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false
/-!
# The finite Galois field detected by a discrete absolute representation

Continuity gives an open normal kernel. Its actual fixed field is finite
Galois, and its Galois group embeds in the target through the quotient by
that kernel. In particular a `p`-group target produces a `p`-extension;
the target itself need not be finite. No new instances are installed.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open RamificationTheory.Field.absoluteGaloisGroup

variable (F : Type) [Field F] [NumberField F]
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- The open normal kernel, on the literal algebraic-closure automorphism group. -/
def absoluteDiscreteKernelOpenNormal (s : Field.absoluteGaloisGroup F →ₜ* Q) :
    OpenNormalSubgroup Gal(AlgebraicClosure F/F) := by
  let a : Gal(AlgebraicClosure F/F) →ₜ* Q :=
    s.comp (absoluteGaloisGroupContinuousMulEquiv F).symm
  exact
    { toOpenSubgroup := ⟨a.toMonoidHom.ker,
        (isOpen_discrete ({1} : Set Q)).preimage a.continuous⟩
      isNormal' := MonoidHom.normal_ker _ }

/-- The actual finite fixed field of a continuous discrete representation. -/
abbrev absoluteDiscreteKernelField (s : Field.absoluteGaloisGroup F →ₜ* Q) :
    IntermediateField F (AlgebraicClosure F) :=
  fixedFieldOfOpenNormalSubgroup F (absoluteDiscreteKernelOpenNormal F s)

/-- The kernel fixed field is Galois by normality of the actual kernel. -/
theorem absoluteDiscreteKernelField_isGalois
    (s : Field.absoluteGaloisGroup F →ₜ* Q) : IsGalois F (absoluteDiscreteKernelField F s) :=
  isGalois_fixedFieldOfOpenNormalSubgroup F (absoluteDiscreteKernelOpenNormal F s)

variable (s : Field.absoluteGaloisGroup F →ₜ* Q)

/-- The fixing subgroup is exactly the kernel of the original representation. -/
theorem absoluteDiscreteKernelField_fixingSubgroup :
    (absoluteDiscreteKernelField F s).fixingSubgroup =
      (s.comp (↑(absoluteGaloisGroupContinuousMulEquiv F).symm :
        Gal(AlgebraicClosure F/F) →ₜ* Field.absoluteGaloisGroup F)).toMonoidHom.ker :=
  fixingSubgroup_fixedFieldOfOpenSubgroup F
    (absoluteDiscreteKernelOpenNormal F s).toOpenSubgroup

/-- The finite Galois group acts faithfully through the target of the representation. -/
def absoluteDiscreteKernelGaloisHom : Gal(absoluteDiscreteKernelField F s/F) →* Q :=
  (QuotientGroup.lift
    ((absoluteDiscreteKernelOpenNormal F s).toSubgroup)
    (s.comp (↑(absoluteGaloisGroupContinuousMulEquiv F).symm :
      Gal(AlgebraicClosure F/F) →ₜ* Field.absoluteGaloisGroup F)).toMonoidHom
    le_rfl).comp
      (quotientOpenNormalSubgroupEquivGalFixedField F
        (absoluteDiscreteKernelOpenNormal F s)).symm.toMonoidHom

/-- Faithfulness follows from quotienting by exactly the kernel. -/
theorem absoluteDiscreteKernelGaloisHom_injective :
    Function.Injective (absoluteDiscreteKernelGaloisHom F s) := by
  unfold absoluteDiscreteKernelGaloisHom
  apply Function.Injective.comp _ (MulEquiv.injective _)
  exact QuotientGroup.kerLift_injective _

/-- A `p`-group target gives a genuine finite Galois `p`-extension. -/
theorem absoluteDiscreteKernelField_isPGroup
    (p : ℕ) (hP : IsPGroup p Q) : IsPGroup p Gal(absoluteDiscreteKernelField F s/F) :=
  hP.of_injective (absoluteDiscreteKernelGaloisHom F s)
    (absoluteDiscreteKernelGaloisHom_injective F s)

/-- Restriction to the kernel fixed field recovers the original representation. -/
theorem absoluteDiscreteKernelGaloisHom_restrict
    (sigma : Field.absoluteGaloisGroup F) :
    absoluteDiscreteKernelGaloisHom F s
      (AlgEquiv.restrictNormalHom (absoluteDiscreteKernelField F s)
        (absoluteGaloisGroupContinuousMulEquiv F sigma)) =
        s sigma := by
  rw [← quotientOpenNormalSubgroupEquivGalFixedField_mk']
  simp only [absoluteDiscreteKernelGaloisHom, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

end ClassFieldTower.Martinet.Shafarevich
