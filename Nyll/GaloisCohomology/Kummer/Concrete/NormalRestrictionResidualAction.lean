/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.NormalRestrictionKernel
import Nyll.GaloisCohomology.Kummer.Concrete.NormalRestrictionKernelFinite
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteResidualAbelianizationAction
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualEquivalence
import Nyll.ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The restriction kernel and the absolute residual action

The actual kernel of normal restriction identifies with the upper field's
absolute Galois group. Transport through both actual quotient maps preserves
conjugation by the same lift of the relative automorphism.
-/

namespace KummerTheory

open ProCGroups ProCGroups.ProC ProCGroups.Abelian

universe u

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  [FiniteDimensional K M] [Normal K M] [CharZero K]
  {C : FiniteGroupClass.{u}}

local notation "AC" => AlgebraicClosure M
local notation "N" => MonoidHom.ker (AlgEquiv.restrictNormalHom M : Gal(AC/K) →* Gal(M/K))
local notation "G" => Gal(AC/M)

/-- The actual restriction kernel's abelianized residual quotient is the
upper field's abelianized absolute residual quotient. -/
noncomputable def normalRestrictionResidualAbelianizationEquiv
    (hC : FiniteGroupClass.Hereditary C) :
    TopologicalAbelianization (N ⧸ proCResidualCore C N) ≃ₜ*
      TopologicalAbelianization (G ⧸ proCResidualCore C G) := by
  have : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  have : CompactSpace N :=
    ((N).isClosed_of_isOpen (normalRestrictionKernel_isOpen
      (K := K) (M := M) (Ω := AC))).isClosedEmbedding_subtypeVal.compactSpace
  exact TopologicalAbelianization.congr (residualQuotientContinuousMulEquiv hC
    (normalRestrictionKernelContinuousEquiv (K := K) M AC))

/-- The restriction-kernel comparison evaluates through the actual two
quotient maps. -/
theorem normalRestrictionResidualAbelianizationEquiv_apply_mk
    (hC : FiniteGroupClass.Hereditary C) (x : N) :
    normalRestrictionResidualAbelianizationEquiv (K := K) (M := M) hC
        (TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
          (QuotientGroup.mk' (proCResidualCore C N) x)) =
      TopologicalAbelianization.mk (G ⧸ proCResidualCore C G)
        (QuotientGroup.mk' (proCResidualCore C G)
          (normalRestrictionKernelContinuousEquiv (K := K) M AC x)) := by
  rfl

/-- Conjugation on the restriction kernel transports to the canonical
absolute residual action of the actual restricted field automorphism. -/
theorem normalRestrictionResidualAbelianizationEquiv_conjugation
    (hC : FiniteGroupClass.FullFormation C) (g : Gal(AC/K))
    (a : TopologicalAbelianization (N ⧸ proCResidualCore C N)) :
    normalRestrictionResidualAbelianizationEquiv (K := K) (M := M) hC.hereditary
        (TopologicalAbelianization.congr
          (residualQuotientConjugationContinuousMulEquiv hC N
            ((N).isClosed_of_isOpen
              (normalRestrictionKernel_isOpen (K := K) (M := M) (Ω := AC))) g) a) =
      absoluteGaloisResidualAbelianizationAction hC.hereditary
        (g.restrictNormal M).toRingEquiv
        (normalRestrictionResidualAbelianizationEquiv (K := K) (M := M) hC.hereditary a) := by
  refine Quotient.inductionOn' a ?_
  intro q
  refine Quotient.inductionOn' q ?_
  intro x
  let j : G →* TopologicalAbelianization (G ⧸ proCResidualCore C G) :=
    (TopologicalAbelianization.mk (G ⧸ proCResidualCore C G)).comp
      (QuotientGroup.mk' (proCResidualCore C G))
  exact (congrArg j (normalRestrictionKernelContinuousEquiv_conjNormal
      (K := K) M AC g x)).trans
    (absoluteGaloisResidualAbelianizationAction_apply_mk_of_lift (K := M) hC.hereditary
      (g.restrictNormal M).toRingEquiv g.toRingEquiv (normalRestriction_algebraMap M AC g)
      (normalRestrictionKernelContinuousEquiv (K := K) M AC x)).symm

end KummerTheory
