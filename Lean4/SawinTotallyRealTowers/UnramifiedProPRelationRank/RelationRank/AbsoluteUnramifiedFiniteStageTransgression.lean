/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.FiniteStageTransgressionLinear
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteUnramifiedH2Quotient

set_option autoImplicit false
/-!
# Finite-stage transgression for the absolute unramified quotient

For an open normal finite `p`-quotient of the absolute Galois group, finite transgression first
lands in the degree-two cohomology of the absolute group modulo its unramified kernel.  The
topological quotient equivalence then transports that class back to the degree-two cohomology of
the maximal everywhere-unramified pro-`p` Galois group.
-/

open scoped NumberField

noncomputable section

universe u

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open ClassFieldTower.Martinet
open ClassFieldTower.ProP
open ProCGroups ProCGroups.ProC

variable (F : Type u) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

private noncomputable instance absoluteFiniteStageCompactSpace :
    CompactSpace (Field.absoluteGaloisGroup F) :=
  inferInstanceAs
    (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))

/-- Finite-stage transgression for the absolute unramified kernel, transported from the quotient
of the absolute Galois group to the maximal everywhere-unramified pro-`p` Galois group. -/
noncomputable def absoluteUnramifiedFiniteStageTransgressionLinearMap
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p)
      (Field.absoluteGaloisGroup F)) :
    InvariantFiniteCharacter (p := p)
        (finiteStageImage (absoluteUnramifiedKernel F p) U) →ₗ[ZMod p]
      continuousCohomologyZModPLifted p
        (MaxEverywhereUnramifiedProPGaloisGroup F p) 2 :=
  (absoluteUnramifiedQuotientH2LinearEquiv F p).symm.toLinearMap.comp
    (inflatedFiniteTransgressionLinearMap
      (absoluteUnramifiedKernel F p) U)

/-- The absolute finite-stage map is inflated transgression followed by inverse transport across
the quotient cohomology equivalence. -/
@[simp]
theorem absoluteUnramifiedFiniteStageTransgressionLinearMap_apply
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p)
      (Field.absoluteGaloisGroup F))
    (χ : InvariantFiniteCharacter (p := p)
      (finiteStageImage (absoluteUnramifiedKernel F p) U)) :
    absoluteUnramifiedFiniteStageTransgressionLinearMap F p U χ =
      (absoluteUnramifiedQuotientH2LinearEquiv F p).symm
        (inflatedFiniteTransgressionLinearMap
          (absoluteUnramifiedKernel F p) U χ) :=
  rfl

/-- The zero invariant character has zero absolute unramified transgression. -/
@[simp]
theorem absoluteUnramifiedFiniteStageTransgressionLinearMap_zero
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p)
      (Field.absoluteGaloisGroup F)) :
    absoluteUnramifiedFiniteStageTransgressionLinearMap F p U
        (0 : InvariantFiniteCharacter (p := p)
          (finiteStageImage (absoluteUnramifiedKernel F p) U)) = 0 :=
  map_zero (absoluteUnramifiedFiniteStageTransgressionLinearMap F p U)

/-- Transport across the quotient cohomology equivalence does not change the kernel of finite-
stage inflated transgression. -/
theorem absoluteUnramifiedFiniteStageTransgressionLinearMap_ker
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p)
      (Field.absoluteGaloisGroup F)) :
    LinearMap.ker (absoluteUnramifiedFiniteStageTransgressionLinearMap F p U) =
      LinearMap.ker (inflatedFiniteTransgressionLinearMap
        (absoluteUnramifiedKernel F p) U) := by
  ext χ
  simp only [LinearMap.mem_ker,
    absoluteUnramifiedFiniteStageTransgressionLinearMap_apply,
    LinearEquiv.map_eq_zero_iff]

end ClassFieldTower.Martinet.Shafarevich
