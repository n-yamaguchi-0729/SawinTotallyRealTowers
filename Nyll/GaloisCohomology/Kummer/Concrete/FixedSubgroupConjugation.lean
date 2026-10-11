/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugationTopology
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# Conjugation on a normal intermediate field's fixing subgroup

Restriction supplies the base map of an ambient automorphism. The fixing
subgroup equivalence intertwines its actual subgroup conjugation with that
semilinear conjugation, and therefore intertwines their abelianized actions.
-/

namespace KummerTheory

open ProCGroups.Abelian

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
  (L : IntermediateField K Ω) [Normal K L]

/-- The fixing subgroup of a normal intermediate field is the normal kernel
of restriction, even without normality of the ambient extension. -/
theorem fixingSubgroup_normal : L.fixingSubgroup.Normal := by
  rw [← L.restrictNormalHom_ker]
  exact MonoidHom.normal_ker (AlgEquiv.restrictNormalHom L)

local instance fixingSubgroupNormal : L.fixingSubgroup.Normal := fixingSubgroup_normal L

/-- An ambient Galois automorphism is a semilinear lift of its restriction. -/
theorem galois_restrictNormal_algebraMap (σ : Gal(Ω/K)) (x : L) :
    σ.toRingEquiv (algebraMap L Ω x) =
      algebraMap L Ω ((σ.restrictNormal L).toRingEquiv x) :=
  (σ.restrictNormal_commutes L x).symm

/-- The relative Galois identification intertwines subgroup conjugation with
semilinear conjugation by the actual ambient representative. -/
theorem fixingSubgroupEquiv_conjNormal (σ : Gal(Ω/K)) (ρ : L.fixingSubgroup) :
    L.fixingSubgroupEquiv (MulAut.conjNormal σ ρ) =
      semilinearGaloisConjugate (σ.restrictNormal L).toRingEquiv σ.toRingEquiv
        (galois_restrictNormal_algebraMap L σ) (L.fixingSubgroupEquiv ρ) := by
  apply AlgEquiv.ext
  intro x
  rw [fixingSubgroupEquiv_apply, semilinearGaloisConjugate_apply]
  change (σ * (ρ : Gal(Ω/K)) * σ⁻¹) x = σ ((ρ : Gal(Ω/K)) (σ.symm x))
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.coe_inv]

variable [FiniteDimensional K L] [Algebra.IsAlgebraic L Ω]

/-- On topological abelianizations, the actual quotient conjugation agrees
with semilinear conjugation under the continuous fixing subgroup equivalence. -/
theorem fixingSubgroupAbelianization_conjugation (σ : Gal(Ω/K))
    (x : _root_.TopologicalAbelianization L.fixingSubgroup) :
    TopologicalAbelianization.congr (fixingSubgroupContinuousEquiv L)
        (quotientConjugationTopologicalAbelianizationMap L.fixingSubgroup
          (QuotientGroup.mk' L.fixingSubgroup σ) x) =
      TopologicalAbelianization.congr
        (semilinearGaloisConjugateContinuousEquiv (σ.restrictNormal L).toRingEquiv
          σ.toRingEquiv (galois_restrictNormal_algebraMap L σ))
        (TopologicalAbelianization.congr (fixingSubgroupContinuousEquiv L) x) := by
  obtain ⟨ρ, rfl⟩ := TopologicalAbelianization.surjective_mk L.fixingSubgroup x
  rw [quotientConjugationTopologicalAbelianizationMap_mk_apply_mk,
    TopologicalAbelianization.congr_apply_mk, TopologicalAbelianization.congr_apply_mk,
    TopologicalAbelianization.congr_apply_mk, fixingSubgroupContinuousEquiv_apply,
    fixingSubgroupContinuousEquiv_apply, semilinearGaloisConjugateContinuousEquiv_apply,
    fixingSubgroupEquiv_conjNormal]

end KummerTheory
