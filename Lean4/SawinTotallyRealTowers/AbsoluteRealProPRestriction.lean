/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.MaximalRealProPOutside
import ProCGroups.Topologies.ContinuousMulEquiv
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient

set_option autoImplicit false

/-!
# Absolute restriction to the maximal real pro-p compositum

The actual ambient inclusion supplies a continuous surjective restriction
homomorphism. Its kernel is exactly the subgroup fixing the constructed
compositum. The quotient by this kernel is continuously isomorphic to the
relative Galois group, providing the concrete quotient for later factorization.
No primality or ramification comparison is needed for this Galois boundary.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

private def normalAbsoluteRestriction (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M) :
    Field.absoluteGaloisGroup F →ₜ* (M ≃ₐ[F] M) := by
  let : Normal F M := hM
  exact
    { toMonoidHom := AlgEquiv.restrictNormalHom M
      continuous_toFun := InfiniteGalois.restrictNormalHom_continuous M }

private theorem normalAbsoluteRestriction_surjective (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M) :
    Function.Surjective (normalAbsoluteRestriction F M hM) := by
  let : Normal F M := hM
  exact AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure F)

private theorem normalAbsoluteRestriction_apply (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M)
    (σ : Field.absoluteGaloisGroup F) (x : M) :
    (normalAbsoluteRestriction F M hM σ x : AlgebraicClosure F) =
      (AlgEquiv.toAlgHom (R := F) (A₁ := AlgebraicClosure F)
        (A₂ := AlgebraicClosure F) σ) (x : AlgebraicClosure F) := by
  let : Normal F M := hM
  exact AlgEquiv.restrictNormalHom_apply M σ x

private theorem normalAbsoluteRestriction_ker (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M) :
    (normalAbsoluteRestriction F M hM).toMonoidHom.ker = M.fixingSubgroup := by
  let : Normal F M := hM
  exact IntermediateField.restrictNormalHom_ker M

/-- Restriction of absolute automorphisms to the constructed maximal real
compositum with the given finite ramification support. -/
def absoluteToMaximalRealProPOutside (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    Field.absoluteGaloisGroup ℚ →ₜ*
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) :=
  normalAbsoluteRestriction ℚ (maximalRealProPOutside p T)
    (maximalRealProPOutside_isGalois p T).to_normal

/-- Every automorphism of the maximal real compositum extends to the fixed
algebraic closure. -/
theorem absoluteToMaximalRealProPOutside_surjective (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    Function.Surjective (absoluteToMaximalRealProPOutside p T) :=
  normalAbsoluteRestriction_surjective ℚ (maximalRealProPOutside p T)
    (maximalRealProPOutside_isGalois p T).to_normal

/-- The restriction acts by the original absolute automorphism on each
element of the constructed intermediate field. -/
theorem absoluteToMaximalRealProPOutside_apply (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (σ : Field.absoluteGaloisGroup ℚ) (x : maximalRealProPOutside p T) :
    (absoluteToMaximalRealProPOutside p T σ x : AlgebraicClosure ℚ) =
      (AlgEquiv.toAlgHom (R := ℚ) (A₁ := AlgebraicClosure ℚ)
        (A₂ := AlgebraicClosure ℚ) σ) (x : AlgebraicClosure ℚ) :=
  normalAbsoluteRestriction_apply ℚ (maximalRealProPOutside p T)
    (maximalRealProPOutside_isGalois p T).to_normal σ x

/-- The actual restriction kernel is the fixing subgroup of the actual
maximal compositum. No separate kernel structure is introduced. -/
theorem absoluteToMaximalRealProPOutside_ker (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    (absoluteToMaximalRealProPOutside p T).toMonoidHom.ker =
      (maximalRealProPOutside p T).fixingSubgroup :=
  normalAbsoluteRestriction_ker ℚ (maximalRealProPOutside p T)
    (maximalRealProPOutside_isGalois p T).to_normal

/-- The quotient by the actual restriction kernel is the relative Galois
group as a topological group. -/
def absoluteRealProPOutsideQuotientEquiv (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    (Field.absoluteGaloisGroup ℚ ⧸
      (absoluteToMaximalRealProPOutside p T).toMonoidHom.ker) ≃ₜ*
      (maximalRealProPOutside p T ≃ₐ[ℚ] maximalRealProPOutside p T) := by
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let : IsGalois ℚ (maximalRealProPOutside p T) := maximalRealProPOutside_isGalois p T
  let : CompactSpace (Field.absoluteGaloisGroup ℚ) :=
    inferInstanceAs
      (CompactSpace (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  let f := absoluteToMaximalRealProPOutside p T
  let e := QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom
    (absoluteToMaximalRealProPOutside_surjective p T)
  have hContinuous : Continuous e.toMonoidHom := by
    apply (QuotientGroup.isQuotientMap_mk f.toMonoidHom.ker).continuous_iff.mpr
    exact f.continuous_toFun
  have hBijective : Function.Bijective e.toMonoidHom := e.bijective
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    e.toMonoidHom hContinuous hBijective

/-- The quotient equivalence sends the class of an absolute automorphism
to its restriction. -/
theorem absoluteRealProPOutsideQuotientEquiv_mk (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) (σ : Field.absoluteGaloisGroup ℚ) :
    absoluteRealProPOutsideQuotientEquiv p T
      (QuotientGroup.mk' (absoluteToMaximalRealProPOutside p T).toMonoidHom.ker σ) =
        absoluteToMaximalRealProPOutside p T σ := by
  change QuotientGroup.kerLift (absoluteToMaximalRealProPOutside p T).toMonoidHom
      (QuotientGroup.mk' (absoluteToMaximalRealProPOutside p T).toMonoidHom.ker σ) =
    absoluteToMaximalRealProPOutside p T σ
  exact QuotientGroup.kerLift_mk (absoluteToMaximalRealProPOutside p T).toMonoidHom σ

end ClassFieldTower.Sawin
