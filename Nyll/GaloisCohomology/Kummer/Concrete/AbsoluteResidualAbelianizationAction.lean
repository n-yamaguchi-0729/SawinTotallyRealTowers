/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualEquivalence
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Ring.Aut
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The absolute action on an abelianized residual quotient

Base automorphisms act on the actual residual quotient of the absolute
Galois group. After topological abelianization the action is independent of
the selected semilinear lift, and composition agrees with composition on the
base field. No restriction on the characteristic is needed: compactness of
the absolute Galois group is supplied by its actual comparison with the
separable-closure Galois group.
-/

namespace KummerTheory

open ProCGroups ProCGroups.ProC ProCGroups.Abelian

universe u

variable {K : Type u} [Field K]
  {C : FiniteGroupClass.{u}} (hC : FiniteGroupClass.Hereditary C)

local notation "G" => Gal(AlgebraicClosure K/K)
local notation "R" => proCResidualCore C G
local notation "Q" => G ⧸ R

private noncomputable def residualAbelianizationEquiv (τ : RingAut K) :
    TopologicalAbelianization Q ≃ₜ* TopologicalAbelianization Q := by
  have : CompactSpace G :=
    (ValuationTheory.Completion.separableClosureAutContinuousEquiv K).symm.toHomeomorph.compactSpace
  exact TopologicalAbelianization.congr
    (residualQuotientContinuousMulEquiv hC (absoluteGaloisConjugateContinuousEquiv τ))

private theorem residualAbelianizationEquiv_apply_mk
    (τ : RingAut K) (σ : G) :
    residualAbelianizationEquiv hC τ
        (TopologicalAbelianization.mk Q (QuotientGroup.mk' R σ)) =
      TopologicalAbelianization.mk Q
        (QuotientGroup.mk' R (absoluteGaloisConjugate τ σ)) := by
  rw [residualAbelianizationEquiv, TopologicalAbelianization.congr_apply_mk,
    ← absoluteGaloisConjugateContinuousEquiv_apply]
  rfl

private theorem residualAbelianizationEquiv_one :
    (residualAbelianizationEquiv hC (1 : RingAut K)).toMulEquiv = 1 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨q, rfl⟩ := TopologicalAbelianization.surjective_mk Q x
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective R q
  change residualAbelianizationEquiv hC (1 : RingAut K)
      (TopologicalAbelianization.mk Q (QuotientGroup.mk' R σ)) =
    TopologicalAbelianization.mk Q (QuotientGroup.mk' R σ)
  rw [residualAbelianizationEquiv_apply_mk, RingAut.one_eq_refl]
  change ((TopologicalAbelianization.mk Q).comp (QuotientGroup.mk' R))
      (absoluteGaloisConjugate (RingEquiv.refl K) σ) = _
  unfold absoluteGaloisConjugate
  rw [map_semilinearGaloisConjugate_eq
    ((TopologicalAbelianization.mk Q).comp (QuotientGroup.mk' R))
    (RingEquiv.refl K) (RingEquiv.refl (AlgebraicClosure K))
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K)
      (RingEquiv.refl K))
    (semilinear_refl_algebraMap (K := K) (Ω := AlgebraicClosure K))
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K)
      (RingEquiv.refl K)), semilinearGaloisConjugate_refl]
  rfl

private theorem residualAbelianizationEquiv_mul (τ υ : RingAut K) :
    (residualAbelianizationEquiv hC (τ * υ)).toMulEquiv =
      (residualAbelianizationEquiv hC τ).toMulEquiv *
        (residualAbelianizationEquiv hC υ).toMulEquiv := by
  apply MulEquiv.ext
  intro x
  obtain ⟨q, rfl⟩ := TopologicalAbelianization.surjective_mk Q x
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective R q
  change residualAbelianizationEquiv hC (τ * υ)
      (TopologicalAbelianization.mk Q (QuotientGroup.mk' R σ)) =
    residualAbelianizationEquiv hC τ
      (residualAbelianizationEquiv hC υ
        (TopologicalAbelianization.mk Q (QuotientGroup.mk' R σ)))
  rw [residualAbelianizationEquiv_apply_mk, residualAbelianizationEquiv_apply_mk,
    residualAbelianizationEquiv_apply_mk]
  have hbase : (τ * υ : RingAut K) = υ.trans τ := rfl
  rw [hbase]
  change ((TopologicalAbelianization.mk Q).comp (QuotientGroup.mk' R))
      (absoluteGaloisConjugate (υ.trans τ) σ) = _
  unfold absoluteGaloisConjugate
  rw [map_semilinearGaloisConjugate_eq
    ((TopologicalAbelianization.mk Q).comp (QuotientGroup.mk' R)) (υ.trans τ)
    ((IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) υ).trans
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ))
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) (υ.trans τ))
    (semilinear_trans_algebraMap υ τ
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) υ)
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ)
      (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) υ)
      (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) τ))
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K)
      (υ.trans τ)), semilinearGaloisConjugate_trans]
  rfl

/-- Base automorphisms act on the abelianization of the actual residual
quotient of the absolute Galois group. -/
noncomputable def absoluteGaloisResidualAbelianizationAction :
    RingAut K →* MulAut (TopologicalAbelianization Q) where
  toFun τ := (residualAbelianizationEquiv hC τ).toMulEquiv
  map_one' := residualAbelianizationEquiv_one hC
  map_mul' := residualAbelianizationEquiv_mul hC

/-- On representatives the residual action is the actual absolute Galois
conjugation, followed by the two quotient maps. -/
theorem absoluteGaloisResidualAbelianizationAction_apply_mk
    (τ : RingAut K) (σ : G) :
    absoluteGaloisResidualAbelianizationAction hC τ
        (TopologicalAbelianization.mk Q (QuotientGroup.mk' R σ)) =
      TopologicalAbelianization.mk Q
        (QuotientGroup.mk' R (absoluteGaloisConjugate τ σ)) :=
  residualAbelianizationEquiv_apply_mk hC τ σ

/-- The representative formula holds for any actual semilinear lift of
the same field automorphism. -/
theorem absoluteGaloisResidualAbelianizationAction_apply_mk_of_lift
    (τ : RingAut K) (e : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (he : ∀ k : K, e (algebraMap K (AlgebraicClosure K) k) =
      algebraMap K (AlgebraicClosure K) (τ k))
    (σ : G) :
    absoluteGaloisResidualAbelianizationAction hC τ
        (TopologicalAbelianization.mk Q (QuotientGroup.mk' R σ)) =
      TopologicalAbelianization.mk Q
        (QuotientGroup.mk' R (semilinearGaloisConjugate τ e he σ)) := by
  rw [absoluteGaloisResidualAbelianizationAction_apply_mk]
  change ((TopologicalAbelianization.mk Q).comp (QuotientGroup.mk' R))
      (absoluteGaloisConjugate τ σ) = _
  unfold absoluteGaloisConjugate
  exact map_semilinearGaloisConjugate_eq
    ((TopologicalAbelianization.mk Q).comp (QuotientGroup.mk' R)) τ e
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ) he
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) τ) σ

end KummerTheory
