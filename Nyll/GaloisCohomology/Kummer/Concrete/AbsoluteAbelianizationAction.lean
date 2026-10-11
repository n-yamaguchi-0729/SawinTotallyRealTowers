/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Ring.Aut
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugationTopology

/-!
# The canonical action on the abelianized absolute Galois group

Semilinear conjugation descends through the closed commutator subgroup. The
result is independent of the chosen lift to the algebraic closure and gives a
covariant action of base-field automorphisms. A changed continuous abelian
character detects a nontrivial element of this action.
-/

namespace KummerTheory

open ProCGroups.Abelian

section GeneralDetection

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup A] [TopologicalSpace A] [T1Space A]

/-- A continuous abelian character changed by an automorphism detects its
nontrivial action on topological abelianization. -/
theorem topologicalAbelianization_congr_ne_one_of_character_ne
    (e : G ≃ₜ* G) (χ : G →ₜ* A) {x : G} (hχ : χ (e x) ≠ χ x) :
    (TopologicalAbelianization.congr e).toMulEquiv ≠ 1 := by
  intro h
  apply hχ
  have hp := congrArg
    (fun a : MulAut (_root_.TopologicalAbelianization G) =>
      a (TopologicalAbelianization.mk G x)) h
  have hc : TopologicalAbelianization.mk G (e x) =
      TopologicalAbelianization.mk G x := by
    change TopologicalAbelianization.congr e (TopologicalAbelianization.mk G x) =
      TopologicalAbelianization.mk G x at hp
    rw [TopologicalAbelianization.congr_apply_mk] at hp
    exact hp
  have hvalue := congrArg (TopologicalAbelianization.lift χ) hc
  rw [TopologicalAbelianization.lift_apply_mk,
    TopologicalAbelianization.lift_apply_mk] at hvalue
  exact hvalue

end GeneralDetection

section SemilinearIndependence

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω]

/-- The continuous automorphism of topological abelianization depends only
on the base automorphism, not on its semilinear lift. -/
theorem semilinearGaloisAbelianizationEquiv_eq (τ : K ≃+* K) (e e' : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (he' : ∀ k : K, e' (algebraMap K Ω k) = algebraMap K Ω (τ k)) :
    TopologicalAbelianization.congr (semilinearGaloisConjugateContinuousEquiv τ e' he') =
      TopologicalAbelianization.congr (semilinearGaloisConjugateContinuousEquiv τ e he) := by
  apply ContinuousMulEquiv.ext
  intro a
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk Gal(Ω/K) a
  rw [TopologicalAbelianization.congr_apply_mk, TopologicalAbelianization.congr_apply_mk,
    semilinearGaloisConjugateContinuousEquiv_apply,
    semilinearGaloisConjugateContinuousEquiv_apply]
  exact map_semilinearGaloisConjugate_eq (TopologicalAbelianization.mk Gal(Ω/K))
    τ e e' he he' σ

end SemilinearIndependence

section AbsoluteAction

variable {K : Type*} [Field K]

/-- A base automorphism induces a continuous automorphism of the topological
abelianization of its absolute Galois group. -/
noncomputable def absoluteGaloisAbelianizationEquiv (τ : RingAut K) :
    _root_.TopologicalAbelianization Gal(AlgebraicClosure K/K) ≃ₜ*
      _root_.TopologicalAbelianization Gal(AlgebraicClosure K/K) :=
  TopologicalAbelianization.congr (absoluteGaloisConjugateContinuousEquiv τ)

/-- The descended automorphism acts on representatives by Galois conjugation. -/
theorem absoluteGaloisAbelianizationEquiv_apply_mk (τ : RingAut K)
    (σ : Gal(AlgebraicClosure K/K)) :
    absoluteGaloisAbelianizationEquiv τ
        (TopologicalAbelianization.mk Gal(AlgebraicClosure K/K) σ) =
      TopologicalAbelianization.mk Gal(AlgebraicClosure K/K)
        (absoluteGaloisConjugate τ σ) := by
  rw [absoluteGaloisAbelianizationEquiv, TopologicalAbelianization.congr_apply_mk,
    absoluteGaloisConjugateContinuousEquiv_apply]

/-- The descended automorphism agrees with the descent of any actual lift. -/
theorem absoluteGaloisAbelianizationEquiv_eq_of_lift (τ : RingAut K)
    (e : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (he : ∀ k : K, e (algebraMap K (AlgebraicClosure K) k) =
      algebraMap K (AlgebraicClosure K) (τ k)) :
    absoluteGaloisAbelianizationEquiv τ =
      TopologicalAbelianization.congr (semilinearGaloisConjugateContinuousEquiv τ e he) :=
  semilinearGaloisAbelianizationEquiv_eq τ e
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ) he
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) τ)

/-- The identity base automorphism induces the identity on abelianization. -/
theorem absoluteGaloisAbelianizationEquiv_one :
    (absoluteGaloisAbelianizationEquiv (1 : RingAut K)).toMulEquiv = 1 := by
  apply MulEquiv.ext
  intro a
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk
    Gal(AlgebraicClosure K/K) a
  change absoluteGaloisAbelianizationEquiv (1 : RingAut K)
      (TopologicalAbelianization.mk Gal(AlgebraicClosure K/K) σ) =
    TopologicalAbelianization.mk Gal(AlgebraicClosure K/K) σ
  rw [absoluteGaloisAbelianizationEquiv_apply_mk, RingAut.one_eq_refl]
  unfold absoluteGaloisConjugate
  rw [map_semilinearGaloisConjugate_eq
    (TopologicalAbelianization.mk Gal(AlgebraicClosure K/K)) (RingEquiv.refl K)
    (RingEquiv.refl (AlgebraicClosure K))
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) (RingEquiv.refl K))
    (semilinear_refl_algebraMap (K := K) (Ω := AlgebraicClosure K))
    (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K)
      (RingEquiv.refl K)), semilinearGaloisConjugate_refl]

/-- Composition of base automorphisms acts covariantly on abelianization. -/
theorem absoluteGaloisAbelianizationEquiv_mul (τ υ : RingAut K) :
    (absoluteGaloisAbelianizationEquiv (τ * υ)).toMulEquiv =
      (absoluteGaloisAbelianizationEquiv τ).toMulEquiv *
        (absoluteGaloisAbelianizationEquiv υ).toMulEquiv := by
  apply MulEquiv.ext
  intro a
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk
    Gal(AlgebraicClosure K/K) a
  change absoluteGaloisAbelianizationEquiv (τ * υ)
      (TopologicalAbelianization.mk Gal(AlgebraicClosure K/K) σ) =
    absoluteGaloisAbelianizationEquiv τ
      (absoluteGaloisAbelianizationEquiv υ
        (TopologicalAbelianization.mk Gal(AlgebraicClosure K/K) σ))
  rw [absoluteGaloisAbelianizationEquiv_apply_mk,
    absoluteGaloisAbelianizationEquiv_apply_mk, absoluteGaloisAbelianizationEquiv_apply_mk]
  have hbase : (τ * υ : RingAut K) = υ.trans τ := by rfl
  rw [hbase]
  unfold absoluteGaloisConjugate
  rw [map_semilinearGaloisConjugate_eq
    (TopologicalAbelianization.mk Gal(AlgebraicClosure K/K)) (υ.trans τ)
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

/-- The canonical covariant action of base automorphisms on the abelianized
absolute Galois group. -/
noncomputable def absoluteGaloisAbelianizationAction :
    RingAut K →* MulAut (_root_.TopologicalAbelianization Gal(AlgebraicClosure K/K)) where
  toFun τ := (absoluteGaloisAbelianizationEquiv τ).toMulEquiv
  map_one' := absoluteGaloisAbelianizationEquiv_one
  map_mul' := absoluteGaloisAbelianizationEquiv_mul

/-- Evaluation of the canonical action on quotient representatives. -/
theorem absoluteGaloisAbelianizationAction_apply_mk (τ : RingAut K)
    (σ : Gal(AlgebraicClosure K/K)) :
    absoluteGaloisAbelianizationAction τ
        (TopologicalAbelianization.mk Gal(AlgebraicClosure K/K) σ) =
      TopologicalAbelianization.mk Gal(AlgebraicClosure K/K)
        (absoluteGaloisConjugate τ σ) :=
  absoluteGaloisAbelianizationEquiv_apply_mk τ σ

/-- A continuous character changed by base conjugation detects a nontrivial
element of the canonical abelianization action. -/
theorem absoluteGaloisAbelianizationAction_ne_one_of_character_ne
    {A : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A]
    (τ : RingAut K) (χ : Gal(AlgebraicClosure K/K) →ₜ* A)
    {σ : Gal(AlgebraicClosure K/K)}
    (hχ : χ (absoluteGaloisConjugate τ σ) ≠ χ σ) :
    absoluteGaloisAbelianizationAction τ ≠ 1 :=
  topologicalAbelianization_congr_ne_one_of_character_ne
    (absoluteGaloisConjugateContinuousEquiv τ) χ hχ

end AbsoluteAction

end KummerTheory
