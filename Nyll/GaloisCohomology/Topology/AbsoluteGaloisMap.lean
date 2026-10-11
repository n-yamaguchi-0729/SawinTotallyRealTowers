/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Normal.Basic

/-!
# Composing absolute Galois restrictions with commutative targets

The chosen algebraic-closure embeddings behind `absoluteGaloisGroup.map`
need not compose. Their discrepancy is an inner automorphism, so restriction
of a continuous homomorphism with commutative target does compose exactly.
-/

namespace Field.absoluteGaloisGroup

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- The algebraic-closure embedding used to define the absolute Galois restriction. -/
noncomputable def closureLift (f : K →+* L) :
    AlgebraicClosure K →+* AlgebraicClosure L :=
  let : Algebra K L := f.toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toRingHom

/-- The chosen closure embedding extends the original field embedding. -/
theorem closureLift_algebraMap (f : K →+* L) (x : K) :
    closureLift f (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (f x) := by
  let : Algebra K L := f.toAlgebra
  change (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (algebraMap K (AlgebraicClosure K) x) = _
  rw [AlgHom.commutes]
  rfl

/-- Absolute Galois restriction commutes with its chosen closure embedding. -/
theorem map_closureLift (f : K →+* L)
    (σ : Gal(AlgebraicClosure L/L)) (x : AlgebraicClosure K) :
    closureLift f ((map f σ : Gal(AlgebraicClosure K/K)).toAlgHom x) = σ (closureLift f x) := by
  let : Algebra K L := f.toAlgebra
  let j : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := j.toAlgebra
  change j (((σ.restrictScalars K).restrictNormal (AlgebraicClosure K)) x) = σ (j x)
  exact (σ.restrictScalars K).restrictNormal_commutes (AlgebraicClosure K) x

private theorem exists_precomposition_aut
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (j₁ j₂ : AlgebraicClosure K →ₐ[K] Ω) :
    ∃ τ : Gal(AlgebraicClosure K/K), ∀ x, j₁ (τ x) = j₂ x := by
  let : Algebra (AlgebraicClosure K) Ω := j₁.toAlgebra
  refine ⟨j₂.restrictNormal' (AlgebraicClosure K), fun x => ?_⟩
  exact j₂.restrictNormal_commutes (AlgebraicClosure K) x

/-- Restriction to a commutative target is independent of the discrepancy between
chosen closure embeddings, and hence respects composition of field embeddings. -/
theorem character_map_comp
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    (f : K →+* L) (g : L →+* M)
    (χ : Gal(AlgebraicClosure K/K) →ₜ* A) :
    χ.comp (map (g.comp f)) = (χ.comp (map f)).comp (map g) := by
  let : Algebra K M := (g.comp f).toAlgebra
  let j₁ : AlgebraicClosure K →ₐ[K] AlgebraicClosure M :=
    { toRingHom := closureLift (g.comp f)
      commutes' := fun x => closureLift_algebraMap (g.comp f) x }
  let j₂ : AlgebraicClosure K →ₐ[K] AlgebraicClosure M :=
    { toRingHom := (closureLift g).comp (closureLift f)
      commutes' := by
        intro x
        change closureLift g (closureLift f (algebraMap K (AlgebraicClosure K) x)) = _
        rw [closureLift_algebraMap, closureLift_algebraMap]
        rfl }
  obtain ⟨τ, hτ⟩ := exists_precomposition_aut j₁ j₂
  ext σ
  let ρ : Gal(AlgebraicClosure K/K) := map (g.comp f) σ
  let θ : Gal(AlgebraicClosure K/K) := map f (map g σ)
  let σ' : Gal(AlgebraicClosure M/M) := σ
  let η : Gal(AlgebraicClosure L/L) := map g σ
  have hcomm : ρ * τ = τ * θ := by
    ext x
    apply j₁.injective
    change j₁ (ρ (τ x)) = j₁ (τ (θ x))
    calc
      j₁ (ρ (τ x)) = σ' (j₁ (τ x)) := map_closureLift (g.comp f) σ' (τ x)
      _ = σ' (j₂ x) := congrArg σ' (hτ x)
      _ = closureLift g (η (closureLift f x)) := (map_closureLift g σ' _).symm
      _ = j₂ (θ x) := congrArg (closureLift g) (map_closureLift f η x).symm
      _ = j₁ (τ (θ x)) := (hτ (θ x)).symm
  have hχ := congrArg χ hcomm
  rw [map_mul, map_mul, mul_comm (χ τ)] at hχ
  exact mul_right_cancel hχ

end Field.absoluteGaloisGroup
