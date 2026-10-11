/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.AlgebraCoactionTransport
public import Nyll.SchemeTheory.FiniteEtale.Algebra.ProductBaseChangeComparison
public import Nyll.SchemeTheory.FiniteEtale.Algebra.UniversalHomeomorphismAlgHom
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descending the actual coaction of an étale local model

An actual model over an étale covering algebra acquires its canonical upper
coaction from its scalar-extension equivalence. Universal-homeomorphism
invariance of algebra maps descends this map. The same injectivity detects
linearity, the counit equation, and coassociativity.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Algebra.Descent

variable (R S B M : Type u) [CommRing R] [CommRing S] [CommRing B] [CommRing M]
variable [Algebra R S] [Algebra R B] [Algebra R M] [Algebra B M]
variable [IsScalarTower R B M]

private theorem scalarTensorIso_counit :
    let : Algebra (S ⊗[R] B) (S ⊗[R] M) :=
      Algebra.TensorProduct.baseChangeAlgebra R S B M;
    let : IsScalarTower S (S ⊗[R] B) (S ⊗[R] M) :=
      Algebra.TensorProduct.baseChangeAlgebra_isScalarTower R S B M;
    ∀ z : (S ⊗[R] B) ⊗[S] (S ⊗[R] M),
      Algebra.TensorProduct.map (.id S S)
          ((tensorTargetDiagonal R B M).restrictScalars R)
          (scalarTensorIso R S B M z) =
        tensorTargetDiagonal S (S ⊗[R] B) (S ⊗[R] M) z := by
  intro hEU hTower z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    induction x using TensorProduct.inductionOn with
    | tmul s b =>
      induction y using TensorProduct.inductionOn with
      | tmul t m =>
        simp only [scalarTensorIso_tmul, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, AlgHom.restrictScalars_apply, tensorTargetDiagonal,
          Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
        change (s * t) ⊗ₜ[R] (algebraMap B M b * m) =
          (s ⊗ₜ[R] algebraMap B M b) * (t ⊗ₜ[R] m)
        exact (Algebra.TensorProduct.tmul_mul_tmul s t (algebraMap B M b) m).symm
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An actual scalar-extension model has a descended algebra coaction with
its counit, coassociativity, and exact scalar-extension comparison. -/
theorem exists_coaction_of_radicial_model
    (A : Type u) [CommRing A] [Algebra S A]
    [Algebra.Etale R B] [Algebra.Etale B M]
    [IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    let : Algebra (S ⊗[R] B) (S ⊗[R] M) :=
      Algebra.TensorProduct.baseChangeAlgebra R S B M;
    let : IsScalarTower S (S ⊗[R] B) (S ⊗[R] M) :=
      Algebra.TensorProduct.baseChangeAlgebra_isScalarTower R S B M;
    ∀ e : (S ⊗[R] M) ≃ₐ[S ⊗[R] B] (S ⊗[R] B) ⊗[S] A,
      ∃ ρ : M →ₐ[B] B ⊗[R] M,
        (∀ m : M, tensorTargetDiagonal R B M (ρ m) = m) ∧
        (∀ m : M,
          Algebra.TensorProduct.map (.id B B) (ρ.restrictScalars R) (ρ m) =
            Algebra.TensorProduct.map (.id B B)
              (Algebra.TensorProduct.includeRight : M →ₐ[R] B ⊗[R] M) (ρ m)) ∧
        Algebra.TensorProduct.map (.id S S) (ρ.restrictScalars R) =
          (scalarTensorIso R S B M).toAlgHom.comp
            ((transportedCoaction S (S ⊗[R] B) (S ⊗[R] M) A e).restrictScalars S) := by
  intro hEU hTower e
  let E := S ⊗[R] B
  let U := S ⊗[R] M
  let N := B ⊗[R] M
  let N₂ := B ⊗[R] N
  have : Algebra.Etale R M := Algebra.Etale.comp R B M
  let ηM : M →ₐ[R] U := Algebra.TensorProduct.includeRight
  let ηN : N →ₐ[R] S ⊗[R] N := Algebra.TensorProduct.includeRight
  let ψ : E ⊗[S] U ≃ₐ[S] S ⊗[R] N := scalarTensorIso R S B M
  let σ : U →ₐ[E] E ⊗[S] U := transportedCoaction S E U A e
  let τ : U →ₐ[S] S ⊗[R] N := ψ.toAlgHom.comp (σ.restrictScalars S)
  obtain ⟨ρ₀, hρ₀⟩ :=
    (Algebra.Etale.includeRight_comp_bijective_of_universalHomeomorphism R S M N).2
      ((τ.restrictScalars R).comp ηM)
  have hcomparison₀ : Algebra.TensorProduct.map (.id S S) ρ₀ = τ := by
    apply Algebra.TensorProduct.ext'
    intro s m
    have hm : (1 : S) ⊗ₜ[R] ρ₀ m = τ ((1 : S) ⊗ₜ[R] m) :=
      AlgHom.congr_fun hρ₀ m
    calc
      Algebra.TensorProduct.map (.id S S) ρ₀ (s ⊗ₜ[R] m) =
          s • ((1 : S) ⊗ₜ[R] ρ₀ m) := by
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = s • τ ((1 : S) ⊗ₜ[R] m) := congrArg (s • ·) hm
      _ = τ (s ⊗ₜ[R] m) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let β : B →ₐ[R] M := IsScalarTower.toAlgHom R B M
  let γ : B →ₐ[R] N := (Algebra.TensorProduct.includeLeft : B →ₐ[B] N).restrictScalars R
  have hlinear : ρ₀.comp β = γ := by
    apply (Algebra.Etale.includeRight_comp_bijective_of_universalHomeomorphism R S B N).1
    apply AlgHom.ext
    intro b
    calc
      ηN (ρ₀ (β b)) = τ ((1 : S) ⊗ₜ[R] β b) := AlgHom.congr_fun hρ₀ (β b)
      _ = ψ (σ (algebraMap E U ((1 : S) ⊗ₜ[R] b))) := rfl
      _ = ψ (((1 : S) ⊗ₜ[R] b) ⊗ₜ[S] (1 : U)) := by
        rw [σ.commutes, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self_apply]
      _ = (1 : S) ⊗ₜ[R] (b ⊗ₜ[R] (1 : M)) := by
        change scalarTensorIso R S B M
          (((1 : S) ⊗ₜ[R] b) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] (1 : M))) = _
        rw [scalarTensorIso_tmul, one_mul]
      _ = ηN (γ b) := rfl
  let ρ : M →ₐ[B] N := {
    __ := ρ₀.toRingHom
    commutes' b := AlgHom.congr_fun hlinear b
  }
  have hcomparison : Algebra.TensorProduct.map (.id S S) (ρ.restrictScalars R) = τ :=
    hcomparison₀
  have hρ (m : M) : (1 : S) ⊗ₜ[R] ρ m = ψ (σ (ηM m)) :=
    AlgHom.congr_fun hρ₀ m
  have hcounit : (tensorTargetDiagonal R B M).comp ρ = AlgHom.id B M := by
    apply AlgHom.restrictScalars_injective R
    apply (Algebra.Etale.includeRight_comp_bijective_of_universalHomeomorphism R S M M).1
    apply AlgHom.ext
    intro m
    change (1 : S) ⊗ₜ[R] tensorTargetDiagonal R B M (ρ m) = (1 : S) ⊗ₜ[R] m
    calc
      (1 : S) ⊗ₜ[R] tensorTargetDiagonal R B M (ρ m) =
          Algebra.TensorProduct.map (.id S S)
            ((tensorTargetDiagonal R B M).restrictScalars R)
            ((1 : S) ⊗ₜ[R] ρ m) := by
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.restrictScalars_apply]
      _ = Algebra.TensorProduct.map (.id S S)
          ((tensorTargetDiagonal R B M).restrictScalars R) (ψ (σ (ηM m))) :=
        congrArg (Algebra.TensorProduct.map (.id S S)
          ((tensorTargetDiagonal R B M).restrictScalars R)) (hρ m)
      _ = tensorTargetDiagonal S E U (σ (ηM m)) :=
        scalarTensorIso_counit R S B M (σ (ηM m))
      _ = (1 : S) ⊗ₜ[R] m := transportedCoaction_counit S E U A e (ηM m)
  let H : E ⊗[S] (E ⊗[S] U) →ₐ[S] S ⊗[R] N₂ :=
    (scalarTensorIso R S B N).toAlgHom.comp
      (Algebra.TensorProduct.map (.id S E) ψ.toAlgHom)
  have hleft (z : E ⊗[S] U) :
      Algebra.TensorProduct.map (.id S S)
          ((Algebra.TensorProduct.map (.id B B) (ρ.restrictScalars R)).restrictScalars R)
          (ψ z) =
        H (Algebra.TensorProduct.map (.id E E) (σ.restrictScalars S) z) := by
    rw [scalarTensorIso_natural]
    change scalarTensorIso R S B N
        (Algebra.TensorProduct.map (.id S E)
          (Algebra.TensorProduct.map (.id S S) (ρ.restrictScalars R)) z) = _
    rw [hcomparison]
    apply congrArg (scalarTensorIso R S B N)
    induction z using TensorProduct.inductionOn with
    | tmul b u => rfl
    | add z w hz hw => simp only [map_add, hz, hw]
  have hright (z : E ⊗[S] U) :
      Algebra.TensorProduct.map (.id S S)
          ((Algebra.TensorProduct.map (.id B B)
            (Algebra.TensorProduct.includeRight : M →ₐ[R] N)).restrictScalars R)
          (ψ z) =
        H (Algebra.TensorProduct.map (.id E E)
          (Algebra.TensorProduct.includeRight : U →ₐ[S] E ⊗[S] U) z) := by
    rw [scalarTensorIso_natural]
    apply congrArg (scalarTensorIso R S B N)
    induction z using TensorProduct.inductionOn with
    | tmul b u =>
      change b ⊗ₜ[S] Algebra.TensorProduct.map (.id S S)
          (Algebra.TensorProduct.includeRight : M →ₐ[R] N) u =
        b ⊗ₜ[S] ψ ((1 : E) ⊗ₜ[S] u)
      exact congrArg (fun v : S ⊗[R] N ↦ b ⊗ₜ[S] v)
        (scalarTensorIso_one_tmul R S B M u).symm
    | add z w hz hw => simp only [map_add, hz, hw]
  have hcoassoc :
      (Algebra.TensorProduct.map (.id B B) (ρ.restrictScalars R)).comp ρ =
        (Algebra.TensorProduct.map (.id B B)
          (Algebra.TensorProduct.includeRight : M →ₐ[R] N)).comp ρ := by
    apply AlgHom.restrictScalars_injective R
    apply (Algebra.Etale.includeRight_comp_bijective_of_universalHomeomorphism R S M N₂).1
    apply AlgHom.ext
    intro m
    change (1 : S) ⊗ₜ[R]
        Algebra.TensorProduct.map (.id B B) (ρ.restrictScalars R) (ρ m) =
      (1 : S) ⊗ₜ[R] Algebra.TensorProduct.map (.id B B)
        (Algebra.TensorProduct.includeRight : M →ₐ[R] N) (ρ m)
    calc
      _ = Algebra.TensorProduct.map (.id S S)
          ((Algebra.TensorProduct.map (.id B B) (ρ.restrictScalars R)).restrictScalars R)
          ((1 : S) ⊗ₜ[R] ρ m) := rfl
      _ = Algebra.TensorProduct.map (.id S S)
          ((Algebra.TensorProduct.map (.id B B) (ρ.restrictScalars R)).restrictScalars R)
          (ψ (σ (ηM m))) := by rw [hρ]
      _ = H (Algebra.TensorProduct.map (.id E E) (σ.restrictScalars S) (σ (ηM m))) :=
        hleft (σ (ηM m))
      _ = H (Algebra.TensorProduct.map (.id E E)
          (Algebra.TensorProduct.includeRight : U →ₐ[S] E ⊗[S] U) (σ (ηM m))) :=
        congrArg H (transportedCoaction_coassoc S E U A e (ηM m))
      _ = Algebra.TensorProduct.map (.id S S)
          ((Algebra.TensorProduct.map (.id B B)
            (Algebra.TensorProduct.includeRight : M →ₐ[R] N)).restrictScalars R)
          (ψ (σ (ηM m))) := (hright (σ (ηM m))).symm
      _ = Algebra.TensorProduct.map (.id S S)
          ((Algebra.TensorProduct.map (.id B B)
            (Algebra.TensorProduct.includeRight : M →ₐ[R] N)).restrictScalars R)
          ((1 : S) ⊗ₜ[R] ρ m) := by rw [hρ]
      _ = _ := rfl
  exact ⟨ρ, (fun m ↦ AlgHom.congr_fun hcounit m),
    (fun m ↦ AlgHom.congr_fun hcoassoc m), hcomparison⟩

end Algebra.Descent
