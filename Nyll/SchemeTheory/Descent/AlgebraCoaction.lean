/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.FaithfullyFlatAlgebra
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.RingTheory.TensorProduct.Maps


/-!
# From tensor-form descent isomorphisms to algebra coactions

An overlap isomorphism is written as `C ⊗[R] B ≃ₐ[B] B ⊗[R] C`.
Its diagonal normalization is an equality after the two multiplication maps.
Its triple cocycle compares two explicit maps from `C ⊗[R] (B ⊗[R] B)`
to `B ⊗[R] (B ⊗[R] C)`, using the tensor associator and exchanges of factors.
Evaluating these genuine overlap laws on `c ⊗ 1` and `c ⊗ 1 ⊗ 1` gives
the counit and coassociativity of the native scalar-extension comonad.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Algebra.Descent

section Tensor

variable (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

/-- The coaction extracted from the actual overlap isomorphism. -/
def tensorCoaction (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C) : C →ₐ[B] B ⊗[R] C :=
  θ.toAlgHom.comp Algebra.TensorProduct.includeLeft

@[simp]
theorem tensorCoaction_apply (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C) (c : C) :
    tensorCoaction R B C θ c = θ (c ⊗ₜ[R] (1 : B)) := rfl

/-- Restricting the source of the overlap comparison to the diagonal. -/
def tensorSourceDiagonal : C ⊗[R] B →ₐ[B] C :=
  Algebra.TensorProduct.lift (.id B C) (IsScalarTower.toAlgHom R B C)
    (fun _ _ ↦ Commute.all _ _)

/-- Restricting the target of the overlap comparison to the diagonal. -/
def tensorTargetDiagonal : B ⊗[R] C →ₐ[B] C :=
  Algebra.TensorProduct.lift (Algebra.ofId B C) (.id R C)
    (fun _ _ ↦ Commute.all _ _)

/-- The overlap comparison on the first two of three coordinates. -/
def tensorFirstTransition (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C) :
    C ⊗[R] (B ⊗[R] B) →ₐ[R] B ⊗[R] (C ⊗[R] B) :=
  (Algebra.TensorProduct.assoc R R R B C B).toAlgHom.comp
    ((Algebra.TensorProduct.map (θ.restrictScalars R).toAlgHom (.id R B)).comp
      (Algebra.TensorProduct.assoc R R R C B B).symm.toAlgHom)

/-- The successive first-second and second-third comparisons. -/
def tensorCocycleLeft (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C) :
    C ⊗[R] (B ⊗[R] B) →ₐ[R] B ⊗[R] (B ⊗[R] C) :=
  (Algebra.TensorProduct.map (.id R B) (θ.restrictScalars R).toAlgHom).comp
    (tensorFirstTransition R B C θ)

/-- The direct first-third comparison, leaving the middle coordinate fixed. -/
def tensorCocycleRight (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C) :
    C ⊗[R] (B ⊗[R] B) →ₐ[R] B ⊗[R] (B ⊗[R] C) :=
  (Algebra.TensorProduct.map (.id R B) (Algebra.TensorProduct.comm R C B).toAlgHom).comp
    ((tensorFirstTransition R B C θ).comp
      (Algebra.TensorProduct.map (.id R C) (Algebra.TensorProduct.comm R B B).toAlgHom))

private theorem tensorFirstTransition_one
    (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C) (c : C) :
    tensorFirstTransition R B C θ (c ⊗ₜ[R] ((1 : B) ⊗ₜ[R] (1 : B))) =
      Algebra.TensorProduct.assoc R R R B C B
        (tensorCoaction R B C θ c ⊗ₜ[R] (1 : B)) := by
  simp only [tensorFirstTransition, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    Algebra.TensorProduct.assoc_symm_tmul, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, tensorCoaction_apply]
  rfl

private theorem tensorCocycleLeft_one
    (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C) (c : C) :
    tensorCocycleLeft R B C θ (c ⊗ₜ[R] ((1 : B) ⊗ₜ[R] (1 : B))) =
      Algebra.TensorProduct.map (.id R B) ((tensorCoaction R B C θ).restrictScalars R)
        (tensorCoaction R B C θ c) := by
  rw [tensorCocycleLeft, AlgHom.comp_apply, tensorFirstTransition_one]
  generalize tensorCoaction R B C θ c = z
  induction z using TensorProduct.inductionOn with
  | tmul b c => rfl
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

private theorem tensorCocycleRight_one
    (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C) (c : C) :
    tensorCocycleRight R B C θ (c ⊗ₜ[R] ((1 : B) ⊗ₜ[R] (1 : B))) =
      Algebra.TensorProduct.map (.id R B)
        (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C)
        (tensorCoaction R B C θ c) := by
  simp only [tensorCocycleRight, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, Algebra.TensorProduct.comm_tmul, tensorFirstTransition_one]
  generalize tensorCoaction R B C θ c = z
  induction z using TensorProduct.inductionOn with
  | tmul b c => rfl
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

/-- Diagonal normalization implies the counit identity of the extracted coaction. -/
theorem tensorCoaction_counit
    (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C)
    (hdiag : (tensorTargetDiagonal R B C).comp θ.toAlgHom = tensorSourceDiagonal R B C)
    (c : C) : tensorTargetDiagonal R B C (tensorCoaction R B C θ c) = c := by
  have h := AlgHom.congr_fun hdiag (c ⊗ₜ[R] (1 : B))
  change tensorTargetDiagonal R B C (tensorCoaction R B C θ c) =
    tensorSourceDiagonal R B C (c ⊗ₜ[R] (1 : B)) at h
  simpa only [tensorSourceDiagonal, Algebra.TensorProduct.lift_tmul,
    AlgHom.id_apply, map_one, mul_one] using h

/-- The actual triple cocycle implies coassociativity of the extracted coaction. -/
theorem tensorCoaction_coassoc
    (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C)
    (hcocycle : tensorCocycleLeft R B C θ = tensorCocycleRight R B C θ)
    (c : C) :
    Algebra.TensorProduct.map (.id R B) ((tensorCoaction R B C θ).restrictScalars R)
        (tensorCoaction R B C θ c) =
      Algebra.TensorProduct.map (.id R B)
        (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C)
        (tensorCoaction R B C θ c) :=
  (tensorCocycleLeft_one R B C θ c).symm.trans
    ((AlgHom.congr_fun hcocycle (c ⊗ₜ[R] ((1 : B) ⊗ₜ[R] (1 : B)))).trans
      (tensorCocycleRight_one R B C θ c))

end Tensor

section Native

variable {R B : Type u} [CommRing R] [CommRing B]
variable (f : R →+* B) (C : Type u) [CommRing C] [Algebra B C]

/-- Pointwise counit and coassociativity for an algebra coaction are exactly
the two equations of the native scalar-extension comonad. -/
theorem nativeCoactionAxioms_of_pointwise :
    let : Algebra R B := f.toAlgebra;
    let : Algebra R C := Algebra.compHom C f;
    let : IsScalarTower R B C := IsScalarTower.of_compHom R B C;
    ∀ (ρ : C →ₐ[B] B ⊗[R] C),
      (∀ c : C, tensorTargetDiagonal R B C (ρ c) = c) →
      (∀ c : C,
        Algebra.TensorProduct.map (.id R B) (ρ.restrictScalars R) (ρ c) =
          Algebra.TensorProduct.map (.id R B)
            (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C) (ρ c)) →
      (FaithfullyFlatDescent.coactionLinear f C ρ ≫
          (ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app (ModuleCat.of B C) =
        𝟙 (ModuleCat.of B C)) ∧
      (FaithfullyFlatDescent.coactionLinear f C ρ ≫
          (ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app (ModuleCat.of B C) =
        FaithfullyFlatDescent.coactionLinear f C ρ ≫
          (ModuleCat.extendRestrictScalarsAdj f).toComonad.map
            (FaithfullyFlatDescent.coactionLinear f C ρ)) := by
  intro hRB hRC hTower ρ hcounit hcoassoc
  have hε (z : B ⊗[R] C) :
      (ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app (ModuleCat.of B C) z =
        tensorTargetDiagonal R B C z := by
    induction z using TensorProduct.inductionOn with
    | tmul b c =>
      change b • c = algebraMap B C b * c
      exact Algebra.smul_def b c
    | add x y hx hy =>
      have hadd :=
        ((ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app (ModuleCat.of B C)).hom.map_add x y
      have hsum := hadd.trans (congrArg₂ (· + ·) hx hy)
      change ((ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app
        (ModuleCat.of B C)).hom (x + y) = _
      rw [map_add]
      exact hsum
  have hδ (z : B ⊗[R] C) :
      (ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app (ModuleCat.of B C) z =
        Algebra.TensorProduct.map (.id R B)
          (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C) z := by
    induction z using TensorProduct.inductionOn with
    | tmul b c => rfl
    | add x y hx hy =>
      have hadd :=
        ((ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app (ModuleCat.of B C)).hom.map_add x y
      have hsum := hadd.trans (congrArg₂ (· + ·) hx hy)
      change ((ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app
        (ModuleCat.of B C)).hom (x + y) = _
      rw [map_add]
      exact hsum
  have hmap (z : B ⊗[R] C) :
      (ModuleCat.extendRestrictScalarsAdj f).toComonad.map
          (FaithfullyFlatDescent.coactionLinear f C ρ) z =
        Algebra.TensorProduct.map (.id R B) (ρ.restrictScalars R) z := by
    induction z using TensorProduct.inductionOn with
    | tmul b c => rfl
    | add x y hx hy =>
      have hadd := ((ModuleCat.extendRestrictScalarsAdj f).toComonad.map
        (FaithfullyFlatDescent.coactionLinear f C ρ)).hom.map_add x y
      have hsum := hadd.trans (congrArg₂ (· + ·) hx hy)
      change ((ModuleCat.extendRestrictScalarsAdj f).toComonad.map
        (FaithfullyFlatDescent.coactionLinear f C ρ)).hom (x + y) = _
      rw [map_add]
      exact hsum
  constructor
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change (ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app
      (ModuleCat.of B C) (ρ c) = c
    rw [hε]
    exact hcounit c
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change (ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app
        (ModuleCat.of B C) (ρ c) =
      (ModuleCat.extendRestrictScalarsAdj f).toComonad.map
        (FaithfullyFlatDescent.coactionLinear f C ρ) (ρ c)
    rw [hδ, hmap]
    exact (hcoassoc c).symm

/-- Tensor-form overlap normalization and cocycle give precisely the two
laws of the native scalar-extension comonad, for the constructed coaction. -/
theorem nativeCoactionAxioms :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
    ∀ (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C),
      (tensorTargetDiagonal R B C).comp θ.toAlgHom = tensorSourceDiagonal R B C →
      tensorCocycleLeft R B C θ = tensorCocycleRight R B C θ →
      let ρ := tensorCoaction R B C θ
      (FaithfullyFlatDescent.coactionLinear f C ρ ≫
          (ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app (ModuleCat.of B C) =
        𝟙 (ModuleCat.of B C)) ∧
      (FaithfullyFlatDescent.coactionLinear f C ρ ≫
          (ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app (ModuleCat.of B C) =
        FaithfullyFlatDescent.coactionLinear f C ρ ≫
          (ModuleCat.extendRestrictScalarsAdj f).toComonad.map
            (FaithfullyFlatDescent.coactionLinear f C ρ)) := by
  let : Algebra R B := f.toAlgebra
  let : Algebra R C := Algebra.compHom C f
  let : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  intro θ hdiag hcocycle
  exact nativeCoactionAxioms_of_pointwise f C (tensorCoaction R B C θ)
    (tensorCoaction_counit R B C θ hdiag)
    (tensorCoaction_coassoc R B C θ hcocycle)

/-- A genuine tensor-form descent isomorphism with its ordinary overlap laws
is effective: the invariant subalgebra recovers the given algebra after base change. -/
def tensorDescentEquiv (hf : f.FaithfullyFlat) :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
    (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C) →
      (tensorTargetDiagonal R B C).comp θ.toAlgHom = tensorSourceDiagonal R B C →
      tensorCocycleLeft R B C θ = tensorCocycleRight R B C θ →
      B ⊗[R] FaithfullyFlatDescent.invariants f C (tensorCoaction R B C θ) ≃ₐ[B] C := by
  letI : Algebra R B := f.toAlgebra
  letI : Algebra R C := Algebra.compHom C f
  letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  intro θ hdiag hcocycle
  exact FaithfullyFlatDescent.invariantsBaseChangeEquiv f C hf (tensorCoaction R B C θ)
    (nativeCoactionAxioms f C θ hdiag hcocycle).1
    (nativeCoactionAxioms f C θ hdiag hcocycle).2

end Native

end Algebra.Descent
