/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.AlgebraCoaction
public import Nyll.SchemeTheory.Descent.AffineAlgebraCoaction
public import Nyll.SchemeTheory.Descent.FaithfullyFlatAlgebra
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Equivariance of effective algebra descent

The actual map from the scalar extension of the invariant subalgebra intertwines
the canonical scalar-extension coaction and the given coaction. This identity
already holds without flatness or the coaction laws. For genuine descent data,
it applies to the constructed base-change equivalence itself.

When an overlap isomorphism preserves both coordinates of the overlap base,
the same map also intertwines the full overlap isomorphism with the standard
comparison on a scalar extension. This equality can be transported through
`Spec` to compare the corresponding geometric descent data.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Algebra.FaithfullyFlatDescent

variable {R B : Type u} [CommRing R] [CommRing B]
variable (f : R →+* B) (C : Type u) [CommRing C] [Algebra B C]

/-- On an invariant pure tensor, the canonical base-change map preserves the coaction. -/
theorem coaction_invariantsBaseChange_tmul
    (ρ :
      letI : Algebra R B := f.toAlgebra
      letI : Algebra R C := Algebra.compHom C f
      C →ₐ[B] B ⊗[R] C)
    (b : B) (z : invariants f C ρ) :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    ρ (invariantsBaseChange f C ρ (b ⊗ₜ[R] z)) = b ⊗ₜ[R] (z : C) := by
  let : Algebra R B := f.toAlgebra
  let : Algebra R C := Algebra.compHom C f
  have hz : ρ (z : C) = (1 : B) ⊗ₜ[R] (z : C) := z.property
  rw [invariantsBaseChange_tmul, map_mul, ρ.commutes, hz,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul, Algebra.algebraMap_self_apply]

/-- The canonical base-change map is a morphism for the scalar-extension coactions. -/
theorem invariantsBaseChange_coaction
    (ρ :
      letI : Algebra R B := f.toAlgebra
      letI : Algebra R C := Algebra.compHom C f
      C →ₐ[B] B ⊗[R] C) :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
    ρ.comp (invariantsBaseChange f C ρ) =
      (Algebra.TensorProduct.map (.id B B)
        ((invariantsBaseChange f C ρ).restrictScalars R)).comp
          (Algebra.TensorProduct.map (.id B B)
            (Algebra.TensorProduct.includeRight : invariants f C ρ →ₐ[R]
              B ⊗[R] invariants f C ρ)) := by
  let : Algebra R B := f.toAlgebra
  let : Algebra R C := Algebra.compHom C f
  let : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b z =>
    change ρ (invariantsBaseChange f C ρ (b ⊗ₜ[R] z)) =
      b ⊗ₜ[R] invariantsBaseChange f C ρ ((1 : B) ⊗ₜ[R] z)
    rw [coaction_invariantsBaseChange_tmul, invariantsBaseChange_tmul, map_one, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The effective descent equivalence, with its actual underlying map, preserves coactions. -/
theorem invariantsBaseChangeEquiv_coaction (hf : f.FaithfullyFlat)
    (ρ :
      letI : Algebra R B := f.toAlgebra
      letI : Algebra R C := Algebra.compHom C f
      C →ₐ[B] B ⊗[R] C)
    (hε : coactionLinear f C ρ ≫
        (ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app (ModuleCat.of B C) =
      𝟙 (ModuleCat.of B C))
    (hδ : coactionLinear f C ρ ≫
        (ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app (ModuleCat.of B C) =
      coactionLinear f C ρ ≫
        (ModuleCat.extendRestrictScalarsAdj f).toComonad.map (coactionLinear f C ρ)) :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
    let e := invariantsBaseChangeEquiv f C hf ρ hε hδ
    ρ.comp e.toAlgHom =
      (Algebra.TensorProduct.map (.id B B) (e.restrictScalars R).toAlgHom).comp
        (Algebra.TensorProduct.map (.id B B)
          (Algebra.TensorProduct.includeRight : invariants f C ρ →ₐ[R]
            B ⊗[R] invariants f C ρ)) :=
  invariantsBaseChange_coaction f C ρ

end Algebra.FaithfullyFlatDescent

namespace Algebra.Descent

/-- The standard overlap comparison on an algebra obtained by scalar extension. -/
def standardTensorOverlap (R B D : Type u) [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D] :
    (B ⊗[R] D) ⊗[R] B ≃ₐ[B] B ⊗[R] (B ⊗[R] D) :=
  (Algebra.TensorProduct.assoc R R B B D B).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
      (Algebra.TensorProduct.comm R D B))

/-- The standard comparison leaves the first base coordinate fixed and exchanges
the invariant and second base coordinates. -/
theorem standardTensorOverlap_tmul (R B D : Type u) [CommRing R] [CommRing B]
    [CommRing D] [Algebra R B] [Algebra R D] (b b' : B) (d : D) :
    standardTensorOverlap R B D ((b ⊗ₜ[R] d) ⊗ₜ[R] b') = b ⊗ₜ[R] (b' ⊗ₜ[R] d) := rfl

variable {R B : Type u} [CommRing R] [CommRing B]
variable (f : R →+* B) (C : Type u) [CommRing C] [Algebra B C]

/-- The original overlap comparison has the canonical formula on an invariant tensor,
provided it preserves both coordinates of the overlap base. -/
theorem invariantsBaseChange_overlap_tmul :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
    ∀ (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C),
      θ.toAlgHom.comp (affineOverlapSourceBase R B C) = affineOverlapTargetBase R B C →
      ∀ (b b' : B) (z : FaithfullyFlatDescent.invariants f C (tensorCoaction R B C θ)),
        θ (FaithfullyFlatDescent.invariantsBaseChange f C (tensorCoaction R B C θ)
            (b ⊗ₜ[R] z) ⊗ₜ[R] b') =
          b ⊗ₜ[R] FaithfullyFlatDescent.invariantsBaseChange f C (tensorCoaction R B C θ)
            (b' ⊗ₜ[R] z) := by
  let : Algebra R B := f.toAlgebra
  let : Algebra R C := Algebra.compHom C f
  let : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  intro θ hbase b b' z
  have hright : θ ((1 : C) ⊗ₜ[R] b') = (1 : B) ⊗ₜ[R] algebraMap B C b' := by
    have h := AlgHom.congr_fun hbase ((1 : B) ⊗ₜ[R] b')
    simpa only [AlgHom.comp_apply, affineOverlapSourceBase, affineOverlapTargetBase,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply,
      IsScalarTower.toAlgHom_apply, AlgEquiv.toAlgHom_apply] using h
  let e := FaithfullyFlatDescent.invariantsBaseChange f C (tensorCoaction R B C θ)
  have hleft : θ (e (b ⊗ₜ[R] z) ⊗ₜ[R] (1 : B)) = b ⊗ₜ[R] (z : C) :=
    FaithfullyFlatDescent.coaction_invariantsBaseChange_tmul f C
      (tensorCoaction R B C θ) b z
  change θ (e (b ⊗ₜ[R] z) ⊗ₜ[R] b') = b ⊗ₜ[R] e (b' ⊗ₜ[R] z)
  calc
    θ (e (b ⊗ₜ[R] z) ⊗ₜ[R] b') =
        θ ((e (b ⊗ₜ[R] z) ⊗ₜ[R] (1 : B)) * ((1 : C) ⊗ₜ[R] b')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = (b ⊗ₜ[R] (z : C)) * ((1 : B) ⊗ₜ[R] algebraMap B C b') := by
      rw [map_mul, hleft, hright]
    _ = b ⊗ₜ[R] e (b' ⊗ₜ[R] z) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      change b ⊗ₜ[R] ((z : C) * algebraMap B C b') =
        b ⊗ₜ[R] (algebraMap B C b' * (z : C))
      rw [mul_comm]

/-- The full overlap square commutes for the canonical map out of the invariant algebra. -/
theorem invariantsBaseChange_overlap :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
    ∀ (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C),
      θ.toAlgHom.comp (affineOverlapSourceBase R B C) = affineOverlapTargetBase R B C →
      let D := FaithfullyFlatDescent.invariants f C (tensorCoaction R B C θ)
      let e := FaithfullyFlatDescent.invariantsBaseChange f C (tensorCoaction R B C θ)
      θ.toAlgHom.comp (Algebra.TensorProduct.map e (.id R B)) =
        (Algebra.TensorProduct.map (.id B B) (e.restrictScalars R)).comp
          (standardTensorOverlap R B D).toAlgHom := by
  let : Algebra R B := f.toAlgebra
  let : Algebra R C := Algebra.compHom C f
  let : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  intro θ hbase
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul x b' =>
    induction x using TensorProduct.inductionOn with
    | tmul b z =>
      exact invariantsBaseChange_overlap_tmul f C θ hbase b b' z
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The actual effective descent equivalence intertwines the entire tensor overlap datum. -/
theorem tensorDescentEquiv_overlap (hf : f.FaithfullyFlat) :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
    ∀ (θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C)
      (hdiag : (tensorTargetDiagonal R B C).comp θ.toAlgHom = tensorSourceDiagonal R B C)
      (hcocycle : tensorCocycleLeft R B C θ = tensorCocycleRight R B C θ),
      θ.toAlgHom.comp (affineOverlapSourceBase R B C) = affineOverlapTargetBase R B C →
      let D := FaithfullyFlatDescent.invariants f C (tensorCoaction R B C θ)
      let e := tensorDescentEquiv f C hf θ hdiag hcocycle
      θ.toAlgHom.comp (Algebra.TensorProduct.map e.toAlgHom (.id R B)) =
        (Algebra.TensorProduct.map (.id B B) (e.restrictScalars R).toAlgHom).comp
          (standardTensorOverlap R B D).toAlgHom := by
  let : Algebra R B := f.toAlgebra
  let : Algebra R C := Algebra.compHom C f
  let : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  intro θ hdiag hcocycle hbase
  exact invariantsBaseChange_overlap f C θ hbase

end Algebra.Descent
