/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.AlgebraCoaction
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Transporting the canonical algebra coaction

A concrete scalar-extension equivalence gives a concrete coaction. Its two
laws follow from the pure-tensor formula for the canonical coaction. These
are the upper coactions used when descending a finite radicial local model.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Algebra.Descent

section Transport

variable (S E U A : Type u) [CommRing S] [CommRing E] [CommRing U] [CommRing A]
variable [Algebra S E] [Algebra S U] [Algebra E U] [IsScalarTower S E U]
variable [Algebra S A]

/-- The canonical coaction on a scalar extension. -/
def canonicalCoaction : E ⊗[S] A →ₐ[E] E ⊗[S] (E ⊗[S] A) :=
  Algebra.TensorProduct.map (.id E E) Algebra.TensorProduct.includeRight

/-- The actual coaction obtained by transporting the canonical coaction along
the chosen scalar-extension equivalence. -/
def transportedCoaction (e : U ≃ₐ[E] E ⊗[S] A) : U →ₐ[E] E ⊗[S] U :=
  (Algebra.TensorProduct.map (.id E E) (e.symm.restrictScalars S).toAlgHom).comp
    ((canonicalCoaction S E A).comp e.toAlgHom)

theorem transportedCoaction_symm_tmul (e : U ≃ₐ[E] E ⊗[S] A) (b : E) (a : A) :
    transportedCoaction S E U A e (e.symm (b ⊗ₜ[S] a)) =
      b ⊗ₜ[S] e.symm ((1 : E) ⊗ₜ[S] a) := by
  simp only [transportedCoaction, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    e.apply_symm_apply, canonicalCoaction, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply,
    AlgEquiv.restrictScalars_apply]

/-- The defining comparison with the actual canonical coaction. -/
theorem transportedCoaction_comparison (e : U ≃ₐ[E] E ⊗[S] A) (x : U) :
    Algebra.TensorProduct.map (.id E E) (e.restrictScalars S).toAlgHom
        (transportedCoaction S E U A e x) = canonicalCoaction S E A (e x) := by
  change Algebra.TensorProduct.map (.id E E) (e.restrictScalars S).toAlgHom
      (Algebra.TensorProduct.map (.id E E) (e.symm.restrictScalars S).toAlgHom
        (canonicalCoaction S E A (e x))) = canonicalCoaction S E A (e x)
  generalize canonicalCoaction S E A (e x) = z
  induction z using TensorProduct.inductionOn with
  | tmul b y =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgEquiv.toAlgHom_apply, AlgEquiv.restrictScalars_apply, e.apply_symm_apply]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The transported canonical coaction satisfies its actual counit equation. -/
theorem transportedCoaction_counit (e : U ≃ₐ[E] E ⊗[S] A) (x : U) :
    tensorTargetDiagonal S E U (transportedCoaction S E U A e x) = x := by
  obtain ⟨z, rfl⟩ := e.symm.surjective x
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
    apply e.injective
    rw [transportedCoaction_symm_tmul]
    simp only [tensorTargetDiagonal, Algebra.TensorProduct.lift_tmul,
      Algebra.ofId_apply, AlgHom.id_apply, map_mul, e.commutes,
      e.apply_symm_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The transported canonical coaction satisfies coassociativity. -/
theorem transportedCoaction_coassoc (e : U ≃ₐ[E] E ⊗[S] A) (x : U) :
    Algebra.TensorProduct.map (.id E E)
        ((transportedCoaction S E U A e).restrictScalars S)
        (transportedCoaction S E U A e x) =
      Algebra.TensorProduct.map (.id E E)
        (Algebra.TensorProduct.includeRight : U →ₐ[S] E ⊗[S] U)
        (transportedCoaction S E U A e x) := by
  obtain ⟨z, rfl⟩ := e.symm.surjective x
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
    simp only [transportedCoaction_symm_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
  | add z w hz hw => simp only [map_add, hz, hw]

end Transport

section TensorComparison

variable (R S B M : Type u) [CommRing R] [CommRing S] [CommRing B] [CommRing M]
variable [Algebra R S] [Algebra R B] [Algebra R M]

/-- The tensor-product comparison that changes the coefficients of a coaction. -/
def scalarTensorIso :
    (S ⊗[R] B) ⊗[S] (S ⊗[R] M) ≃ₐ[S] S ⊗[R] (B ⊗[R] M) :=
  (Algebra.TensorProduct.tensorTensorTensorComm R R S S S B S M).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid S S)
      (AlgEquiv.refl : (B ⊗[R] M) ≃ₐ[R] B ⊗[R] M))

theorem scalarTensorIso_tmul (s t : S) (b : B) (m : M) :
    scalarTensorIso R S B M ((s ⊗ₜ[R] b) ⊗ₜ[S] (t ⊗ₜ[R] m)) =
      (s * t) ⊗ₜ[R] (b ⊗ₜ[R] m) := by
  simp only [scalarTensorIso, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorTensorTensorComm_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.lid_tmul,
    AlgEquiv.coe_refl, id_eq, smul_eq_mul]

/-- Naturality of the coefficient comparison in the algebra carrying the coaction. -/
theorem scalarTensorIso_natural
    {N : Type u} [CommRing N] [Algebra R N] (g : M →ₐ[R] N)
    (z : (S ⊗[R] B) ⊗[S] (S ⊗[R] M)) :
    Algebra.TensorProduct.map (.id S S)
        ((Algebra.TensorProduct.map (.id B B) g).restrictScalars R)
        (scalarTensorIso R S B M z) =
      scalarTensorIso R S B N
        (Algebra.TensorProduct.map (.id S (S ⊗[R] B))
          (Algebra.TensorProduct.map (.id S S) g) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    induction x using TensorProduct.inductionOn with
    | tmul s b =>
      induction y using TensorProduct.inductionOn with
      | tmul t m =>
        simp only [scalarTensorIso_tmul, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, AlgHom.restrictScalars_apply]
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The unit inclusion is preserved by the coefficient comparison. -/
theorem scalarTensorIso_one_tmul (z : S ⊗[R] M) :
    scalarTensorIso R S B M ((1 : S ⊗[R] B) ⊗ₜ[S] z) =
      Algebra.TensorProduct.map (.id S S)
        (Algebra.TensorProduct.includeRight : M →ₐ[R] B ⊗[R] M) z := by
  induction z using TensorProduct.inductionOn with
  | tmul s m =>
    change scalarTensorIso R S B M
      (((1 : S) ⊗ₜ[R] (1 : B)) ⊗ₜ[S] (s ⊗ₜ[R] m)) = _
    simp only [scalarTensorIso_tmul, one_mul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

end TensorComparison

end Algebra.Descent
