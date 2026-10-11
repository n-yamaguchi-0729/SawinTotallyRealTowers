/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight


/-!
# The module equalizer for faithfully flat base change

This file develops the degree-zero part of faithfully flat descent for
modules.  The first step is the split case: if an algebra admits an algebra
section, then the usual Amitsur pair remains exact after tensoring with an
arbitrary module.
-/

@[expose] public noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- The contraction of `S ⊗[R] M` induced by an algebra section `S →ₐ[R] R`. -/
private def tensorProductCounitOfSection (g : S →ₐ[R] R) :
    S ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap ∘ₗ
    TensorProduct.map g.toLinearMap (LinearMap.id : M →ₗ[R] M)

@[simp]
private theorem tensorProductCounitOfSection_tmul
    (g : S →ₐ[R] R) (s : S) (m : M) :
    tensorProductCounitOfSection g (s ⊗ₜ[R] m) = g s • m := by
  simp [tensorProductCounitOfSection]

/-- Apply an algebra section to the first algebra factor of
`(S ⊗[R] S) ⊗[R] M`. -/
private def tensorProductFirstCounitOfSection (g : S →ₐ[R] R) :
    (S ⊗[R] S) ⊗[R] M →ₗ[R] S ⊗[R] M :=
  ((TensorProduct.lid R S).toLinearMap ∘ₗ
      TensorProduct.map g.toLinearMap (LinearMap.id : S →ₗ[R] S)).rTensor M

@[simp]
private theorem tensorProductFirstCounitOfSection_tmul
    (g : S →ₐ[R] R) (s t : S) (m : M) :
    tensorProductFirstCounitOfSection g ((s ⊗ₜ[R] t) ⊗ₜ[R] m) =
      (g s • t) ⊗ₜ[R] m := by
  simp [tensorProductFirstCounitOfSection]

/-- If `S` admits an `R`-algebra section, then the module-valued Amitsur
pair is exact for every `R`-module `M`.

No flatness assumption on `M` is needed.  This split calculation is the
contracting-homotopy input used in faithfully flat descent. -/
theorem tensorProduct_exact_of_section (g : S →ₐ[R] R) :
    Function.Exact
      (TensorProduct.mk R S M 1)
      ((Algebra.TensorProduct.includeLeftSubRight R S).rTensor M) := by
  intro x
  constructor
  · intro hx
    refine ⟨tensorProductCounitOfSection g x, ?_⟩
    have hcontract := congrArg (tensorProductFirstCounitOfSection g) hx
    rw [map_zero] at hcontract
    have hidentity : ∀ y : S ⊗[R] M,
        tensorProductFirstCounitOfSection g
            (((Algebra.TensorProduct.includeLeftSubRight R S).rTensor M) y) =
          1 ⊗ₜ[R] tensorProductCounitOfSection g y - y := by
      intro y
      induction y using TensorProduct.inductionOn with
      | add x y hx hy => simp [hx, hy, TensorProduct.tmul_add, sub_add_sub_comm]
      | tmul s m =>
          simp only [LinearMap.rTensor_tmul,
            Algebra.TensorProduct.includeLeftSubRight_apply,
            TensorProduct.sub_tmul, map_sub,
            tensorProductFirstCounitOfSection_tmul,
            tensorProductCounitOfSection_tmul]
          rw [map_one, one_smul]
          congr 1
          rw [← TensorProduct.smul_tmul]
    rw [hidentity x] at hcontract
    exact sub_eq_zero.mp hcontract
  · rintro ⟨m, rfl⟩
    simp [Algebra.TensorProduct.includeLeftSubRight_apply]

/-- Multiplication of the two algebra factors after base change. -/
private def tensorProductBaseChangeCounit :
    S ⊗[R] (S ⊗[R] M) →ₗ[R] S ⊗[R] M :=
  ((Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toLinearMap.rTensor M) ∘ₗ
    (TensorProduct.assoc R S S M).symm.toLinearMap

@[simp]
private theorem tensorProductBaseChangeCounit_tmul
    (a s : S) (m : M) :
    tensorProductBaseChangeCounit (a ⊗ₜ[R] (s ⊗ₜ[R] m)) =
      (a * s) ⊗ₜ[R] m := by
  simp [tensorProductBaseChangeCounit]

/-- Multiply the first two algebra factors in
`S ⊗ ((S ⊗ S) ⊗ M)`, leaving the third algebra factor untouched. -/
private def tensorProductBaseChangeFirstMultiplication :
    S ⊗[R] ((S ⊗[R] S) ⊗[R] M) →ₗ[R] S ⊗[R] (S ⊗[R] M) :=
  (TensorProduct.assoc R S S M).toLinearMap ∘ₗ
    ((((Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toLinearMap.rTensor S) ∘ₗ
      (TensorProduct.assoc R S S S).symm.toLinearMap).rTensor M) ∘ₗ
    (TensorProduct.assoc R S (S ⊗[R] S) M).symm.toLinearMap

@[simp]
private theorem tensorProductBaseChangeFirstMultiplication_tmul
    (a s t : S) (m : M) :
    tensorProductBaseChangeFirstMultiplication
        (a ⊗ₜ[R] ((s ⊗ₜ[R] t) ⊗ₜ[R] m)) =
      (a * s) ⊗ₜ[R] (t ⊗ₜ[R] m) := by
  simp [tensorProductBaseChangeFirstMultiplication]

/-- Faithfully flat module descent in degree zero: for any faithfully flat
`R`-algebra `S` and any `R`-module `M`, the canonical Amitsur pair

`M → S ⊗[R] M → (S ⊗[R] S) ⊗[R] M`

is exact.  In particular, `M` is the equalizer of the two pullbacks of
`S ⊗[R] M` to `S ⊗[R] S`. -/
theorem tensorProduct_exact_of_faithfullyFlat
    [Module.FaithfullyFlat R S] :
    Function.Exact
      (TensorProduct.mk R S M 1)
      ((Algebra.TensorProduct.includeLeftSubRight R S).rTensor M) := by
  apply Module.FaithfullyFlat.lTensor_reflects_exact R S
  intro x
  constructor
  · intro hx
    refine ⟨tensorProductBaseChangeCounit x, ?_⟩
    have hcontract := congrArg tensorProductBaseChangeFirstMultiplication hx
    rw [map_zero] at hcontract
    have hidentity : ∀ y : S ⊗[R] (S ⊗[R] M),
        tensorProductBaseChangeFirstMultiplication
            ((((Algebra.TensorProduct.includeLeftSubRight R S).rTensor M).lTensor S) y) =
          ((TensorProduct.mk R S M 1).lTensor S)
              (tensorProductBaseChangeCounit y) - y := by
      intro y
      induction y using TensorProduct.inductionOn with
      | add x y hx hy => simp [hx, hy, sub_add_sub_comm]
      | tmul a y =>
          induction y using TensorProduct.inductionOn with
          | add x y hx hy =>
              simp only [TensorProduct.tmul_add, map_add]
              rw [hx, hy]
              abel
          | tmul s m =>
              simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
                Algebra.TensorProduct.includeLeftSubRight_apply,
                TensorProduct.sub_tmul, TensorProduct.tmul_sub, map_sub,
                tensorProductBaseChangeFirstMultiplication_tmul,
                tensorProductBaseChangeCounit_tmul]
              simp
    rw [hidentity x] at hcontract
    exact sub_eq_zero.mp hcontract
  · rintro ⟨y, rfl⟩
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul s m =>
        simp [Algebra.TensorProduct.includeLeftSubRight_apply]

/-- Pull an extended module back along the left projection
`S ⇉ S ⊗[R] S`. -/
def tensorProductDescentLeft :
    S ⊗[R] M →ₗ[R] (S ⊗[R] S) ⊗[R] M :=
  (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S).toLinearMap.rTensor M

/-- Pull an extended module back along the right projection
`S ⇉ S ⊗[R] S`. -/
def tensorProductDescentRight :
    S ⊗[R] M →ₗ[R] (S ⊗[R] S) ⊗[R] M :=
  (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toLinearMap.rTensor M

@[simp]
theorem tensorProductDescentLeft_tmul (s : S) (m : M) :
    tensorProductDescentLeft (s ⊗ₜ[R] m) =
      (s ⊗ₜ[R] 1) ⊗ₜ[R] m :=
  rfl

@[simp]
theorem tensorProductDescentRight_tmul (s : S) (m : M) :
    tensorProductDescentRight (s ⊗ₜ[R] m) =
      (1 ⊗ₜ[R] s) ⊗ₜ[R] m :=
  rfl

/-- The canonical map from an `R`-module to the equalizer of its two
pullbacks from `S` to `S ⊗[R] S`. -/
def tensorProductEqualizerMap :
    M →ₗ[R] LinearMap.eqLocus
      (tensorProductDescentLeft (R := R) (S := S) (M := M))
      (tensorProductDescentRight (R := R) (S := S) (M := M)) :=
  LinearMap.codRestrict _ (TensorProduct.mk R S M 1) (by
    intro m
    simp [tensorProductDescentLeft, tensorProductDescentRight])

@[simp]
theorem tensorProductEqualizerMap_coe (m : M) :
    (tensorProductEqualizerMap (R := R) (S := S) (M := M) m : S ⊗[R] M) =
      1 ⊗ₜ[R] m :=
  rfl

/-- Faithfully flat descent identifies an `R`-module with the equalizer of
the two canonical pullback maps from `S ⊗[R] M` to
`(S ⊗[R] S) ⊗[R] M`. -/
noncomputable def tensorProductEqualizerEquiv
    [Module.FaithfullyFlat R S] :
    M ≃ₗ[R] LinearMap.eqLocus
      (tensorProductDescentLeft (R := R) (S := S) (M := M))
      (tensorProductDescentRight (R := R) (S := S) (M := M)) :=
  LinearEquiv.ofBijective tensorProductEqualizerMap <| by
    constructor
    · intro m n hmn
      apply Module.FaithfullyFlat.tensorProduct_mk_injective
        (A := R) (B := S) M
      exact congrArg Subtype.val hmn
    · rintro ⟨x, hx⟩
      have hxzero :
          ((Algebra.TensorProduct.includeLeftSubRight R S).rTensor M) x = 0 := by
        rw [Algebra.TensorProduct.includeLeftSubRight, LinearMap.rTensor_sub]
        exact sub_eq_zero.mpr hx
      obtain ⟨m, hm⟩ :=
        (tensorProduct_exact_of_faithfullyFlat (R := R) (S := S) (M := M) x).mp hxzero
      exact ⟨m, Subtype.ext hm⟩

@[simp]
theorem tensorProductEqualizerEquiv_apply
    [Module.FaithfullyFlat R S] (m : M) :
    (tensorProductEqualizerEquiv (R := R) (S := S) (M := M) m : S ⊗[R] M) =
      1 ⊗ₜ[R] m :=
  rfl

end EtaleFundamentalGroups

end
