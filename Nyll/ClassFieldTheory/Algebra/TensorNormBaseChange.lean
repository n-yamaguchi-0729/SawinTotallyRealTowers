/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Determinant norm and scalar extension

For a finite field extension `L / K`, the norm of `y : L` is unchanged by
base change, in the sense that the determinant norm of `1 ⊗ y` over a
commutative `K`-algebra `A` is the image of its field norm over `K`.
This applies to the whole tensor algebra, whether or not it is a field.
-/

@[expose] public section

open scoped TensorProduct

namespace ClassFieldTheory

universe u v w

/-- The determinant norm on `A ⊗[K] L` of a globally defined element is the
base change of its field norm. In particular, no Galois assumption or choice
of a factor of the tensor algebra is required. -/
theorem tensorNorm_includeRight
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [Nontrivial A]
    (y : L) :
    Algebra.norm A
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := L) y) =
      algebraMap K A (Algebra.norm K y) := by
  classical
  let b := Module.Free.chooseBasis K L
  let bA := b.baseChange A
  rw [Algebra.norm_eq_matrix_det bA,
    Algebra.norm_eq_matrix_det b, (algebraMap K A).map_det]
  congr 1
  ext i j
  simp only [Algebra.TensorProduct.includeRight, TensorProduct.AlgebraTensorModule.mk_apply,
    ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, LinearMap.toAddMonoidHom_coe,
    LinearMap.coe_mk, AddHom.coe_mk, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.baseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, RingHom.mapMatrix_apply, Matrix.map_apply, bA, b]

end ClassFieldTheory
