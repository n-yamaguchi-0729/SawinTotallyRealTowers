/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RelativeBasic
public import Mathlib.RingTheory.Norm.Basic

/-!
# Scalar extension of the field norm to the adele algebra
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable section

variable (K L : Type*) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

namespace RelativeIdeleGroup

omit [NumberField L] in
/-- Norm commutes with scalar extension from `K` to the base adele ring. -/
theorem norm_fieldInclusion (x : L) :
    Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (fieldInclusion K L x) =
      algebraMap K (NumberField.AdeleRing (𝓞 K) K)
        (Algebra.norm K x) := by
  classical
  let b := Module.Free.chooseBasis K L
  let bA := b.baseChange
    (NumberField.AdeleRing (𝓞 K) K)
  rw [Algebra.norm_eq_matrix_det bA,
    Algebra.norm_eq_matrix_det b,
    (algebraMap K
      (NumberField.AdeleRing (𝓞 K) K)).map_det]
  congr 1
  ext i j
  simp only [fieldInclusion, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.baseChange_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, RingHom.mapMatrix_apply, Matrix.map_apply,
    bA, b]

end RelativeIdeleGroup
