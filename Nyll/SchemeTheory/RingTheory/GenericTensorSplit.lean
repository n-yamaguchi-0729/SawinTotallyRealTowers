/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.IsTensorProduct


/-!
# A split generic tensor in the original scalar-extension orientation

Mathlib's pushout cancellation identifies `(K ⊗[R] S) ⊗[K] B` with
`S ⊗[R] B` as S-algebras, using the canonical S action on the right factor
of `K ⊗[R] S`. A supplied splitting then gives an actual splitting into
copies of `S ⊗[R] K`, with explicit formulas for both directions.
-/

noncomputable section

namespace SchemeTheory

open scoped TensorProduct

universe u v

variable (R K S B : Type u)
  [CommRing R] [CommRing K] [CommRing S] [CommRing B]
  [Algebra R K] [Algebra R S] [Algebra R B] [Algebra K B]
  [IsScalarTower R K B]

/-- Cancel the actual K-base change, preserving its literal ring maps. -/
def genericTensorCancelRingEquiv :
    ((K ⊗[R] S) ⊗[K] B) ≃+* (S ⊗[R] B) := by
  letI : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  exact (Algebra.IsPushout.cancelBaseChangeAlg R S K (K ⊗[R] S) B).toRingEquiv

/-- The cancellation comparison on a double pure tensor. -/
theorem genericTensorCancelRingEquiv_tmul (k : K) (s : S) (b : B) :
    genericTensorCancelRingEquiv R K S B ((k ⊗ₜ[R] s) ⊗ₜ[K] b) =
      s ⊗ₜ[R] (k • b) := by
  let : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  change Algebra.IsPushout.cancelBaseChangeAlg R S K (K ⊗[R] S) B
    ((k ⊗ₜ[R] s) ⊗ₜ[K] b) = s ⊗ₜ[R] (k • b)
  apply (Algebra.IsPushout.cancelBaseChangeAlg R S K (K ⊗[R] S) B).symm.injective
  rw [AlgEquiv.symm_apply_apply, Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul]
  change ((k ⊗ₜ[R] s) ⊗ₜ[K] b) = ((1 : K) ⊗ₜ[R] s) ⊗ₜ[K] (k • b)
  simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The inverse comparison retains both original factors. -/
theorem genericTensorCancelRingEquiv_symm_tmul (s : S) (b : B) :
    (genericTensorCancelRingEquiv R K S B).symm (s ⊗ₜ[R] b) =
      ((1 : K) ⊗ₜ[R] s) ⊗ₜ[K] b := by
  let : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  exact Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul R S K (K ⊗[R] S) B s b

/-- Transport an actual splitting over the left generic fiber into the
original scalar-extension orientation used by integral-closure descent. -/
def genericTensorSplitEquiv (ι : Type v)
    (e : ((K ⊗[R] S) ⊗[K] B) ≃ₐ[K ⊗[R] S] (ι → K ⊗[R] S)) :
    (S ⊗[R] B) ≃ₐ[S] (ι → S ⊗[R] K) := by
  letI : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let eS : ((K ⊗[R] S) ⊗[K] B) ≃ₐ[S] (S ⊗[R] B) :=
    Algebra.IsPushout.cancelBaseChangeAlg R S K (K ⊗[R] S) B
  exact eS.symm.trans ((e.restrictScalars S).trans
    (AlgEquiv.piCongrRight (fun _ : ι => (Algebra.TensorProduct.commRight R S K).symm)))

/-- The transported forward map is the supplied splitting, followed by the
literal commutation of each generic-fiber factor. -/
theorem genericTensorSplitEquiv_tmul (ι : Type v)
    (e : ((K ⊗[R] S) ⊗[K] B) ≃ₐ[K ⊗[R] S] (ι → K ⊗[R] S))
    (s : S) (b : B) (i : ι) :
    genericTensorSplitEquiv R K S B ι e (s ⊗ₜ[R] b) i =
      Algebra.TensorProduct.comm R K S (e (((1 : K) ⊗ₜ[R] s) ⊗ₜ[K] b) i) := by
  change Algebra.TensorProduct.comm R K S
    (e ((genericTensorCancelRingEquiv R K S B).symm (s ⊗ₜ[R] b)) i) = _
  rw [genericTensorCancelRingEquiv_symm_tmul]

/-- The transported inverse applies the supplied inverse to the literal
commuted coordinates, then applies the constructed cancellation map. -/
theorem genericTensorSplitEquiv_symm_apply (ι : Type v)
    (e : ((K ⊗[R] S) ⊗[K] B) ≃ₐ[K ⊗[R] S] (ι → K ⊗[R] S))
    (y : ι → S ⊗[R] K) :
    (genericTensorSplitEquiv R K S B ι e).symm y =
      genericTensorCancelRingEquiv R K S B
        (e.symm (fun i => Algebra.TensorProduct.comm R S K (y i))) := by
  rfl

end SchemeTheory
