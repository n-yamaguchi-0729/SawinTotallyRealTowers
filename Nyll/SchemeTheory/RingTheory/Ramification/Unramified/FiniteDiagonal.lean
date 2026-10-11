/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Unramified.Finite

/-!
# The diagonal factor of a finite formally unramified algebra

For a finite formally unramified `R`-algebra `S`, the canonical separability
element `Algebra.FormallyUnramified.elem R S` cuts out the diagonal component
of `S \otimes_R S`.  After inverting this element, multiplication identifies
that component with `S` itself as an `S`-algebra.

The proof first derives the idempotence of the separability element from its
defining switching and multiplication identities.  It then uses the universal
property of `Localization.Away` and proves bijectivity by exhibiting `S`, with
the multiplication algebra structure, as a second localization away from the
same element.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Algebra.FormallyUnramified R S]

/-- Multiplication by the separability element turns every tensor into the
left-factor image of its product. -/
lemma mul_formallyUnramifiedElem_eq_lmul_tmul_one_mul
    (x : S ⊗[R] S) :
    x * Algebra.FormallyUnramified.elem R S =
      ((Algebra.TensorProduct.lmul' R x) ⊗ₜ[R] (1 : S)) *
        Algebra.FormallyUnramified.elem R S := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
      rw [show x ⊗ₜ[R] y = (x ⊗ₜ[R] (1 : S)) * ((1 : S) ⊗ₜ[R] y) by simp]
      rw [mul_assoc, Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) y]
      simp [← mul_assoc]
  | add x y hx hy =>
      simp only [add_mul, map_add, TensorProduct.add_tmul, hx, hy]

/-- The canonical separability element of a finite formally unramified algebra
is idempotent. -/
lemma formallyUnramifiedElem_isIdempotentElem :
    IsIdempotentElem (Algebra.FormallyUnramified.elem R S) := by
  calc
    Algebra.FormallyUnramified.elem R S * Algebra.FormallyUnramified.elem R S =
        ((Algebra.TensorProduct.lmul' R
          (Algebra.FormallyUnramified.elem R S)) ⊗ₜ[R] (1 : S)) *
          Algebra.FormallyUnramified.elem R S :=
      mul_formallyUnramifiedElem_eq_lmul_tmul_one_mul
        (R := R) (S := S) (Algebra.FormallyUnramified.elem R S)
    _ = Algebra.FormallyUnramified.elem R S := by
      rw [Algebra.FormallyUnramified.lmul_elem]
      rw [← Algebra.TensorProduct.one_def, one_mul]

/-- Multiplication, extended across the Away localization at the separability
element. -/
noncomputable def finiteUnramifiedDiagonalAwayMul :
    Localization.Away (Algebra.FormallyUnramified.elem R S) →ₐ[S] S :=
  IsLocalization.Away.liftAlgHom
    (Algebra.FormallyUnramified.elem R S)
    (f := Algebra.TensorProduct.lmul'' R)
    (by
      change IsUnit
        (Algebra.TensorProduct.lmul' R (Algebra.FormallyUnramified.elem R S))
      rw [Algebra.FormallyUnramified.lmul_elem]
      exact isUnit_one)

@[simp]
lemma finiteUnramifiedDiagonalAwayMul_algebraMap (x : S ⊗[R] S) :
    finiteUnramifiedDiagonalAwayMul (R := R) (S := S)
        (algebraMap (S ⊗[R] S)
          (Localization.Away (Algebra.FormallyUnramified.elem R S)) x) =
      Algebra.TensorProduct.lmul' R x := by
  simp [finiteUnramifiedDiagonalAwayMul]
  rfl

/-- The multiplication map from the diagonal Away factor is bijective. -/
lemma finiteUnramifiedDiagonalAwayMul_bijective :
    Function.Bijective (finiteUnramifiedDiagonalAwayMul (R := R) (S := S)) := by
  let T := S ⊗[R] S
  let e : T := Algebra.FormallyUnramified.elem R S
  let : Algebra T S :=
    (Algebra.TensorProduct.lmul' R : T →ₐ[R] S).toRingHom.toAlgebra
  let : IsLocalization.Away e S := by
    apply IsLocalization.Away.mk e
    · change IsUnit (Algebra.TensorProduct.lmul' R e)
      dsimp only [e]
      rw [Algebra.FormallyUnramified.lmul_elem]
      exact isUnit_one
    · intro s
      refine ⟨0, s ⊗ₜ[R] (1 : S), ?_⟩
      change s * (Algebra.TensorProduct.lmul' R e) ^ 0 =
        Algebra.TensorProduct.lmul' R (s ⊗ₜ[R] (1 : S))
      simp
    · intro x y hxy
      change Algebra.TensorProduct.lmul' R x =
        Algebra.TensorProduct.lmul' R y at hxy
      refine ⟨1, ?_⟩
      rw [pow_one, mul_comm e x,
        mul_formallyUnramifiedElem_eq_lmul_tmul_one_mul (R := R) (S := S) x,
        mul_comm e y,
        mul_formallyUnramifiedElem_eq_lmul_tmul_one_mul (R := R) (S := S) y,
        hxy]
  apply IsLocalization.bijective (Submonoid.powers e)
    (finiteUnramifiedDiagonalAwayMul (R := R) (S := S)).toRingHom
  apply RingHom.ext
  intro x
  exact finiteUnramifiedDiagonalAwayMul_algebraMap (R := R) (S := S) x

/-- The diagonal factor of `S \otimes_R S` selected by the canonical
separability element is `S` itself. -/
noncomputable def finiteUnramifiedDiagonalAwayEquiv :
    Localization.Away (Algebra.FormallyUnramified.elem R S) ≃ₐ[S] S :=
  AlgEquiv.ofBijective
    (finiteUnramifiedDiagonalAwayMul (R := R) (S := S))
    finiteUnramifiedDiagonalAwayMul_bijective

end EtaleFundamentalGroups
