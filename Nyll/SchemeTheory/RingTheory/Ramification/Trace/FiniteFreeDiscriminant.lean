/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Trace discriminants of finite free algebras

This file develops the linear-algebra input for the dimension-two branch-locus argument.
For a finite free commutative algebra, the trace pairing is onto the module dual exactly when
the discriminant of a basis is a unit.  The statement works over an arbitrary commutative base
ring; no domain, locality, or etaleness hypothesis is used.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Module
open scoped TensorProduct

universe u v w

/-- For a finite basis, surjectivity of the trace-pairing map is equivalent to the
discriminant being a unit. -/
theorem traceForm_surjective_iff_isUnit_discr
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι R S) :
    Function.Surjective (Algebra.traceForm R S) ↔
      IsUnit (Algebra.discr R b) := by
  let M : Matrix ι ι R :=
    LinearMap.toMatrix b b.dualBasis (Algebra.traceForm R S)
  have hM : M = Algebra.traceMatrix R b := by
    ext i j
    simp [M, LinearMap.toMatrix_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, mul_comm]
  have hsurj :
      Function.Surjective (Algebra.traceForm R S) ↔
        Function.Surjective M.mulVec := by
    constructor
    · intro h v
      obtain ⟨x, hx⟩ := h (b.dualBasis.equivFun.symm v)
      refine ⟨b.equivFun x, ?_⟩
      have hmatrix :=
        LinearMap.toMatrix_mulVec_repr b b.dualBasis
          (Algebra.traceForm R S) x
      calc
        M.mulVec (b.equivFun x) =
            b.dualBasis.equivFun ((Algebra.traceForm R S) x) := by
          simpa [M, Basis.equivFun_apply] using hmatrix
        _ = b.dualBasis.equivFun (b.dualBasis.equivFun.symm v) := by
          rw [hx]
        _ = v := b.dualBasis.equivFun.apply_symm_apply v
    · intro h y
      obtain ⟨v, hv⟩ := h (b.dualBasis.equivFun y)
      refine ⟨b.equivFun.symm v, ?_⟩
      apply b.dualBasis.equivFun.injective
      have hmatrix :=
        LinearMap.toMatrix_mulVec_repr b b.dualBasis
          (Algebra.traceForm R S) (b.equivFun.symm v)
      have hmatrix' :
          M.mulVec v =
            b.dualBasis.equivFun
              ((Algebra.traceForm R S) (b.equivFun.symm v)) := by
        change
          M.mulVec (b.equivFun (b.equivFun.symm v)) =
            b.dualBasis.equivFun
              ((Algebra.traceForm R S) (b.equivFun.symm v)) at hmatrix
        simpa only [LinearEquiv.apply_symm_apply] using hmatrix
      exact hmatrix'.symm.trans hv
  rw [hsurj, Matrix.mulVec_surjective_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, Algebra.discr_def, hM]

/-- A unit trace discriminant makes the trace-pairing map injective.  This direction works over
an arbitrary commutative base because the corresponding trace matrix is invertible. -/
theorem traceForm_injective_of_isUnit_discr
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι R S) (hdisc : IsUnit (Algebra.discr R b)) :
    Function.Injective (Algebra.traceForm R S) := by
  let M : Matrix ι ι R :=
    LinearMap.toMatrix b b.dualBasis (Algebra.traceForm R S)
  have hM : M = Algebra.traceMatrix R b := by
    ext i j
    simp [M, LinearMap.toMatrix_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, mul_comm]
  have hMunit : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hM, ← Algebra.discr_def]
    exact hdisc
  intro x y hxy
  apply b.equivFun.injective
  apply Matrix.mulVec_injective_of_isUnit hMunit
  have hx :=
    LinearMap.toMatrix_mulVec_repr b b.dualBasis
      (Algebra.traceForm R S) x
  have hy :=
    LinearMap.toMatrix_mulVec_repr b b.dualBasis
      (Algebra.traceForm R S) y
  change M.mulVec (b.equivFun x) =
    b.dualBasis.equivFun ((Algebra.traceForm R S) x) at hx
  change M.mulVec (b.equivFun y) =
    b.dualBasis.equivFun ((Algebra.traceForm R S) y) at hy
  rw [hx, hy, hxy]

/-- For a finite free algebra, formal unramifiedness makes the trace-pairing map onto the
module dual.  The preimage of a functional is obtained by contracting that functional with
the separability element. -/
theorem traceForm_surjective_of_formallyUnramified
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [_root_.Finite ι]
    (b : Basis ι R S) (h : Algebra.FormallyUnramified R S) :
    Function.Surjective (Algebra.traceForm R S) := by
  let : Module.Free R S := Module.Free.of_basis b
  let : Module.Finite R S := Module.Finite.of_basis b
  let : Algebra.FormallyUnramified R S := h
  let contraction (f : Module.Dual R S) : S ⊗[R] S →ₗ[R] S :=
    TensorProduct.lift ((LinearMap.lsmul R S).comp f)
  let twist (f : Module.Dual R S) : S →ₗ[R] Module.Dual R S :=
    (Algebra.lsmul R R S).toLinearMap.compr₂ f
  let tensorEnd (f : Module.Dual R S) : S ⊗[R] S →ₗ[R] Module.End R S :=
    (dualTensorHom R S S).comp
      (TensorProduct.map (twist f) (LinearMap.id (R := R) (M := S)))
  have htrace (f : Module.Dual R S) (q : S ⊗[R] S) :
      LinearMap.trace R S (tensorEnd f q) =
        f (Algebra.TensorProduct.lmul' R q) := by
    induction q using TensorProduct.inductionOn with
    | tmul x y =>
        rw [show tensorEnd f (x ⊗ₜ[R] y) = (twist f x).smulRight y by
          ext z
          simp [tensorEnd, twist]]
        rw [LinearMap.trace_smulRight]
        simp [twist]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcontract_right (f : Module.Dual R S) (s : S) (q : S ⊗[R] S) :
      contraction f (((1 : S) ⊗ₜ[R] s) * q) = contraction f q * s := by
    induction q using TensorProduct.inductionOn with
    | tmul x y =>
        simp [contraction, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
    | add x y hx hy => simp only [mul_add, map_add, hx, hy, add_mul]
  have hcontract_left (f : Module.Dual R S) (s : S) (q : S ⊗[R] S) :
      contraction f ((s ⊗ₜ[R] (1 : S)) * q) = tensorEnd f q s := by
    induction q using TensorProduct.inductionOn with
    | tmul x y =>
        simp [contraction, tensorEnd, twist, Algebra.TensorProduct.tmul_mul_tmul,
          mul_comm]
    | add x y hx hy => simp only [mul_add, map_add, hx, hy, LinearMap.add_apply]
  have htensorEnd_eq_contraction_twist
      (f : Module.Dual R S) (q : S ⊗[R] S) (s : S) :
      tensorEnd f q s = contraction (twist f s) q := by
    induction q using TensorProduct.inductionOn with
    | tmul x y =>
        simp [contraction, tensorEnd, twist, mul_comm]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  let t : S ⊗[R] S := Algebra.FormallyUnramified.elem R S
  have hlsmul (f : Module.Dual R S) :
      Algebra.lmul R S (contraction f t) = tensorEnd f t := by
    ext s
    have hc := congrArg (contraction f)
      (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) (S := S) s)
    rw [hcontract_right, hcontract_left] at hc
    simpa [Algebra.coe_lmul_eq_mul] using hc
  have htrace_contraction (f : Module.Dual R S) :
      Algebra.trace R S (contraction f t) = f 1 := by
    rw [Algebra.trace_apply, hlsmul, htrace,
      show Algebra.TensorProduct.lmul' R t = 1 from
        Algebra.FormallyUnramified.lmul_elem (R := R) (S := S)]
  intro f
  refine ⟨contraction f t, ?_⟩
  ext s
  rw [Algebra.traceForm_apply]
  have hc := congrArg (contraction f)
    (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) (S := S) s)
  rw [hcontract_right, hcontract_left, htensorEnd_eq_contraction_twist] at hc
  rw [hc, htrace_contraction]
  simp [twist]

/-- Surjectivity of the trace pairing produces the separability element witnessing formal
unramifiedness.  The element is the Casimir tensor associated to a basis and its trace-dual
family; both its multiplication and centrality identities are proved from the trace pairing. -/
theorem formallyUnramified_of_traceForm_surjective
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [_root_.Finite ι]
    (b : Basis ι R S)
    (hsurj : Function.Surjective (Algebra.traceForm R S)) :
    Algebra.FormallyUnramified R S := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Module.Finite R S := Module.Finite.of_basis b
  have hdisc : IsUnit (Algebra.discr R b) :=
    (traceForm_surjective_iff_isUnit_discr b).mp hsurj
  have hinj : Function.Injective (Algebra.traceForm R S) :=
    traceForm_injective_of_isUnit_discr b hdisc
  choose c hc using fun i : ι ↦ hsurj (b.coord i)
  have hdual (i : ι) (x : S) :
      Algebra.trace R S (c i * x) = b.repr x i := by
    have h := LinearMap.congr_fun (hc i) x
    simpa [Algebra.traceForm_apply, Basis.coord_apply] using h
  let t : S ⊗[R] S := ∑ i, c i ⊗ₜ[R] b i
  have ht_lmul : Algebra.TensorProduct.lmul' R t = 1 := by
    apply hinj
    ext x
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
    simp only [t, map_sum, Algebra.TensorProduct.lmul'_apply_tmul,
      Finset.sum_mul, one_mul]
    simp_rw [mul_assoc, hdual]
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
    simp_rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
    congr 1
    funext i
    rw [mul_comm (b i) x]
  refine (Algebra.FormallyUnramified.iff_exists_tensorProduct).mpr
    ⟨t, ?_, ht_lmul⟩
  intro s
  rw [sub_mul, sub_eq_zero]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext j
  simp only [t, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
    map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  apply hinj
  ext x
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
  simp only [Finset.sum_mul, map_sum]
  simp_rw [one_mul,
    TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  have hright (i : ι) :
      Algebra.trace R S ((s * c i) * x) = b.repr (s * x) i := by
    rw [mul_comm s (c i), mul_assoc, hdual]
  simp_rw [smul_mul_assoc, map_smul, hdual, hright]
  calc
    (∑ i, b.repr (s * b i) j • b.repr x i) =
        ∑ i, b.repr x i • b.repr (s * b i) j := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = b.repr (s * x) j := by
      conv_rhs => rw [← b.sum_repr x]
      simp only [Finset.mul_sum, Algebra.mul_smul_comm, map_sum, map_smul]
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply]
    _ = ∑ i, b.repr (b i) j • b.repr (s * x) i := by
      symm
      rw [Fintype.sum_eq_single j]
      · simp
      · intro i hij
        simp [Basis.repr_self, hij]

/-- A finite free commutative algebra is formally unramified exactly when the discriminant of
one (equivalently, every) basis is a unit. -/
theorem formallyUnramified_iff_isUnit_discr
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι R S) :
    Algebra.FormallyUnramified R S ↔ IsUnit (Algebra.discr R b) := by
  constructor
  · intro h
    exact (traceForm_surjective_iff_isUnit_discr b).mp
      (traceForm_surjective_of_formallyUnramified b h)
  · intro h
    exact formallyUnramified_of_traceForm_surjective b
      ((traceForm_surjective_iff_isUnit_discr b).mpr h)

/-- A finite free commutative algebra is étale exactly when the discriminant of a basis is a
unit.  Finite presentation and flatness are supplied by the same finite basis. -/
theorem etale_iff_isUnit_discr
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι R S) :
    Algebra.Etale R S ↔ IsUnit (Algebra.discr R b) := by
  let : Module.Free R S := Module.Free.of_basis b
  let : Module.Finite R S := Module.Finite.of_basis b
  let : Module.FinitePresentation R S :=
    Module.finitePresentation_of_projective R S
  let : Algebra.FinitePresentation R S := inferInstance
  constructor
  · intro h
    let : Algebra.Etale R S := h
    exact (formallyUnramified_iff_isUnit_discr b).mp inferInstance
  · intro h
    let : Algebra.FormallyUnramified R S :=
      (formallyUnramified_iff_isUnit_discr b).mpr h
    exact Algebra.Etale.of_formallyUnramified_of_flat

end EtaleFundamentalGroups
