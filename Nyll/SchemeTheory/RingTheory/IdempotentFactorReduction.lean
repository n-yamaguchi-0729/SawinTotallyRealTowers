/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.QuotientBaseChange
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span

/-!
# Reduction of an idempotent factor

Imposing `e = 1` commutes with reducing by an extended base ideal. The
comparison is obtained from the canonical interchange of two quotient rings.
It also identifies a reduced factor with a specified factor of a product.
-/

@[expose] public noncomputable section

universe u v w z

namespace Algebra

variable {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]

/-- Taking the factor where `e = 1` commutes with reduction modulo the base
ideal. The construction does not require idempotence of `e`. -/
def idempotentFactorReduction (I : Ideal R) (e : C) :
    ((C ⧸ Ideal.span {1 - e}) ⧸
      I.map (algebraMap R (C ⧸ Ideal.span {1 - e}))) ≃ₐ[R ⧸ I]
    (C ⧸ I.map (algebraMap R C)) ⧸
      Ideal.span {1 - Ideal.Quotient.mk (I.map (algebraMap R C)) e} := by
  let K : Ideal C := Ideal.span {1 - e}
  let J : Ideal C := I.map (algebraMap R C)
  have hleft : J.map (Ideal.Quotient.mkₐ R K) =
      I.map (algebraMap R (C ⧸ K)) :=
    (Ideal.Quotient.mkₐ R K).map_extendedIdeal I
  have hright : K.map (Ideal.Quotient.mkₐ R J) =
      Ideal.span {1 - Ideal.Quotient.mk J e} := by
    simp only [K, Ideal.map_span, Set.image_singleton, map_sub, map_one]
    rfl
  let E : ((C ⧸ K) ⧸ I.map (algebraMap R (C ⧸ K))) ≃ₐ[R]
      (C ⧸ J) ⧸ Ideal.span {1 - Ideal.Quotient.mk J e} :=
    ((Ideal.quotientEquivAlgOfEq R hleft.symm).trans
      (DoubleQuot.quotQuotEquivCommₐ R K J)).trans
        (Ideal.quotientEquivAlgOfEq R hright)
  exact E.extendScalarsOfSurjective Ideal.Quotient.mk_surjective

@[simp]
theorem idempotentFactorReduction_mk_mk (I : Ideal R) (e c : C) :
    idempotentFactorReduction I e
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {1 - e}) c)) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk (I.map (algebraMap R C)) c) := rfl

/-- If `e` reduces to `1`, its factor has the same reduction as the original
algebra. -/
def idempotentFactorReductionEquivOfEqOne (I : Ideal R) (e : C)
    (he : Ideal.Quotient.mk (I.map (algebraMap R C)) e = 1) :
    ((C ⧸ Ideal.span {1 - e}) ⧸
      I.map (algebraMap R (C ⧸ Ideal.span {1 - e}))) ≃ₐ[R ⧸ I]
        C ⧸ I.map (algebraMap R C) := by
  have hzero : Ideal.span {1 - Ideal.Quotient.mk (I.map (algebraMap R C)) e} =
      (⊥ : Ideal (C ⧸ I.map (algebraMap R C))) := by
    rw [he, sub_self, Ideal.span_singleton_zero]
  exact ((idempotentFactorReduction I e).trans
    (Ideal.quotientEquivAlgOfEq (R ⧸ I) hzero)).trans
      (AlgEquiv.quotientBot (R ⧸ I) (C ⧸ I.map (algebraMap R C)))

@[simp]
theorem idempotentFactorReductionEquivOfEqOne_mk_mk
    (I : Ideal R) (e : C)
    (he : Ideal.Quotient.mk (I.map (algebraMap R C)) e = 1) (c : C) :
    idempotentFactorReductionEquivOfEqOne I e he
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {1 - e}) c)) =
        Ideal.Quotient.mk (I.map (algebraMap R C)) c := rfl

/-- A product decomposition sending `e` to `(1, 0)` identifies the quotient by `1 - e`
with the first factor. -/
def quotientOneSubEquivFst
    {Q : Type u} {A : Type v} {D : Type w} {F : Type z}
    [CommRing Q] [CommRing A] [CommRing D] [CommRing F]
    [Algebra Q A] [Algebra Q D] [Algebra Q F]
    (E : A ≃ₐ[Q] D × F) (e : A) (he : E e = (1, 0)) :
    (A ⧸ Ideal.span {1 - e}) ≃ₐ[Q] D := by
  let p : A →ₐ[Q] D := (AlgHom.fst Q D F).comp E.toAlgHom
  have hp : Function.Surjective p := by
    intro d
    refine ⟨E.symm (d, 0), ?_⟩
    change (E (E.symm (d, 0))).1 = d
    rw [E.apply_symm_apply]
  have hker : Ideal.span {1 - e} = RingHom.ker p.toRingHom := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      change (E (1 - e)).1 = 0
      rw [map_sub, map_one, he]
      change (1 : D) - 1 = 0
      exact sub_self 1
    · intro x hx
      apply Ideal.mem_span_singleton.mpr
      refine ⟨x, ?_⟩
      apply E.injective
      rw [map_mul, map_sub, map_one, he]
      apply Prod.ext
      · change (E x).1 = (1 - 1) * (E x).1
        rw [sub_self, zero_mul]
        exact hx
      · change (E x).2 = (1 - 0) * (E x).2
        rw [sub_zero, one_mul]
  exact (Ideal.quotientEquivAlgOfEq Q hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := p) hp)

/-- A product decomposition of the reduction identifies the reduced factor
selected by `(1, 0)` with its first factor. -/
def idempotentFactorReductionEquivFst (I : Ideal R) (e : C)
    {D : Type w} {F : Type z} [CommRing D] [CommRing F]
    [Algebra (R ⧸ I) D] [Algebra (R ⧸ I) F]
    (E : (C ⧸ I.map (algebraMap R C)) ≃ₐ[R ⧸ I] D × F)
    (hE : E (Ideal.Quotient.mk (I.map (algebraMap R C)) e) = (1, 0)) :
    ((C ⧸ Ideal.span {1 - e}) ⧸
      I.map (algebraMap R (C ⧸ Ideal.span {1 - e}))) ≃ₐ[R ⧸ I] D :=
  (idempotentFactorReduction I e).trans
    (quotientOneSubEquivFst E (Ideal.Quotient.mk (I.map (algebraMap R C)) e) hE)

@[simp]
theorem idempotentFactorReductionEquivFst_mk_mk (I : Ideal R) (e : C)
    {D : Type w} {F : Type z} [CommRing D] [CommRing F]
    [Algebra (R ⧸ I) D] [Algebra (R ⧸ I) F]
    (E : (C ⧸ I.map (algebraMap R C)) ≃ₐ[R ⧸ I] D × F)
    (hE : E (Ideal.Quotient.mk (I.map (algebraMap R C)) e) = (1, 0)) (c : C) :
    idempotentFactorReductionEquivFst I e E hE
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {1 - e}) c)) =
        (E (Ideal.Quotient.mk (I.map (algebraMap R C)) c)).1 := rfl

end Algebra
