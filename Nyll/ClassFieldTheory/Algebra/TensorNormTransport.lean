/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Norm.Basic

/-!
# Transport of the actual tensor determinant norm

Compatible equivalences of the base field, coefficient ring and extension
give an equivalence of their tensor algebras. The determinant norm and its
unit witnesses commute with this equivalence.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace ClassFieldTheory

universe u v w u' v' w'

variable {K : Type u} {L : Type v} {A : Type w}
  {K' : Type u'} {L' : Type v'} {A' : Type w'}
  [CommRing K] [CommRing L] [CommRing A] [Algebra K L] [Algebra K A]
  [CommRing K'] [CommRing L'] [CommRing A'] [Algebra K' L'] [Algebra K' A']

/-- The tensor map induced by the original compatible ring equivalences. -/
def tensorMapOfCompatibleEquiv (eK : K ≃+* K') (eA : A ≃+* A') (eL : L ≃+* L')
    (hA : ∀ x, eA (algebraMap K A x) = algebraMap K' A' (eK x))
    (hL : ∀ x, eL (algebraMap K L x) = algebraMap K' L' (eK x)) :
    A ⊗[K] L →+* A' ⊗[K'] L' := by
  let : Algebra K (A' ⊗[K'] L') :=
    ((algebraMap K' (A' ⊗[K'] L')).comp eK.toRingHom).toAlgebra
  let fA : A →ₐ[K] A' ⊗[K'] L' :=
    { __ := (Algebra.TensorProduct.includeLeft : A' →ₐ[K'] A' ⊗[K'] L').toRingHom.comp
        eA.toRingHom
      commutes' := fun x => by
        change (Algebra.TensorProduct.includeLeft : A' →ₐ[K'] A' ⊗[K'] L')
            (eA (algebraMap K A x)) =
          algebraMap K' (A' ⊗[K'] L') (eK x)
        rw [hA]
        exact (Algebra.TensorProduct.includeLeft : A' →ₐ[K'] A' ⊗[K'] L').commutes _ }
  let fL : L →ₐ[K] A' ⊗[K'] L' :=
    { __ := (Algebra.TensorProduct.includeRight : L' →ₐ[K'] A' ⊗[K'] L').toRingHom.comp
        eL.toRingHom
      commutes' := fun x => by
        change (Algebra.TensorProduct.includeRight : L' →ₐ[K'] A' ⊗[K'] L')
            (eL (algebraMap K L x)) =
          algebraMap K' (A' ⊗[K'] L') (eK x)
        rw [hL]
        exact (Algebra.TensorProduct.includeRight : L' →ₐ[K'] A' ⊗[K'] L').commutes _ }
  exact (Algebra.TensorProduct.lift fA fL (fun _ _ => Commute.all _ _)).toRingHom

/-- A pure tensor keeps its two prescribed coefficient images. -/
theorem tensorMapOfCompatibleEquiv_tmul
    (eK : K ≃+* K') (eA : A ≃+* A') (eL : L ≃+* L')
    (hA : ∀ x, eA (algebraMap K A x) = algebraMap K' A' (eK x))
    (hL : ∀ x, eL (algebraMap K L x) = algebraMap K' L' (eK x)) (a : A) (l : L) :
    tensorMapOfCompatibleEquiv eK eA eL hA hL (a ⊗ₜ[K] l) =
      eA a ⊗ₜ[K'] eL l := by
  change (eA a ⊗ₜ[K'] (1 : L')) * ((1 : A') ⊗ₜ[K'] eL l) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The actual tensor algebras are equivalent under compatible changes of fields. -/
def tensorCongrOfCompatibleEquiv
    (eK : K ≃+* K') (eA : A ≃+* A') (eL : L ≃+* L')
    (hA : ∀ x, eA (algebraMap K A x) = algebraMap K' A' (eK x))
    (hL : ∀ x, eL (algebraMap K L x) = algebraMap K' L' (eK x)) :
    A ⊗[K] L ≃+* A' ⊗[K'] L' := by
  have hA' (x : K') : eA.symm (algebraMap K' A' x) =
      algebraMap K A (eK.symm x) := by
    apply eA.injective
    rw [eA.apply_symm_apply, hA, eK.apply_symm_apply]
  have hL' (x : K') : eL.symm (algebraMap K' L' x) =
      algebraMap K L (eK.symm x) := by
    apply eL.injective
    rw [eL.apply_symm_apply, hL, eK.apply_symm_apply]
  let f := tensorMapOfCompatibleEquiv eK eA eL hA hL
  let g := tensorMapOfCompatibleEquiv eK.symm eA.symm eL.symm hA' hL'
  refine RingEquiv.ofRingHom f g ?_ ?_
  · apply RingHom.ext
    intro z
    change f (g z) = z
    induction z using TensorProduct.inductionOn with
    | add z t hz ht => rw [map_add, map_add, hz, ht]
    | tmul a l =>
        rw [tensorMapOfCompatibleEquiv_tmul, tensorMapOfCompatibleEquiv_tmul,
          eA.apply_symm_apply, eL.apply_symm_apply]
  · apply RingHom.ext
    intro z
    change g (f z) = z
    induction z using TensorProduct.inductionOn with
    | add z t hz ht => rw [map_add, map_add, hz, ht]
    | tmul a l =>
        rw [tensorMapOfCompatibleEquiv_tmul, tensorMapOfCompatibleEquiv_tmul,
          eA.symm_apply_apply, eL.symm_apply_apply]

/-- Tensor transport evaluates through the same two coefficient equivalences. -/
theorem tensorCongrOfCompatibleEquiv_tmul
    (eK : K ≃+* K') (eA : A ≃+* A') (eL : L ≃+* L')
    (hA : ∀ x, eA (algebraMap K A x) = algebraMap K' A' (eK x))
    (hL : ∀ x, eL (algebraMap K L x) = algebraMap K' L' (eK x)) (a : A) (l : L) :
    tensorCongrOfCompatibleEquiv eK eA eL hA hL (a ⊗ₜ[K] l) = eA a ⊗ₜ[K'] eL l :=
  tensorMapOfCompatibleEquiv_tmul eK eA eL hA hL a l

/-- The determinant norm commutes with the actual tensor equivalence. -/
theorem tensorCongrOfCompatibleEquiv_norm
    (eK : K ≃+* K') (eA : A ≃+* A') (eL : L ≃+* L')
    (hA : ∀ x, eA (algebraMap K A x) = algebraMap K' A' (eK x))
    (hL : ∀ x, eL (algebraMap K L x) = algebraMap K' L' (eK x)) (z : A ⊗[K] L) :
    eA (Algebra.norm A z) =
      Algebra.norm A' (tensorCongrOfCompatibleEquiv eK eA eL hA hL z) := by
  let E := tensorCongrOfCompatibleEquiv eK eA eL hA hL
  have hcompat : (algebraMap A' (A' ⊗[K'] L')).comp eA.toRingHom =
      E.toRingHom.comp (algebraMap A (A ⊗[K] L)) := by
    ext a
    change eA a ⊗ₜ[K'] (1 : L') = E (a ⊗ₜ[K] (1 : L))
    rw [tensorCongrOfCompatibleEquiv_tmul, map_one]
  have hn := Algebra.norm_eq_of_equiv_equiv eA E hcompat z
  exact (congrArg eA hn).trans (eA.apply_symm_apply _)

/-- Existence of a unit with a specified tensor norm is transported by
the actual tensor equivalence, preserving its norm value. -/
theorem tensorNorm_exists_iff_of_compatibleEquiv
    (eK : K ≃+* K') (eA : A ≃+* A') (eL : L ≃+* L')
    (hA : ∀ x, eA (algebraMap K A x) = algebraMap K' A' (eK x))
    (hL : ∀ x, eL (algebraMap K L x) = algebraMap K' L' (eK x)) (x : K) :
    (∃ y : (A ⊗[K] L)ˣ, Algebra.norm A (y : A ⊗[K] L) = algebraMap K A x) ↔
      ∃ y : (A' ⊗[K'] L')ˣ,
        Algebra.norm A' (y : A' ⊗[K'] L') = algebraMap K' A' (eK x) := by
  let E := tensorCongrOfCompatibleEquiv eK eA eL hA hL
  let EU := Units.mapEquiv E.toMulEquiv
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨EU y, ?_⟩
    change Algebra.norm A' (E (y : A ⊗[K] L)) = _
    rw [← tensorCongrOfCompatibleEquiv_norm eK eA eL hA hL, hy, hA]
  · rintro ⟨y, hy⟩
    refine ⟨EU.symm y, ?_⟩
    apply eA.injective
    rw [tensorCongrOfCompatibleEquiv_norm eK eA eL hA hL, hA]
    change Algebra.norm A' (E (E.symm (y : A' ⊗[K'] L'))) = _
    rw [E.apply_symm_apply]
    exact hy

/-- The full unit norm image is carried to the full unit norm image,
for every coefficient-ring unit, including nonprincipal local units. -/
theorem tensorNorm_mem_range_iff_of_compatibleEquiv
    (eK : K ≃+* K') (eA : A ≃+* A') (eL : L ≃+* L')
    (hA : ∀ x, eA (algebraMap K A x) = algebraMap K' A' (eK x))
    (hL : ∀ x, eL (algebraMap K L x) = algebraMap K' L' (eK x)) (a : Aˣ) :
    a ∈ (Units.map (Algebra.norm A : A ⊗[K] L →* A)).range ↔
      Units.mapEquiv eA.toMulEquiv a ∈
        (Units.map (Algebra.norm A' : A' ⊗[K'] L' →* A')).range := by
  let E := tensorCongrOfCompatibleEquiv eK eA eL hA hL
  let EU := Units.mapEquiv E.toMulEquiv
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨EU y, ?_⟩
    apply Units.ext
    change Algebra.norm A' (E (y : A ⊗[K] L)) = eA (a : A)
    rw [← tensorCongrOfCompatibleEquiv_norm eK eA eL hA hL]
    exact congrArg eA (congrArg Units.val hy)
  · rintro ⟨y, hy⟩
    refine ⟨EU.symm y, ?_⟩
    apply Units.ext
    apply eA.injective
    change eA (Algebra.norm A (E.symm (y : A' ⊗[K'] L'))) = eA (a : A)
    rw [tensorCongrOfCompatibleEquiv_norm eK eA eL hA hL, E.apply_symm_apply]
    exact congrArg Units.val hy

end ClassFieldTheory
