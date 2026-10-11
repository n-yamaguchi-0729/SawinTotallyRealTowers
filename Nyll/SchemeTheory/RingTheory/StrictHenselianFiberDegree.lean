/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.HenselianOrthogonalIdempotents
import Nyll.SchemeTheory.RingTheory.OrthogonalIdempotentsDegree
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Generic splitting from a full-degree strictly Henselian fiber

Lift the closed fiber's complete orthogonal family in an arbitrary integral
algebra, map it through the actual embedding into a finite-dimensional
algebra, and use the generic degree bound to obtain a split algebra.
-/

noncomputable section

namespace SchemeTheory

open scoped TensorProduct

universe u

/-- An integral algebra over a strictly Henselian ring with an étale closed
fiber supplies an actual generic splitting whenever it injects into a
finite-dimensional algebra of degree no greater than that closed fiber. -/
theorem exists_generic_split_of_strictHenselian_fiber_degree
    (R K B T : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [Field K]
    [CommRing B] [Algebra R B] [Algebra.IsIntegral R B]
    [CommRing T] [Algebra R T] [Algebra K T] [FiniteDimensional K T]
    (f : B →ₐ[R] T) (hf : Function.Injective f)
    [Algebra.Etale (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] B)]
    (hdegree : Module.finrank K T ≤ Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] B)) :
    ∃ (ι : Type u) (_ : Finite ι), Nonempty (T ≃ₐ[K] (ι → K)) := by
  classical
  let k := IsLocalRing.ResidueField R
  let m := IsLocalRing.maximalIdeal R
  let Q := B ⧸ m.map (algebraMap R B)
  let C := k ⊗[R] B
  let eQ : Q ≃+* C := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m).toRingEquiv
  have : Module.Finite k C := Algebra.FormallyUnramified.finite_of_free k C
  have : IsArtinianRing C := isArtinian_of_tower k inferInstance
  let ι := PrimeSpectrum C
  let : Fintype ι := Fintype.ofFinite ι
  let eFiber : C ≃ₐ[k] (ι → k) := Algebra.FormallyEtale.equivPiOfIsSepClosed k C
  let e : ι → Q := fun i => eQ.symm (eFiber.symm (Pi.single i 1))
  have he : CompleteOrthogonalIdempotents e :=
    ((CompleteOrthogonalIdempotents.single (fun _ : ι => k)).map
      eFiber.symm.toRingHom).map eQ.symm.toRingHom
  obtain ⟨eB, heB, hreduce⟩ :=
    Algebra.exists_completeOrthogonalIdempotents_lift_of_isIntegral m e he
  have hnonzero (i : ι) : f (eB i) ≠ 0 := by
    intro h
    have hB : eB i = 0 := hf (h.trans (map_zero f).symm)
    have hezero : e i = 0 := by
      rw [← hreduce i, hB, map_zero]
    have hvalue := congrArg (fun z : Q => eFiber (eQ z) i) hezero
    have hone : (1 : k) = 0 := by
      simpa only [e, RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, map_zero,
        Pi.zero_apply, Pi.single_eq_same] using hvalue
    exact one_ne_zero hone
  have hcard : Module.finrank K T ≤ Fintype.card ι := by
    calc
      Module.finrank K T ≤ Module.finrank k (k ⊗[R] B) := hdegree
      _ = Module.finrank k (ι → k) := eFiber.toLinearEquiv.finrank_eq
      _ = Fintype.card ι := Module.finrank_pi k
  let eGeneric : T ≃ₐ[K] (ι → K) :=
    splitAlgEquivOfCompleteOrthogonalIdempotents
      (fun i => f (eB i)) (heB.map f.toRingHom) hnonzero hcard
  exact ⟨ι, inferInstance, ⟨eGeneric⟩⟩

end SchemeTheory
