/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.TensorNormTransport
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.PlaceEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.InfiniteAlgEquiv
public import Nyll.ClassFieldTheory.Definitions.NormTheorems.IsEverywhereLocalNorm
public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm

/-!
# Transport of local and global norm witnesses

Finite and infinite places are reindexed by their actual field equivalence.
The induced equivalences of completions and tensor algebras retain the
determinant norms, including the specified original base-field unit.
-/

@[expose] public section

noncomputable section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v w x

variable {K : Type u} {L : Type v} {K' : Type w} {L' : Type x}
  [Field K] [NumberField K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Field K'] [NumberField K'] [Field L'] [Algebra K' L'] [FiniteDimensional K' L']

/-- The finite-place condition uses the same norm after completion transport. -/
theorem isNormAtFinitePlace_congr
    (eK : K ≃ₐ[ℚ] K') (eL : L ≃+* L')
    (hL : ∀ a, eL (algebraMap K L a) = algebraMap K' L' (eK a))
    (W : HeightOneSpectrum (𝓞 K')) (x : Kˣ) :
    IsNormAtFinitePlace K L ((finitePlaceCongr eK).symm W) x ↔
      IsNormAtFinitePlace K' L' W (Units.mapEquiv eK.toRingEquiv.toMulEquiv x) := by
  let w := (finitePlaceCongr eK).symm W
  let : Algebra K K' := eK.toRingHom.toAlgebra
  have hKW : finitePlaceBelow (K := K) W = w := by
    apply HeightOneSpectrum.ext
    rfl
  have hA (a : K) : finitePlaceAdicCompletionCongrEquiv eK W
      (algebraMap K (w.adicCompletion K) a) =
        algebraMap K' (W.adicCompletion K') (eK a) := by
    change finitePlaceAdicCompletionMap K K' w ⟨W, hKW⟩
      (a : w.adicCompletion K) = _
    rw [finitePlaceAdicCompletionMap_coe]
    rfl
  exact tensorNorm_exists_iff_of_compatibleEquiv eK.toRingEquiv
    (finitePlaceAdicCompletionCongrEquiv eK W) eL hA hL (x : K)

/-- The infinite-place condition uses the complete tensor norm at the corresponding place. -/
theorem isNormAtInfinitePlace_congr
    (eK : K ≃ₐ[ℚ] K') (eL : L ≃+* L')
    (hL : ∀ a, eL (algebraMap K L a) = algebraMap K' L' (eK a))
    (W : InfinitePlace K') (x : Kˣ) :
    IsNormAtInfinitePlace K L
        ((infinitePlaceEquivOfRingEquiv eK.toRingEquiv).symm W) x ↔
      IsNormAtInfinitePlace K' L' W (Units.mapEquiv eK.toRingEquiv.toMulEquiv x) :=
  tensorNorm_exists_iff_of_compatibleEquiv eK.toRingEquiv
    (infinitePlaceCompletionCongrEquiv eK W) eL
    (infinitePlaceCompletionCongrHom_algebraMap eK W) hL (x : K)

/-- Every original completion norm is retained by compatible field transport. -/
theorem isEverywhereLocalNorm_congr
    (eK : K ≃ₐ[ℚ] K') (eL : L ≃+* L')
    (hL : ∀ a, eL (algebraMap K L a) = algebraMap K' L' (eK a)) (x : Kˣ) :
    IsEverywhereLocalNorm K L x ↔
      IsEverywhereLocalNorm K' L' (Units.mapEquiv eK.toRingEquiv.toMulEquiv x) := by
  constructor
  · rintro ⟨hf, hi⟩
    exact ⟨fun W => (isNormAtFinitePlace_congr eK eL hL W x).mp (hf _),
      fun W => (isNormAtInfinitePlace_congr eK eL hL W x).mp (hi _)⟩
  · rintro ⟨hf, hi⟩
    constructor
    · intro w
      have h := (isNormAtFinitePlace_congr eK eL hL (finitePlaceCongr eK w) x).mpr (hf _)
      rw [(finitePlaceCongr eK).symm_apply_apply] at h
      exact h
    · intro w
      have h := (isNormAtInfinitePlace_congr eK eL hL
        (infinitePlaceEquivOfRingEquiv eK.toRingEquiv w) x).mpr (hi _)
      rw [(infinitePlaceEquivOfRingEquiv eK.toRingEquiv).symm_apply_apply] at h
      exact h

omit [NumberField K] [NumberField K'] in
/-- The actual global field-norm witness commutes with the same field transport. -/
theorem isFieldNorm_congr
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hL : ∀ a, eL (algebraMap K L a) = algebraMap K' L' (eK a)) (x : Kˣ) :
    IsFieldNorm K L x ↔ IsFieldNorm K' L' (Units.mapEquiv eK.toMulEquiv x) := by
  have hcompat : (algebraMap K' L').comp eK.toRingHom =
      eL.toRingHom.comp (algebraMap K L) := RingHom.ext fun a => (hL a).symm
  have hn (y : L) : eK (Algebra.norm K y) = Algebra.norm K' (eL y) :=
    (congrArg eK (Algebra.norm_eq_of_equiv_equiv eK eL hcompat y)).trans
      (eK.apply_symm_apply _)
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.mapEquiv eL.toMulEquiv y, ?_⟩
    apply Units.ext
    change Algebra.norm K' (eL (y : L)) = eK (x : K)
    rw [← hn]
    exact congrArg eK (congrArg Units.val hy)
  · rintro ⟨y, hy⟩
    refine ⟨Units.mapEquiv eL.symm.toMulEquiv y, ?_⟩
    apply Units.ext
    apply eK.injective
    change eK (Algebra.norm K (eL.symm (y : L'))) = eK (x : K)
    rw [hn, eL.apply_symm_apply]
    exact congrArg Units.val hy

end ClassFieldTheory
