/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Tensor comparisons for actual products of local models

The interchange map identifies the two concrete orders of scalar extension.
Its formulas retain the actual coefficient maps used for descent.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

universe u

/-- The canonical action of the base-changed coefficient algebra on the
base-changed model, through the actual tensor map of its structure map. -/
abbrev baseChangeAlgebra
    (R S B M : Type u) [CommRing R] [CommRing S] [CommRing B] [CommRing M]
    [Algebra R S] [Algebra R B] [Algebra R M] [Algebra B M]
    [IsScalarTower R B M] : Algebra (S ⊗[R] B) (S ⊗[R] M) :=
  (map (AlgHom.id S S) (IsScalarTower.toAlgHom R B M)).toRingHom.toAlgebra

theorem baseChangeAlgebra_isScalarTower
    (R S B M : Type u) [CommRing R] [CommRing S] [CommRing B] [CommRing M]
    [Algebra R S] [Algebra R B] [Algebra R M] [Algebra B M]
    [IsScalarTower R B M] :
    let : Algebra (S ⊗[R] B) (S ⊗[R] M) := baseChangeAlgebra R S B M;
    IsScalarTower S (S ⊗[R] B) (S ⊗[R] M) := by
  let : Algebra (S ⊗[R] B) (S ⊗[R] M) := baseChangeAlgebra R S B M
  exact IsScalarTower.of_algebraMap_eq'
    (map (AlgHom.id S S) (IsScalarTower.toAlgHom R B M)).comp_algebraMap.symm

theorem baseChangeAlgebra_algebraMap_tmul
    (R S B M : Type u) [CommRing R] [CommRing S] [CommRing B] [CommRing M]
    [Algebra R S] [Algebra R B] [Algebra R M] [Algebra B M]
    [IsScalarTower R B M] (s : S) (b : B) :
    let : Algebra (S ⊗[R] B) (S ⊗[R] M) := baseChangeAlgebra R S B M;
    algebraMap (S ⊗[R] B) (S ⊗[R] M) (s ⊗ₜ[R] b) =
      s ⊗ₜ[R] algebraMap B M b := by
  let : Algebra (S ⊗[R] B) (S ⊗[R] M) := baseChangeAlgebra R S B M
  exact map_tmul (AlgHom.id S S) (IsScalarTower.toAlgHom R B M) s b

/-- Interchanging the coefficient base change and the model base change.
The source uses the right `S`-algebra structure on `B ⊗[R] S`. -/
def rightBaseChangeInterchange
    (R B S M : Type u) [CommRing R] [CommRing B] [CommRing S] [CommRing M]
    [Algebra R B] [Algebra R S] [Algebra R M] [Algebra B M]
    [IsScalarTower R B M] :
    let : Algebra S (B ⊗[R] S) := rightAlgebra;
    ((B ⊗[R] S) ⊗[B] M) ≃ₐ[S] (S ⊗[R] M) := by
  let : Algebra S (B ⊗[R] S) := rightAlgebra
  let e : ((B ⊗[R] S) ⊗[B] M) ≃+* (S ⊗[R] M) :=
    (Algebra.TensorProduct.comm B (B ⊗[R] S) M).toRingEquiv.trans
      ((cancelBaseChange R B M M S).toRingEquiv.trans
        (Algebra.TensorProduct.comm R M S).toRingEquiv)
  refine { __ := e, commutes' := ?_ }
  intro s
  change Algebra.TensorProduct.comm R M S
    (cancelBaseChange R B M M S
      (Algebra.TensorProduct.comm B (B ⊗[R] S) M
        ((1 ⊗ₜ[R] s) ⊗ₜ[B] (1 : M)))) = s ⊗ₜ[R] (1 : M)
  rw [comm_tmul, cancelBaseChange_tmul, comm_tmul, one_smul]

theorem rightBaseChangeInterchange_tmul
    (R B S M : Type u) [CommRing R] [CommRing B] [CommRing S] [CommRing M]
    [Algebra R B] [Algebra R S] [Algebra R M] [Algebra B M]
    [IsScalarTower R B M] (b : B) (s : S) (m : M) :
    let : Algebra S (B ⊗[R] S) := rightAlgebra;
    rightBaseChangeInterchange R B S M ((b ⊗ₜ[R] s) ⊗ₜ[B] m) = s ⊗ₜ[R] (b • m) := by
  let : Algebra S (B ⊗[R] S) := rightAlgebra
  change Algebra.TensorProduct.comm R M S
    (cancelBaseChange R B M M S
      (Algebra.TensorProduct.comm B (B ⊗[R] S) M
        ((b ⊗ₜ[R] s) ⊗ₜ[B] m))) = s ⊗ₜ[R] (b • m)
  rw [comm_tmul, cancelBaseChange_tmul, comm_tmul]

theorem rightBaseChangeInterchange_symm_tmul_smul
    (R B S M : Type u) [CommRing R] [CommRing B] [CommRing S] [CommRing M]
    [Algebra R B] [Algebra R S] [Algebra R M] [Algebra B M]
    [IsScalarTower R B M] (b : B) (s : S) (m : M) :
    let : Algebra S (B ⊗[R] S) := rightAlgebra;
    (rightBaseChangeInterchange R B S M).symm (s ⊗ₜ[R] (b • m)) =
      (b ⊗ₜ[R] s) ⊗ₜ[B] m := by
  let : Algebra S (B ⊗[R] S) := rightAlgebra
  apply (rightBaseChangeInterchange R B S M).injective
  rw [AlgEquiv.apply_symm_apply, rightBaseChangeInterchange_tmul]

/-- The product of the actual local trivial models recovers the original
cover after the common base change. The coefficient action is the canonical
tensor map `baseChangeAlgebra`, so this is an equivalence over the actual
base-changed product algebra. -/
theorem nonempty_product_baseChange_model
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A]
    {ι : Type u} [Finite ι] (D : ι → Type u) [∀ i, CommRing (D i)]
    [∀ i, Algebra R (D i)] (n : ι → ℕ)
    (e : ∀ i : ι,
      let : Algebra S (D i ⊗[R] S) := rightAlgebra;
      ((D i ⊗[R] S) ⊗[D i] (Fin (n i) → D i)) ≃ₐ[D i ⊗[R] S]
        ((D i ⊗[R] S) ⊗[S] A)) :
    let : Algebra (S ⊗[R] (∀ i : ι, D i))
        (S ⊗[R] (∀ i : ι, Fin (n i) → D i)) :=
      baseChangeAlgebra R S (∀ i : ι, D i) (∀ i : ι, Fin (n i) → D i);
    Nonempty ((S ⊗[R] (∀ i : ι, Fin (n i) → D i)) ≃ₐ[S ⊗[R] (∀ i : ι, D i)]
      ((S ⊗[R] (∀ i : ι, D i)) ⊗[S] A)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let B := ∀ i : ι, D i
  let M := ∀ i : ι, Fin (n i) → D i
  let E := S ⊗[R] B
  let U := S ⊗[R] M
  let : Algebra E U := baseChangeAlgebra R S B M
  let (i : ι) : Algebra S (D i ⊗[R] S) := rightAlgebra
  let localE (i : ι) :
      (S ⊗[R] (Fin (n i) → D i)) ≃ₐ[S] ((S ⊗[R] D i) ⊗[S] A) :=
    (rightBaseChangeInterchange R (D i) S (Fin (n i) → D i)).symm.trans
      ((e i).restrictScalars S |>.trans
        (congr (commRight R S (D i)).symm (AlgEquiv.refl : A ≃ₐ[S] A)))
  have hlocal (i : ι) (s : S) (b : D i) :
      localE i (s ⊗ₜ[R] (b • (1 : Fin (n i) → D i))) =
        (s ⊗ₜ[R] b) ⊗ₜ[S] (1 : A) := by
    change congr (commRight R S (D i)).symm (AlgEquiv.refl : A ≃ₐ[S] A)
      (e i ((rightBaseChangeInterchange R (D i) S (Fin (n i) → D i)).symm
        (s ⊗ₜ[R] (b • (1 : Fin (n i) → D i))))) = _
    rw [rightBaseChangeInterchange_symm_tmul_smul]
    change congr (commRight R S (D i)).symm (AlgEquiv.refl : A ≃ₐ[S] A)
      (e i (algebraMap (D i ⊗[R] S)
        ((D i ⊗[R] S) ⊗[D i] (Fin (n i) → D i)) (b ⊗ₜ[R] s))) = _
    rw [(e i).commutes]
    change map (commRight R S (D i)).symm.toAlgHom (AlgHom.id S A)
      ((b ⊗ₜ[R] s) ⊗ₜ[S] (1 : A)) = _
    rw [map_tmul]
    change (commRight R S (D i)).symm (b ⊗ₜ[R] s) ⊗ₜ[S] (1 : A) = _
    rw [commRight_symm_tmul]
  let toProduct : (E ⊗[S] A) ≃ₐ[S] (∀ i : ι, (S ⊗[R] D i) ⊗[S] A) :=
    (Algebra.TensorProduct.comm S E A).trans
      ((congr (AlgEquiv.refl : A ≃ₐ[S] A) (piRight R S S D)).trans
        ((piRight S S A (fun i : ι ↦ S ⊗[R] D i)).trans
          (AlgEquiv.piCongrRight fun i : ι ↦
            Algebra.TensorProduct.comm S A (S ⊗[R] D i))))
  have htoProduct (s : S) (b : B) (a : A) :
      toProduct ((s ⊗ₜ[R] b) ⊗ₜ[S] a) =
        fun i : ι ↦ (s ⊗ₜ[R] b i) ⊗ₜ[S] a := by
    apply funext
    intro i
    simp only [toProduct, AlgEquiv.trans_apply, comm_tmul, congr_apply, map_tmul,
      AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq, piRight_tmul,
      AlgEquiv.piCongrRight_apply]
    exact congrArg (fun z : ∀ j : ι, S ⊗[R] D j ↦ z i ⊗ₜ[S] a)
      (piRight_tmul R S S D s b)
  let fromLocal : U ≃ₐ[S] (∀ i : ι, (S ⊗[R] D i) ⊗[S] A) :=
    (piRight R S S (fun i : ι ↦ Fin (n i) → D i)).trans
      (AlgEquiv.piCongrRight localE)
  let total : U ≃ₐ[S] (E ⊗[S] A) := fromLocal.trans toProduct.symm
  refine ⟨{ __ := total.toRingEquiv, commutes' := ?_ }⟩
  intro c
  change total (algebraMap E U c) = algebraMap E (E ⊗[S] A) c
  induction c using TensorProduct.inductionOn with
  | add c₁ c₂ hc₁ hc₂ => simp only [map_add, hc₁, hc₂]
  | tmul s b =>
      rw [baseChangeAlgebra_algebraMap_tmul]
      apply toProduct.injective
      change toProduct (toProduct.symm
        (fromLocal (s ⊗ₜ[R] algebraMap B M b))) =
          toProduct ((s ⊗ₜ[R] b) ⊗ₜ[S] (1 : A))
      rw [AlgEquiv.apply_symm_apply, htoProduct]
      apply funext
      intro i
      change localE i ((piRight R S S (fun j : ι ↦ Fin (n j) → D j))
        (s ⊗ₜ[R] algebraMap B M b) i) = _
      rw [piRight_tmul]
      change localE i (s ⊗ₜ[R] algebraMap (D i) (Fin (n i) → D i) (b i)) =
        (s ⊗ₜ[R] b i) ⊗ₜ[S] (1 : A)
      rw [Algebra.algebraMap_eq_smul_one]
      exact hlocal i s (b i)

end Algebra.TensorProduct
