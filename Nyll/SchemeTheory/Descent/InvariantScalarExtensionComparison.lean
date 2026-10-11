/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.CanonicalAlgebraEqualizer
public import Nyll.SchemeTheory.Descent.FaithfullyFlatAlgebra
public import Nyll.SchemeTheory.Descent.AlgebraCoactionTransport
public import Nyll.SchemeTheory.FiniteEtale.Algebra.ProductBaseChangeComparison
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Comparing invariant descent with an actual scalar-extension model

Suppose an actual algebra coaction over a faithfully flat cover becomes the
transported canonical coaction of an actual upper algebra after extending
scalars. The invariant algebra then has that upper algebra as its scalar
extension. The comparison is constructed through the actual faithfully flat
equalizer, and its bijectivity is proved using the effective descent map.

The scalar-extension map need not be flat or finitely presented. The
coaction, its two laws, the upper equivalence, and their compatibility are
the concrete data supplied by the finite radicial cover construction.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Algebra.FaithfullyFlatDescent

variable {R B : Type u} [CommRing R] [CommRing B]
variable (f : R →+* B) (S M A : Type u)
variable [CommRing S] [CommRing M] [CommRing A]
variable [Algebra R S] [Algebra B M] [Algebra S A]

/-- Compatibility with the actual upper coaction identifies the scalar
extension of the invariant algebra with the original upper algebra. -/
def invariantsScalarExtensionEquiv (hf : f.FaithfullyFlat)
    (ρ :
      let : Algebra R B := f.toAlgebra
      let : Algebra R M := Algebra.compHom M f
      M →ₐ[B] B ⊗[R] M)
    (hε : coactionLinear f M ρ ≫
        (ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app (ModuleCat.of B M) =
      𝟙 (ModuleCat.of B M))
    (hδ : coactionLinear f M ρ ≫
        (ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app (ModuleCat.of B M) =
      coactionLinear f M ρ ≫
        (ModuleCat.extendRestrictScalarsAdj f).toComonad.map (coactionLinear f M ρ)) :
    let : Algebra R B := f.toAlgebra
    let : Algebra R M := Algebra.compHom M f
    let : IsScalarTower R B M := IsScalarTower.of_compHom R B M
    let E := S ⊗[R] B
    let U := S ⊗[R] M
    let : Algebra E U := Algebra.TensorProduct.baseChangeAlgebra R S B M
    let : IsScalarTower S E U :=
      Algebra.TensorProduct.baseChangeAlgebra_isScalarTower R S B M
    ∀ (e : U ≃ₐ[E] E ⊗[S] A),
      Algebra.TensorProduct.map (.id S S) (ρ.restrictScalars R) =
        (Algebra.Descent.scalarTensorIso R S B M).toAlgHom.comp
          ((Algebra.Descent.transportedCoaction S E U A e).restrictScalars S) →
      S ⊗[R] invariants f M ρ ≃ₐ[S] A := by
  intro hRB hRM hTower E U hEU hEUTower e he
  have : Module.FaithfullyFlat R B := hf
  let N : Subalgebra R M := invariants f M ρ
  let eN : B ⊗[R] N ≃ₐ[B] M := invariantsBaseChangeEquiv f M hf ρ hε hδ
  let φ : S ⊗[R] N →ₐ[S] E ⊗[S] A :=
    (e.restrictScalars S).toAlgHom.comp
      (Algebra.TensorProduct.map (.id S S) N.val)
  have hφ : ∀ d : S ⊗[R] N,
      Algebra.Descent.canonicalCoaction S E A (φ d) = (1 : E) ⊗ₜ[S] φ d := by
    intro d
    induction d using TensorProduct.inductionOn with
    | tmul s z =>
      change Algebra.Descent.canonicalCoaction S E A (e (s ⊗ₜ[R] (z : M))) =
        (1 : E) ⊗ₜ[S] e (s ⊗ₜ[R] (z : M))
      have hz : ρ (z : M) = (1 : B) ⊗ₜ[R] (z : M) := z.property
      have hbase := AlgHom.congr_fun he (s ⊗ₜ[R] (z : M))
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgHom.restrictScalars_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at hbase
      have hfixed :
          Algebra.Descent.transportedCoaction S E U A e (s ⊗ₜ[R] (z : M)) =
            (1 : E) ⊗ₜ[S] (s ⊗ₜ[R] (z : M)) := by
        apply (Algebra.Descent.scalarTensorIso R S B M).injective
        rw [← hbase, hz]
        change s ⊗ₜ[R] ((1 : B) ⊗ₜ[R] (z : M)) =
          Algebra.Descent.scalarTensorIso R S B M
            (((1 : S) ⊗ₜ[R] (1 : B)) ⊗ₜ[S] (s ⊗ₜ[R] (z : M)))
        rw [Algebra.Descent.scalarTensorIso_tmul, one_mul]
      have h := Algebra.Descent.transportedCoaction_comparison S E U A e
        (s ⊗ₜ[R] (z : M))
      rw [hfixed, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgEquiv.toAlgHom_apply, AlgEquiv.restrictScalars_apply] at h
      exact h.symm
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  let g : E ⊗[S] (S ⊗[R] N) ≃ₐ[S] E ⊗[S] A :=
    (Algebra.Descent.scalarTensorIso R S B N).trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (eN.restrictScalars R)).trans
        (e.restrictScalars S))
  have heN (b : B) (z : N) : eN (b ⊗ₜ[R] z) = algebraMap B M b * (z : M) :=
    invariantsBaseChangeEquiv_tmul f M hf ρ hε hδ b z
  have hmap :
      (Algebra.TensorProduct.lift (Algebra.ofId E (E ⊗[S] A)) φ
        (fun _ _ ↦ Commute.all _ _) : E ⊗[S] (S ⊗[R] N) → E ⊗[S] A) = g := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul c d =>
      induction c using TensorProduct.inductionOn with
      | tmul s b =>
        induction d using TensorProduct.inductionOn with
        | tmul t z =>
          rw [Algebra.TensorProduct.lift_tmul]
          change algebraMap E (E ⊗[S] A) (s ⊗ₜ[R] b) * e (t ⊗ₜ[R] (z : M)) =
            e ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (eN.restrictScalars R))
              (Algebra.Descent.scalarTensorIso R S B N
                ((s ⊗ₜ[R] b) ⊗ₜ[S] (t ⊗ₜ[R] z))))
          rw [Algebra.Descent.scalarTensorIso_tmul, Algebra.TensorProduct.congr_apply,
            Algebra.TensorProduct.map_tmul]
          change algebraMap E (E ⊗[S] A) (s ⊗ₜ[R] b) * e (t ⊗ₜ[R] (z : M)) =
            e ((s * t) ⊗ₜ[R] eN (b ⊗ₜ[R] z))
          rw [heN, ← e.commutes,
            Algebra.TensorProduct.baseChangeAlgebra_algebraMap_tmul R S B M s b,
            ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  apply Algebra.Descent.descendCanonicalEquiv S E A (S ⊗[R] N) φ hφ
  rw [hmap]
  exact g.bijective

end Algebra.FaithfullyFlatDescent
