/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensoring a localization tower

For an algebra over a localization of the base ring, first extending the
localization and then extending that algebra gives the same tensor product
as extending the algebra directly. The comparison remains linear over the
new base, which need not itself be an algebra over the original localization.
-/

noncomputable section

open scoped TensorProduct

namespace SchemeTheory

universe u v w t

/-- Reassociate scalar extension through a localization, retaining the new
base's scalar action rather than requiring the new base to invert denominators. -/
def localizationTensorTowerEquiv
    (R : Type u) (K : Type v) (S : Type w) (B : Type t)
    [CommRing R] [CommRing K] [CommRing S] [CommRing B]
    [Algebra R K] [Algebra R S] [Algebra R B] [Algebra K B]
    [IsScalarTower R K B] (M : Submonoid R) [IsLocalization M K] :
    letI : Algebra K (S ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
    ((S ⊗[R] K) ⊗[K] B) ≃ₐ[S] (S ⊗[R] B) := by
  letI : Algebra K (S ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
  letI : TensorProduct.CompatibleSMul R K (S ⊗[R] K) B :=
    IsLocalization.tensorProduct_compatibleSMul M K (S ⊗[R] K) B
  let e₁ : ((S ⊗[R] K) ⊗[K] B) ≃ₐ[S] ((S ⊗[R] K) ⊗[R] B) :=
    Algebra.TensorProduct.equivOfCompatibleSMul R K S (S ⊗[R] K) B
  let e₂ : ((S ⊗[R] K) ⊗[R] B) ≃ₐ[S] (S ⊗[R] (K ⊗[R] B)) :=
    Algebra.TensorProduct.assoc R R S S K B
  let e₃ : (S ⊗[R] (K ⊗[R] B)) ≃ₐ[S] (S ⊗[R] B) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
      ((IsLocalization.algebraLid M K B).restrictScalars R)
  exact e₁.trans (e₂.trans e₃)

end SchemeTheory
