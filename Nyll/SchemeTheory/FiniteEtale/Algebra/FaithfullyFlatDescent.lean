/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.FaithfullyFlatAlgebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Finite étale invariant algebras

The equalizer algebra constructed by faithfully flat descent is itself finite
étale when the algebra carrying the coaction is finite étale. The comparison
with its scalar extension is the actual invariant-subalgebra map, so the
native descent theorems for finiteness and étaleness apply to this construction.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Algebra.FaithfullyFlatDescent

variable {R B : Type u} [CommRing R] [CommRing B]

/-- The actual invariant algebra of a finite étale algebra coaction is finite
étale over the original ring. -/
theorem invariants_finite_etale (f : R →+* B) (C : Type u)
    [CommRing C] [Algebra B C] [Module.Finite B C] [Algebra.Etale B C]
    (hf : f.FaithfullyFlat)
    (ρ :
      letI : Algebra R B := f.toAlgebra
      letI : Algebra R C := Algebra.compHom C f
      C →ₐ[B] B ⊗[R] C)
    (hε : coactionLinear f C ρ ≫
        (ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app (ModuleCat.of B C) =
      𝟙 (ModuleCat.of B C))
    (hδ : coactionLinear f C ρ ≫
        (ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app (ModuleCat.of B C) =
      coactionLinear f C ρ ≫
        (ModuleCat.extendRestrictScalarsAdj f).toComonad.map (coactionLinear f C ρ)) :
    Module.Finite R (invariants f C ρ) ∧ Algebra.Etale R (invariants f C ρ) := by
  let : Algebra R B := f.toAlgebra
  let : Algebra R C := Algebra.compHom C f
  let : Module.FaithfullyFlat R B := hf
  let e : B ⊗[R] invariants f C ρ ≃ₐ[B] C :=
    invariantsBaseChangeEquiv f C hf ρ hε hδ
  let : Module.Finite B (B ⊗[R] invariants f C ρ) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  let : Algebra.Etale B (B ⊗[R] invariants f C ρ) := Algebra.Etale.of_equiv e.symm
  exact ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B,
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat B⟩

end Algebra.FaithfullyFlatDescent
