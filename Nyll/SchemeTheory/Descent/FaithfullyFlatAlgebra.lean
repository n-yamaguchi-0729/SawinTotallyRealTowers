/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Equalizer
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Effective descent for algebra coactions

For a faithfully flat ring map, an algebra coaction satisfying the usual
counit and coassociativity equations descends to its equalizer subalgebra.
The actual map from the base change of that subalgebra is an isomorphism.

The proof uses the native comonad coalgebra and its Beck split equalizer.
Flatness preserves the equalizer of the coaction and the adjunction unit.
Multiplication, the unit, and commutativity are inherited from the equalizer
subalgebra, so no separate transport of algebra structures is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Algebra.FaithfullyFlatDescent

variable {R B : Type u} [CommRing R] [CommRing B]
variable (f : R →+* B) (C : Type u) [CommRing C] [Algebra B C]

/-- The underlying map of an algebra coaction in the native scalar-extension
comonad. The restricted scalar action is fixed by the ring map `f`. -/
def coactionLinear (ρ :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    C →ₐ[B] B ⊗[R] C) :
    ModuleCat.of B C ⟶
      (ModuleCat.extendRestrictScalarsAdj f).toComonad.obj (ModuleCat.of B C) := by
  letI : Algebra R B := f.toAlgebra
  letI : Algebra R C := Algebra.compHom C f
  exact ConcreteCategory.ofHom ρ.toLinearMap

/-- Elements fixed by the algebra coaction form an actual subalgebra. -/
def invariants (ρ :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    C →ₐ[B] B ⊗[R] C) :
    letI : Algebra R C := Algebra.compHom C f
    Subalgebra R C := by
  letI : Algebra R B := f.toAlgebra
  letI : Algebra R C := Algebra.compHom C f
  letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  exact AlgHom.equalizer (ρ.restrictScalars R) Algebra.TensorProduct.includeRight

/-- The canonical algebra map from the scalar extension of the invariant
subalgebra. On pure tensors it sends `b ⊗ d` to `algebraMap B C b * d`. -/
def invariantsBaseChange (ρ :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    C →ₐ[B] B ⊗[R] C) :
    letI : Algebra R B := f.toAlgebra
    B ⊗[R] invariants f C ρ →ₐ[B] C := by
  letI : Algebra R B := f.toAlgebra
  letI : Algebra R C := Algebra.compHom C f
  letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  exact Algebra.TensorProduct.lift (Algebra.ofId B C) (invariants f C ρ).val
    (fun b d ↦ Commute.all _ _)

@[simp]
theorem invariantsBaseChange_tmul (ρ :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    C →ₐ[B] B ⊗[R] C)
    (b : B) (d : invariants f C ρ) :
    letI : Algebra R B := f.toAlgebra
    invariantsBaseChange f C ρ (b ⊗ₜ[R] d) = algebraMap B C b * (d : C) := by
  let : Algebra R B := f.toAlgebra
  rfl

private def invariantsFork (ρ :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    C →ₐ[B] B ⊗[R] C) :
    Fork ((ModuleCat.restrictScalars f).map (coactionLinear f C ρ))
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B C))) := by
  letI : Algebra R B := f.toAlgebra
  letI : Algebra R C := Algebra.compHom C f
  letI : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  exact Fork.ofι (ModuleCat.ofHom (invariants f C ρ).val.toLinearMap) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro d
    change (ρ.restrictScalars R) (d : C) =
      Algebra.TensorProduct.includeRight (d : C)
    exact d.property)

private def invariantsForkIsLimit (ρ :
    letI : Algebra R B := f.toAlgebra
    letI : Algebra R C := Algebra.compHom C f
    C →ₐ[B] B ⊗[R] C) :
    IsLimit (invariantsFork f C ρ) := by
  letI : Algebra R B := f.toAlgebra
  letI : Algebra R C := Algebra.compHom C f
  refine Fork.IsLimit.mk _ (fun s ↦ ModuleCat.ofHom
    (s.ι.hom.codRestrict (invariants f C ρ).toSubmodule (fun x ↦ ?_))) ?_ ?_
  · exact congrArg
      (fun k : s.pt ⟶ (ModuleCat.restrictScalars f).obj
          ((ModuleCat.extendRestrictScalarsAdj f).toComonad.obj (ModuleCat.of B C)) ↦ k x)
      s.condition
  · intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · intro s m hm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg
      (fun k : s.pt ⟶ (ModuleCat.restrictScalars f).obj (ModuleCat.of B C) ↦ k x) hm

/-- The literal invariant-subalgebra base-change map is bijective for an
algebra coaction with the native counit and coassociativity identities. -/
theorem invariantsBaseChange_bijective (hf : f.FaithfullyFlat)
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
    Function.Bijective (invariantsBaseChange f C ρ) := by
  let : Algebra R B := f.toAlgebra
  let : Algebra R C := Algebra.compHom C f
  let d : (ModuleCat.extendRestrictScalarsAdj f).toComonad.Coalgebra :=
    { A := ModuleCat.of B C
      a := coactionLinear f C ρ
      counit := hε
      coassoc := hδ }
  let : PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf.flat
  let t : Fork
      ((ModuleCat.extendRestrictScalarsAdj f).toComonad.map d.a)
      ((ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app d.A) :=
    Fork.ofι ((ModuleCat.extendScalars f).map (invariantsFork f C ρ).ι) (by
      change (ModuleCat.extendScalars f).map (invariantsFork f C ρ).ι ≫
          (ModuleCat.extendScalars f).map
            ((ModuleCat.restrictScalars f).map (coactionLinear f C ρ)) =
        (ModuleCat.extendScalars f).map (invariantsFork f C ρ).ι ≫
          (ModuleCat.extendScalars f).map
            ((ModuleCat.extendRestrictScalarsAdj f).unit.app
              ((ModuleCat.restrictScalars f).obj (ModuleCat.of B C)))
      rw [← Functor.map_comp, ← Functor.map_comp, (invariantsFork f C ρ).condition]
      rfl)
  have ht : IsLimit t :=
    isLimitForkMapOfIsLimit (ModuleCat.extendScalars f)
      (invariantsFork f C ρ).condition (invariantsForkIsLimit f C ρ)
  let E : (ModuleCat.extendScalars f).obj (ModuleCat.of R (invariants f C ρ)) ≅
      ModuleCat.of B C :=
    ht.conePointUniqueUpToIso (Comonad.beckEqualizer d)
  have hE : E.hom = ModuleCat.ofHom (invariantsBaseChange f C ρ).toLinearMap := by
    change (Comonad.beckEqualizer d).lift t = _
    rw [Comonad.beckEqualizer_lift]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b z =>
      let b' : B := b
      let z' : invariants f C ρ := z
      change b' • (z' : C) = algebraMap B C b' * (z' : C)
      exact Algebra.smul_def b' (z' : C)
    | add x y hx hy => erw [LinearMap.map_add, LinearMap.map_add, hx, hy]
  have hbij : Function.Bijective E.hom :=
    (ConcreteCategory.isIso_iff_bijective E.hom).mp inferInstance
  rw [hE] at hbij
  exact hbij

/-- Effective algebra descent: extending the invariant subalgebra recovers
the original algebra through its canonical map. -/
def invariantsBaseChangeEquiv (hf : f.FaithfullyFlat)
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
    letI : Algebra R B := f.toAlgebra
    B ⊗[R] invariants f C ρ ≃ₐ[B] C := by
  letI : Algebra R B := f.toAlgebra
  exact AlgEquiv.ofBijective (invariantsBaseChange f C ρ)
    (invariantsBaseChange_bijective f C hf ρ hε hδ)

@[simp]
theorem invariantsBaseChangeEquiv_tmul (hf : f.FaithfullyFlat)
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
        (ModuleCat.extendRestrictScalarsAdj f).toComonad.map (coactionLinear f C ρ))
    (b : B) (z : invariants f C ρ) :
    letI : Algebra R B := f.toAlgebra
    invariantsBaseChangeEquiv f C hf ρ hε hδ (b ⊗ₜ[R] z) =
      algebraMap B C b * (z : C) := by
  let : Algebra R B := f.toAlgebra
  rfl

end Algebra.FaithfullyFlatDescent
