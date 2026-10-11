/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleEqualizer
import Nyll.SchemeTheory.RingTheory.Descent.ModuleBaseChangeHomExt

/-!
# Descent of module homomorphisms along a faithfully flat algebra

The usual Amitsur equalizer for a target module also gives the Hom-level
full-faithfulness statement.  An `S`-linear map between two extended modules
comes from the base precisely when its values on the canonical generators
belong to the target equalizer.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe u v w w'

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type w'} [AddCommGroup N] [Module R N]

/-- The submodule of maps between extended modules whose values on the
canonical generators satisfy the Amitsur equalizer relation. -/
def tensorProductDescentCompatibleLinearMaps :
    Submodule R ((S ⊗[R] M) →ₗ[S] (S ⊗[R] N)) where
  carrier := {F | ∀ m : M,
    tensorProductDescentLeft (R := R) (S := S) (M := N)
        (F (1 ⊗ₜ[R] m)) =
      tensorProductDescentRight (R := R) (S := S) (M := N)
        (F (1 ⊗ₜ[R] m))}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG m
    simp only [LinearMap.add_apply, map_add]
    rw [hF m, hG m]
  smul_mem' := by
    intro r F hF m
    simp only [LinearMap.smul_apply, map_smul]
    rw [hF m]

/-- Base change sends every `R`-linear map to a descent-compatible map
between the extended modules. -/
def tensorProductLinearMapToDescentCompatible :
    (M →ₗ[R] N) →ₗ[R]
      tensorProductDescentCompatibleLinearMaps
        (R := R) (S := S) (M := M) (N := N) where
  toFun f := ⟨f.baseChange S, by
    intro m
    simp [tensorProductDescentLeft, tensorProductDescentRight]⟩
  map_add' f g := by
    apply Subtype.ext
    exact LinearMap.baseChange_add f g
  map_smul' r f := by
    apply Subtype.ext
    exact LinearMap.baseChange_smul r f

@[simp]
theorem tensorProductLinearMapToDescentCompatible_coe
    (f : M →ₗ[R] N) :
    (tensorProductLinearMapToDescentCompatible
      (R := R) (S := S) (M := M) (N := N) f :
        (S ⊗[R] M) →ₗ[S] (S ⊗[R] N)) =
      f.baseChange S :=
  rfl

/-- Faithfully flat base change is fully faithful after equipping extended
modules with their canonical Amitsur descent relation. -/
noncomputable def tensorProductLinearMapDescentEquiv
    [Module.FaithfullyFlat R S] :
    (M →ₗ[R] N) ≃ₗ[R]
      tensorProductDescentCompatibleLinearMaps
        (R := R) (S := S) (M := M) (N := N) :=
  LinearEquiv.ofBijective
    (tensorProductLinearMapToDescentCompatible
      (R := R) (S := S) (M := M) (N := N)) <| by
    constructor
    · intro f g hfg
      ext m
      apply Module.FaithfullyFlat.tensorProduct_mk_injective
        (A := R) (B := S) N
      have h := DFunLike.congr_fun
        (congrArg Subtype.val hfg) (1 ⊗ₜ[R] m)
      simpa using h
    · rintro ⟨F, hF⟩
      let e := tensorProductEqualizerEquiv
        (R := R) (S := S) (M := N)
      let lift : M →ₗ[R]
          LinearMap.eqLocus
            (tensorProductDescentLeft (R := R) (S := S) (M := N))
            (tensorProductDescentRight (R := R) (S := S) (M := N)) :=
        LinearMap.codRestrict _
          (F.restrictScalars R ∘ₗ TensorProduct.mk R S M 1) hF
      let f : M →ₗ[R] N := e.symm.toLinearMap ∘ₗ lift
      refine ⟨f, ?_⟩
      apply Subtype.ext
      apply tensorProduct_linearMap_ext_of_one_tmul
      intro m
      change (1 ⊗ₜ[R] f m : S ⊗[R] N) = F (1 ⊗ₜ[R] m)
      exact congrArg Subtype.val (e.apply_symm_apply (lift m))

@[simp]
theorem tensorProductLinearMapDescentEquiv_apply
    [Module.FaithfullyFlat R S] (f : M →ₗ[R] N) :
    ((tensorProductLinearMapDescentEquiv
      (R := R) (S := S) (M := M) (N := N)) f :
        (S ⊗[R] M) →ₗ[S] (S ⊗[R] N)) =
      f.baseChange S :=
  rfl

@[simp]
theorem tensorProductLinearMapDescentEquiv_symm_baseChange
    [Module.FaithfullyFlat R S]
    (F : tensorProductDescentCompatibleLinearMaps
      (R := R) (S := S) (M := M) (N := N)) :
    ((tensorProductLinearMapDescentEquiv
      (R := R) (S := S) (M := M) (N := N)).symm F).baseChange S =
      (F : (S ⊗[R] M) →ₗ[S] (S ⊗[R] N)) := by
  exact congrArg Subtype.val
    ((tensorProductLinearMapDescentEquiv
      (R := R) (S := S) (M := M) (N := N)).apply_symm_apply F)

end EtaleFundamentalGroups

end
