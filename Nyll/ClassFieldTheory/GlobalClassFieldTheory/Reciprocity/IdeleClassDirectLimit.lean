/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleClassSystem
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# The absolute idele-class direct limit over a number field

One directed limit of the standard finite idele-class groups carries the
absolute action. The rational construction is its specialization at `ℚ`.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The direct limit of the actual idele class groups of the finite
Galois subextensions of `SeparableClosure K / K`. -/
noncomputable abbrev ideleClassDirectLimit :=
  DirectLimit
    (fun E : FiniteGaloisIntermediateField K (SeparableClosure K) =>
      NumberField.IdeleClassGroup (𝓞 E) E)
    (fun _ _ h => finiteIdeleClassTransition K h)

/-- The multiplicative structure on the absolute idele-class
direct limit supplied by Mathlib's directed-limit construction. -/
noncomputable abbrev ideleClassDirectLimitMonoid :
    Monoid (ideleClassDirectLimit K) :=
  inferInstance

theorem ideleClassDirectLimit_mk_apply
    {E F : FiniteGaloisIntermediateField K (SeparableClosure K)}
    (c : NumberField.IdeleClassGroup (𝓞 E) E)
    (h : E ≤ F) :
    (⟦⟨F, finiteIdeleClassEmbedding K h c⟩⟧ :
        (ideleClassDirectLimit K)) =
      ⟦⟨E, c⟩⟧ := by
  exact
    DirectLimit.mk_apply
      (F := fun E :
        FiniteGaloisIntermediateField K (SeparableClosure K) =>
          NumberField.IdeleClassGroup (𝓞 E) E)
      (f := fun _ _ h =>
        finiteIdeleClassTransition K h)
      E F c h

/-- The canonical map from one standard finite-level idele class group
to the directed limit. -/
def finiteIdeleClassToDirectLimit
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    NumberField.IdeleClassGroup (𝓞 E) E →*
      (ideleClassDirectLimit K) where
  toFun c := ⟦⟨E, c⟩⟧
  map_one' := by
    exact
      (DirectLimit.one_def
        (G := fun E :
          FiniteGaloisIntermediateField K (SeparableClosure K) =>
            NumberField.IdeleClassGroup (𝓞 E) E)
        (f := fun _ _ h =>
          finiteIdeleClassTransition K h)
        E).symm
  map_mul' c d := by
    exact
      (DirectLimit.mul_def
        (G := fun E :
          FiniteGaloisIntermediateField K (SeparableClosure K) =>
            NumberField.IdeleClassGroup (𝓞 E) E)
        (f := fun _ _ h =>
          finiteIdeleClassTransition K h)
        E c d).symm

/-- The absolute Galois action on the idele-class direct limit,
supplied by Mathlib from the equivariant transition maps. -/
noncomputable instance
    ideleClassDirectLimitMulDistribMulAction :
    MulDistribMulAction
      (SeparableClosure K ≃ₐ[K] SeparableClosure K)
      (ideleClassDirectLimit K) := by
  let transitionMonoidHom
      (E F : FiniteGaloisIntermediateField K (SeparableClosure K)) :
      MonoidHomClass
        (MulDistribMulActionHom
          (MonoidHom.id (SeparableClosure K ≃ₐ[K] SeparableClosure K))
          (NumberField.IdeleClassGroup (𝓞 E) E) (NumberField.IdeleClassGroup (𝓞 F) F))
        (NumberField.IdeleClassGroup (𝓞 E) E) (NumberField.IdeleClassGroup (𝓞 F) F) :=
    inferInstance
  let transitionActionHom
      (E F : FiniteGaloisIntermediateField K (SeparableClosure K)) :
      MulActionHomClass
        (MulDistribMulActionHom
          (MonoidHom.id (SeparableClosure K ≃ₐ[K] SeparableClosure K))
          (NumberField.IdeleClassGroup (𝓞 E) E) (NumberField.IdeleClassGroup (𝓞 F) F))
        (SeparableClosure K ≃ₐ[K] SeparableClosure K)
        (NumberField.IdeleClassGroup (𝓞 E) E) (NumberField.IdeleClassGroup (𝓞 F) F) :=
    inferInstance
  exact inferInstanceAs (MulDistribMulAction
    (SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (DirectLimit
      (fun E : FiniteGaloisIntermediateField K (SeparableClosure K) =>
        NumberField.IdeleClassGroup (𝓞 E) E)
      (fun _ _ h => finiteIdeleClassTransition K h)))

/-- The scalar action underlying the canonical absolute Galois action on
the idele-class direct limit. -/
noncomputable abbrev ideleClassDirectLimitSMul :
    SMul
      (SeparableClosure K ≃ₐ[K] SeparableClosure K)
      (ideleClassDirectLimit K) :=
  (ideleClassDirectLimitMulDistribMulAction K).toSMul

/-- Each standard finite level injects into the one absolute direct limit. -/
theorem finiteIdeleClassToDirectLimit_injective
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    Function.Injective (finiteIdeleClassToDirectLimit K E) :=
  DirectLimit.mk_injective
    (F := fun E : FiniteGaloisIntermediateField K (SeparableClosure K) =>
      NumberField.IdeleClassGroup (𝓞 E) E)
    (f := fun _ _ h => finiteIdeleClassTransition K h)
    (fun _ _ h => finiteIdeleClassEmbedding_injective K h) E

/-- The canonical finite-level map intertwines the same absolute Galois action. -/
theorem finiteIdeleClassToDirectLimit_smul
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (c : NumberField.IdeleClassGroup (𝓞 E) E) :
    (ideleClassDirectLimitSMul K).smul σ (finiteIdeleClassToDirectLimit K E c) =
      finiteIdeleClassToDirectLimit K E (σ • c) :=
  DirectLimit.smul_def
    (G := fun E : FiniteGaloisIntermediateField K (SeparableClosure K) =>
      NumberField.IdeleClassGroup (𝓞 E) E)
    (f := fun _ _ h => finiteIdeleClassTransition K h) E c σ

/-- The coefficient representation on the single absolute idele-class limit. -/
def ideleClassRepresentation : Rep ℤ (SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
  Rep.ofMulDistribMulAction
    (SeparableClosure K ≃ₐ[K] SeparableClosure K) (ideleClassDirectLimit K)

end GlobalClassFieldTheory.Reciprocity
