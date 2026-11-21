/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardClassComparison

/-! # The standard idèle class representation of a finite Galois group -/

@[expose] public section

open CategoryTheory
open scoped NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

section Standard

universe u v

variable (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local instance : MulDistribMulAction Gal(L/K) (NumberField.IdeleClassGroup (𝓞 L) L) :=
  NumberField.IdeleClassGroup.relativeGaloisAction K L

/-- The standard idèle class group with its action by field conjugation. -/
abbrev standardIdeleClassRep : Rep.{v} ℤ Gal(L/K) :=
  Rep.ofMulDistribMulAction Gal(L/K) (NumberField.IdeleClassGroup (𝓞 L) L)

end Standard

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local instance : MulDistribMulAction Gal(L/K) (RelativeIdeleGroup.ClassGroup K L) :=
  RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L

/-- The actual relative-to-standard comparison intertwines Galois conjugation. -/
def relativeToStandardIdeleClassRepIso :
    Rep.ofMulDistribMulAction Gal(L/K) (RelativeIdeleGroup.ClassGroup K L) ≅
      standardIdeleClassRep K L := by
  let e := NumberField.IdeleClassGroup.relativeClassComparison K L
  refine Rep.mkIso (Representation.Equiv.mk e.toAdditive.toIntLinearEquiv ?_)
  intro σ
  apply LinearMap.ext
  intro a
  exact congrArg Additive.ofMul
    (NumberField.IdeleClassGroup.relativeClassComparison_conjugation K L σ a.toMul)

end GlobalClassFieldTheory.Cohomology
