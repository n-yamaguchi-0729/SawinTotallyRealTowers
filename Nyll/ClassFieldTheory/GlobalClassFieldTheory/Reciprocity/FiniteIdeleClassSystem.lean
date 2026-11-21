/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardFieldInclusion
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.FieldEquivNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Equiv
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Standard finite levels over a number field

For any number field, its finite Galois intermediate fields in the chosen
separable closure index Mathlib's actual idele class groups. Field equivalences
act by transport, and the transitions are canonical scalar inclusions.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The algebra on the chosen separable closure uses its actual realization
inside the algebraic closure. -/
@[reducible] instance numberFieldSeparableClosureAlgebra : Algebra K (SeparableClosure K) :=
  let : Algebra K (AlgebraicClosure K) := AlgebraicClosure.instAlgebra K
  IntermediateField.algebra' (R' := K) (separableClosure K (AlgebraicClosure K))

/-- Intermediate fields retain their actual inclusion algebra. -/
@[reducible] instance numberFieldIntermediateFieldAlgebra
    (E : IntermediateField K (SeparableClosure K)) : Algebra K E :=
  IntermediateField.algebra' (R' := K) E

/-- A finite extension of the base number field is a number field. -/
instance numberFieldIntermediateFieldNumberField
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] : NumberField E :=
  NumberField.of_module_finite K E

/-- Standard class inclusion along the specified intermediate-field inclusion.
The local algebra supplier is induced by that exact inclusion. -/
def finiteIdeleClassEmbedding
    {E F : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K E] [FiniteDimensional K F] (h : E ≤ F) :
    NumberField.IdeleClassGroup (𝓞 E) E →* NumberField.IdeleClassGroup (𝓞 F) F := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact NumberField.IdeleClassGroup.fieldInclusion E F

/-- Standard class inclusion at one level is the identity. -/
theorem finiteIdeleClassEmbedding_self
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (c : NumberField.IdeleClassGroup (𝓞 E) E) :
    finiteIdeleClassEmbedding K (show E ≤ E from le_rfl) c = c := by
  exact DFunLike.congr_fun (NumberField.IdeleClassGroup.fieldInclusion_self E) c

/-- Standard class inclusions compose along the actual field tower. -/
theorem finiteIdeleClassEmbedding_comp
    {E F H : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K E] [FiniteDimensional K F] [FiniteDimensional K H]
    (hEF : E ≤ F) (hFH : F ≤ H) (c : NumberField.IdeleClassGroup (𝓞 E) E) :
    finiteIdeleClassEmbedding K hFH (finiteIdeleClassEmbedding K hEF c) =
      finiteIdeleClassEmbedding K (hEF.trans hFH) c := by
  let : Algebra E F := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : Algebra F H := (IntermediateField.inclusion hFH).toRingHom.toAlgebra
  let : Algebra E H := (IntermediateField.inclusion (hEF.trans hFH)).toRingHom.toAlgebra
  let : IsScalarTower E F H := IsScalarTower.of_algebraMap_eq' rfl
  exact DFunLike.congr_fun (NumberField.IdeleClassGroup.fieldInclusion_comp E H F) c

/-- The canonical scalar inclusion is injective on each standard finite level. -/
theorem finiteIdeleClassEmbedding_injective
    {E F : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K E] [FiniteDimensional K F] (h : E ≤ F) :
    Function.Injective (finiteIdeleClassEmbedding K h) := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact NumberField.IdeleClassGroup.fieldInclusion_injective E F

/-- Restriction to a finite normal level, regarded as a rational field
isomorphism for the standard idele transport. -/
def finiteIdeleClassAutomorphism
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    (SeparableClosure K ≃ₐ[K] SeparableClosure K) →* (E ≃ₐ[ℚ] E) :=
  (AlgEquiv.restrictScalarsHom ℚ).comp (AlgEquiv.restrictNormalHom E)

/-- The absolute action on a standard finite idele-class group is induced by
the restricted field automorphism. -/
@[reducible] def absoluteGaloisFiniteIdeleClassAction
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    MulDistribMulAction (SeparableClosure K ≃ₐ[K] SeparableClosure K)
      (NumberField.IdeleClassGroup (𝓞 E) E) :=
  NumberField.IdeleClassGroup.actionOfFieldHom (finiteIdeleClassAutomorphism K E)

instance finiteGaloisIdeleClassMulDistribMulAction
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    MulDistribMulAction (SeparableClosure K ≃ₐ[K] SeparableClosure K)
      (NumberField.IdeleClassGroup (𝓞 E) E) :=
  absoluteGaloisFiniteIdeleClassAction K E

/-- The finite-level action keeps the original standard idele representative. -/
theorem absoluteGaloisFiniteIdeleClass_smul_mk
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (a : NumberField.IdeleGroup (𝓞 E) E) :
    σ • QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 E) E) a =
      QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 E) E)
        (NumberField.IdeleGroup.congr (finiteIdeleClassAutomorphism K E σ) a) := rfl

/-- Canonical inclusion intertwines the actual restricted field actions. -/
theorem finiteIdeleClassEmbedding_smul
    {E F : FiniteGaloisIntermediateField K (SeparableClosure K)} (h : E ≤ F)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (c : NumberField.IdeleClassGroup (𝓞 E) E) :
    finiteIdeleClassEmbedding K h (σ • c) = σ • finiteIdeleClassEmbedding K h c := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  apply (NumberField.IdeleClassGroup.congr_fieldInclusion
    (finiteIdeleClassAutomorphism K E σ) (finiteIdeleClassAutomorphism K F σ) ?_ c).symm
  intro x
  apply Subtype.ext
  exact (AlgEquiv.restrictNormal_commutes σ F (IntermediateField.inclusion h x)).trans
    (AlgEquiv.restrictNormal_commutes σ E x).symm

/-- The equivariant canonical transition on standard finite idele-class groups. -/
def finiteIdeleClassTransition
    {E F : FiniteGaloisIntermediateField K (SeparableClosure K)} (h : E ≤ F) :
    MulDistribMulActionHom
      (MonoidHom.id (SeparableClosure K ≃ₐ[K] SeparableClosure K))
      (NumberField.IdeleClassGroup (𝓞 E) E) (NumberField.IdeleClassGroup (𝓞 F) F) where
  toMonoidHom := finiteIdeleClassEmbedding K h
  map_smul' σ c := finiteIdeleClassEmbedding_smul K h σ c

/-- One directed system of actual standard class groups and equivariant transitions. -/
instance finiteIdeleClassDirectedSystem :
    DirectedSystem
      (fun E : FiniteGaloisIntermediateField K (SeparableClosure K) =>
        NumberField.IdeleClassGroup (𝓞 E) E)
      (fun _ _ h => finiteIdeleClassTransition K h) where
  map_self {i} c := finiteIdeleClassEmbedding_self K i c
  map_map {k j i} hIJ hJK c := finiteIdeleClassEmbedding_comp K
    (E := i.toIntermediateField) (F := j.toIntermediateField) (H := k.toIntermediateField)
    hIJ hJK c

end GlobalClassFieldTheory.Reciprocity
