/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteAbelianization
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
public import Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.IdeleClassConnectedQuotient
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel

/-!
# Topological global reciprocity in Mathlib's groups

The maximal-abelian Artin isomorphism acts on the standard idèle-class
quotient. The canonical comparison of absolute Galois abelianizations
gives the named Artin map on the original number field.
-/

@[expose] public section

open scoped NumberField

noncomputable section

universe u

namespace GlobalClassFieldTheory.Reciprocity

/-- The maximal-abelian Artin isomorphism, expressed entirely in Mathlib's
idèle-class and absolute-Galois groups, on the original number-field carrier. -/
noncomputable def mathlibIdeleClassConnectedQuotientEquivAbelianization
    (K : Type u) [Field K] [NumberField K] :
    ClassFieldTheory.IdeleClassConnectedQuotient K ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K := by
  exact (ideleClassComponentQuotientEquivMaximalAbelianGalois K).trans
    ((absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K).symm.trans
      (absoluteGaloisGroupAbelianizationEquivSeparable K).symm)

/-- The named continuous Artin map on Mathlib's idèle class group. It keeps
the geometric normalization of the existing maximal-abelian construction. -/
noncomputable def mathlibGlobalArtin
    (K : Type u) [Field K] [NumberField K] :
    NumberField.IdeleClassGroup (𝓞 K) K →ₜ*
      Field.absoluteGaloisGroupAbelianization K :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (mathlibIdeleClassConnectedQuotientEquivAbelianization K)).comp
    { toMonoidHom := QuotientGroup.mk'
        (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K))
      continuous_toFun := QuotientGroup.continuous_mk }

/-- Evaluation uses the specified quotient isomorphism on the same class. -/
theorem mathlibGlobalArtin_apply
    (K : Type u) [Field K] [NumberField K]
    (c : NumberField.IdeleClassGroup (𝓞 K) K) :
    mathlibGlobalArtin K c =
      mathlibIdeleClassConnectedQuotientEquivAbelianization K
        (QuotientGroup.mk'
          (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)) c) :=
  rfl

/-- The named Artin map is surjective. -/
theorem mathlibGlobalArtin_surjective
    (K : Type u) [Field K] [NumberField K] :
    Function.Surjective (mathlibGlobalArtin K) :=
  (mathlibIdeleClassConnectedQuotientEquivAbelianization K).surjective.comp
    (QuotientGroup.mk'_surjective _)

/-- The kernel is the actual identity component of Mathlib's idèle class group. -/
theorem mathlibGlobalArtin_ker
    (K : Type u) [Field K] [NumberField K] :
    (mathlibGlobalArtin K).toMonoidHom.ker =
      Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K) := by
  ext c
  change (mathlibIdeleClassConnectedQuotientEquivAbelianization K).toMulEquiv
      (QuotientGroup.mk'
        (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)) c) = 1 ↔ _
  rw [(mathlibIdeleClassConnectedQuotientEquivAbelianization K).map_eq_one_iff]
  exact QuotientGroup.eq_one_iff c

end GlobalClassFieldTheory.Reciprocity
