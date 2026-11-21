/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtin
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison

/-!
# Descent of the infinite global Artin homomorphism

The finite global Artin product formula at every finite Galois intermediate
field shows that the infinite global Artin homomorphism kills principal ideles.
This file descends that homomorphism to the idele class group and retains its
ordinary quotient topology.
-/



@[expose] public section

open scoped NumberField

noncomputable section

universe u v

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K : Type u} {Ω : Type v}
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]

private theorem
    continuousMulEquivToLimit_infiniteGlobalArtinMonoidHom_apply
    (a : IdeleGroup K) :
    InfiniteGalois.continuousMulEquivToLimit K Ω
        (infiniteGlobalArtinMonoidHom K Ω a) =
      infiniteGlobalArtinToLimit K Ω a := by
  exact
    (InfiniteGalois.continuousMulEquivToLimit K Ω).apply_symm_apply _

/-- The infinite global Artin homomorphism is trivial on every principal
idele. -/
@[simp]
theorem infiniteGlobalArtinMonoidHom_principalIdele
    (x : Kˣ) :
    infiniteGlobalArtinMonoidHom K Ω
        (IdeleGroup.principalIdele K x) =
      1 := by
  let (E : FiniteGaloisIntermediateField K Ω) : NumberField E :=
    NumberField.of_module_finite K E
  let (E : FiniteGaloisIntermediateField K Ω) : IsAbelianGalois K E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  apply (InfiniteGalois.continuousMulEquivToLimit K Ω).injective
  rw [
    continuousMulEquivToLimit_infiniteGlobalArtinMonoidHom_apply,
    map_one]
  apply Subtype.ext
  funext E
  exact
    globalArtinMonoidHom_principalIdele
      (K := K) (L := E.unop) x

/-- The infinite global Artin map descended to the topological idèle class group. -/
noncomputable def infiniteGlobalIdeleClassArtinContinuousMonoidHom :
    IdeleClassGroup K →ₜ* (Ω ≃ₐ[K] Ω) :=
  IdeleGroup.liftContinuousToStandardClass K
    (infiniteGlobalArtinMonoidHom K Ω)
    (by
      intro a ha
      change infiniteGlobalArtinMonoidHom K Ω a = 1
      rcases ha with ⟨x, rfl⟩
      exact infiniteGlobalArtinMonoidHom_principalIdele (K := K) (Ω := Ω) x)

/-- The underlying homomorphism of the continuous infinite Artin map. -/
noncomputable abbrev infiniteGlobalIdeleClassArtinMonoidHom :
    IdeleClassGroup K →* (Ω ≃ₐ[K] Ω) :=
  (infiniteGlobalIdeleClassArtinContinuousMonoidHom (K := K) (Ω := Ω)).toMonoidHom

/-- Evaluation of the descended infinite global Artin homomorphism on an idele
representative recovers the original infinite Artin homomorphism. -/
@[simp]
theorem infiniteGlobalIdeleClassArtinMonoidHom_mk
    (a : IdeleGroup K) :
    infiniteGlobalIdeleClassArtinMonoidHom
        (K := K) (Ω := Ω)
        (IdeleGroup.toStandardClass K a) =
      infiniteGlobalArtinMonoidHom K Ω a := by
  change infiniteGlobalIdeleClassArtinContinuousMonoidHom (K := K) (Ω := Ω)
    (IdeleGroup.toStandardClass K a) = infiniteGlobalArtinMonoidHom K Ω a
  simp only [infiniteGlobalIdeleClassArtinContinuousMonoidHom,
    IdeleGroup.liftContinuousToStandardClass_toStandardClass]

/-- The underlying infinite Artin homomorphism is continuous. -/
theorem infiniteGlobalIdeleClassArtinMonoidHom_continuous :
    Continuous (infiniteGlobalIdeleClassArtinMonoidHom (K := K) (Ω := Ω)) :=
  (infiniteGlobalIdeleClassArtinContinuousMonoidHom (K := K) (Ω := Ω)).continuous_toFun

/-- The descended infinite global Artin homomorphism has dense image in the
Krull topology. -/
theorem infiniteGlobalIdeleClassArtinContinuousMonoidHom_denseRange :
    DenseRange
      (infiniteGlobalIdeleClassArtinContinuousMonoidHom
        (K := K) (Ω := Ω)) := by
  refine
    (infiniteGlobalArtinMonoidHom_denseRange K Ω).mono ?_
  rintro σ ⟨a, rfl⟩
  refine ⟨IdeleGroup.toStandardClass K a, ?_⟩
  exact
    infiniteGlobalIdeleClassArtinMonoidHom_mk
      (K := K) (Ω := Ω) a

end Reciprocity
end GlobalClassFieldTheory
