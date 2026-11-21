/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PositiveArchimedeanSection
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinDescent
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic

/-!
# Surjectivity of the infinite global Artin homomorphism

The absolute idele norm is split, up to inversion, by an idele supported at
one infinite place.  Its local component is positive, so every finite global
Artin homomorphism, and hence the infinite global Artin homomorphism, kills
it.  Multiplication by this section therefore replaces any idele by a
norm-one idele without changing its Artin symbol.
-/



@[expose] public section

open scoped IsMulCommutative NNReal NumberField Topology
open NumberField IsDedekindDomain
open NumberField.Units.dirichletUnitTheorem

noncomputable section

universe u v

namespace GlobalClassFieldTheory
namespace Reciprocity

private theorem
    infiniteGlobalIdeleClassArtinContinuousMonoidHom_normOne_denseRange
    (K : Type u) (Ω : Type v)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    DenseRange
      (fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
        infiniteGlobalIdeleClassArtinContinuousMonoidHom
          (K := K) (Ω := Ω) (c : IdeleClassGroup K)) := by
  apply
    (infiniteGlobalIdeleClassArtinContinuousMonoidHom_denseRange
      (K := K) (Ω := Ω)).mono
  rintro σ ⟨c, rfl⟩
  obtain ⟨a, rfl⟩ := IdeleGroup.toStandardClass_surjective K c
  obtain ⟨b, hb⟩ :=
    exists_normOneIdele_same_infiniteGlobalArtin K Ω a
  let d : IdeleClassGroup.normOneSubgroup (K := K) :=
    ⟨IdeleGroup.toStandardClass K (b : IdeleGroup K),
      (IdeleClassGroup.mk_mem_normOneSubgroup_iff
        (b : IdeleGroup K)).2 b.2⟩
  refine ⟨d, ?_⟩
  change
    infiniteGlobalIdeleClassArtinMonoidHom
        (K := K) (Ω := Ω)
        (IdeleGroup.toStandardClass K (b : IdeleGroup K)) =
      infiniteGlobalIdeleClassArtinMonoidHom
        (K := K) (Ω := Ω)
        (IdeleGroup.toStandardClass K a)
  rw [infiniteGlobalIdeleClassArtinMonoidHom_mk,
    infiniteGlobalIdeleClassArtinMonoidHom_mk]
  exact hb

private theorem
    infiniteGlobalIdeleClassArtinContinuousMonoidHom_normOne_surjective
    (K : Type u) (Ω : Type v)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    Function.Surjective
      (fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
        infiniteGlobalIdeleClassArtinContinuousMonoidHom
          (K := K) (Ω := Ω) (c : IdeleClassGroup K)) := by
  let f :=
    fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
      infiniteGlobalIdeleClassArtinContinuousMonoidHom
        (K := K) (Ω := Ω) (c : IdeleClassGroup K)
  have hf : Continuous f := by
    exact
      (infiniteGlobalIdeleClassArtinContinuousMonoidHom
        (K := K) (Ω := Ω)).continuous_toFun.comp
          continuous_subtype_val
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf).isClosed
  have hdense : DenseRange f := by
    simpa only [f] using
      (infiniteGlobalIdeleClassArtinContinuousMonoidHom_normOne_denseRange
        K Ω)
  intro σ
  have hσ : σ ∈ closure (Set.range f) := by
    rw [hdense.closure_range]
    trivial
  rwa [hclosed.closure_eq] at hσ

/-- The infinite global Artin homomorphism on idele classes is surjective. -/
theorem infiniteGlobalIdeleClassArtinContinuousMonoidHom_surjective
    (K : Type u) (Ω : Type v)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    Function.Surjective
      (infiniteGlobalIdeleClassArtinContinuousMonoidHom
        (K := K) (Ω := Ω)) := by
  intro σ
  obtain ⟨c, hc⟩ :=
    infiniteGlobalIdeleClassArtinContinuousMonoidHom_normOne_surjective
      K Ω σ
  exact ⟨(c : IdeleClassGroup K), hc⟩

/-- The infinite global Artin homomorphism is surjective. -/
theorem infiniteGlobalArtinMonoidHom_surjective
    (K : Type u) (Ω : Type v)
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    Function.Surjective
      (infiniteGlobalArtinMonoidHom K Ω) := by
  intro σ
  obtain ⟨c, hc⟩ :=
    infiniteGlobalIdeleClassArtinContinuousMonoidHom_surjective
      K Ω σ
  obtain ⟨a, ha⟩ := IdeleGroup.toStandardClass_surjective K c
  refine ⟨a, ?_⟩
  calc
    infiniteGlobalArtinMonoidHom K Ω a =
        infiniteGlobalIdeleClassArtinContinuousMonoidHom
          (K := K) (Ω := Ω)
          (IdeleGroup.toStandardClass K a) :=
      (infiniteGlobalIdeleClassArtinMonoidHom_mk
        (K := K) (Ω := Ω) a).symm
    _ = infiniteGlobalIdeleClassArtinContinuousMonoidHom
          (K := K) (Ω := Ω) c := by rw [ha]
    _ = σ := hc

end Reciprocity
end GlobalClassFieldTheory
