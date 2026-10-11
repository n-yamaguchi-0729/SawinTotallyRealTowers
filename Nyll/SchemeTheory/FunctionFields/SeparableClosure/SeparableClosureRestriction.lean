/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.LinearDisjoint

/-!
# Restriction to a separable closure in a common overfield

For a tower of fields `k ⊆ K ⊆ Ω`, every `K`-automorphism of `Ω`
restricts to the separable closure of `k` inside `Ω`. When `Ω` is a
separable closure of `K`, this restriction map is surjective provided that
`K` and the separable closure of `k` are linearly disjoint over `k`.

The surjectivity proof extends an automorphism across the tensor compositum;
linear disjointness supplies the field structure on that tensor product.
-/

@[expose] public section

noncomputable section

universe u v w

open IntermediateField

namespace EtaleFundamentalGroups

variable {k : Type u} {K : Type v} {Ω : Type w}
variable [Field k] [Field K] [Field Ω]
variable [Algebra k K] [Algebra K Ω] [Algebra k Ω]
variable [IsScalarTower k K Ω]

/-- Restriction of `K`-automorphisms of a common overfield to the separable
closure of `k` in that overfield. -/
noncomputable def separableClosureRestriction :
    (Ω ≃ₐ[K] Ω) →* (separableClosure k Ω ≃ₐ[k] separableClosure k Ω) where
  toFun σ := separableClosure.algEquivOfAlgEquiv (σ.restrictScalars k)
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

@[simp]
theorem separableClosureRestriction_coe
    (σ : Ω ≃ₐ[K] Ω) (x : separableClosure k Ω) :
    ((separableClosureRestriction (k := k) (K := K) (Ω := Ω) σ x :
      separableClosure k Ω) : Ω) = σ (x : Ω) :=
  rfl

/-- If `Ω` is a separable closure of `K` and the separable closure of `k`
inside `Ω` is linearly disjoint from `K`, every automorphism of that
separable closure over `k` extends to a `K`-automorphism of `Ω`. -/
theorem separableClosureRestriction_surjective_of_linearDisjoint
    [IsSepClosure K Ω]
    (h : (separableClosure k Ω).LinearDisjoint K) :
    Function.Surjective
      (separableClosureRestriction (k := k) (K := K) (Ω := Ω)) := by
  intro σ
  let S := separableClosure k Ω
  let T := TensorProduct k K S
  let iK : K →ₐ[k] Ω := IsScalarTower.toAlgHom k K Ω
  have hField : IsField T := by
    have hDomain : IsDomain T := by
      apply IntermediateField.LinearDisjoint.isDomain'
        (E := Ω) (fa := iK) (fb := S.val)
      rw [IntermediateField.fieldRange_val]
      have h' : S.LinearDisjoint iK.fieldRange := by
        rw [IntermediateField.linearDisjoint_iff']
        exact h
      exact h'.symm
    exact Algebra.TensorProduct.isField_of_isAlgebraic k K S (.inr inferInstance)
  let : Field T := hField.toField
  let j : T →ₐ[K] Ω :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Ω) S.val
  let jσ : T →ₐ[K] Ω :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Ω)
      (S.val.comp σ.toAlgHom)
  let : Algebra T Ω := j.toRingHom.toAlgebra
  let : IsScalarTower K T Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  have : Algebra.IsSeparable T Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K T Ω
  let : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨f, hf⟩ :=
    (IsSepClosed.surjective_domRestrict_of_isSeparable
      (K := K) T (M := Ω) (E := Ω)) jσ
  let e : Ω ≃ₐ[K] Ω :=
    AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective f)
  refine ⟨e, ?_⟩
  ext x
  change e (x : Ω) = (σ x : Ω)
  have hx := DFunLike.congr_fun hf
    (Algebra.TensorProduct.includeRight x)
  change f (j (Algebra.TensorProduct.includeRight x)) =
    jσ (Algebra.TensorProduct.includeRight x) at hx
  change f ((Algebra.TensorProduct.lift (Algebra.ofId K Ω) S.val
    (fun _ _ => Commute.all _ _)) (1 ⊗ₜ[k] x)) =
    (Algebra.TensorProduct.lift (Algebra.ofId K Ω)
      (S.val.comp σ.toAlgHom) (fun _ _ => Commute.all _ _)) (1 ⊗ₜ[k] x) at hx
  rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul] at hx
  simpa [e] using hx

end EtaleFundamentalGroups
