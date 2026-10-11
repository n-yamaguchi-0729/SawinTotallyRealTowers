/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.DifferentialModule.Map.Stage

/-!
# Fox differential: completed — differential module — map — limit

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraMap`
  The ring homomorphism on prime-power completed group algebras induced stagewise by a continuous
  group homomorphism.
- `primePowerCompletedGroupAlgebraProjection_map`
  The finite-stage Fox-differential projection is computed by the prime-power completed
  group-algebra projection formula.
- `continuous_primePowerCompletedGroupAlgebraMap`
  The completed group-algebra map induced by a continuous homomorphism is continuous for the
  inverse-limit topologies.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The ring homomorphism on prime-power completed group algebras induced stagewise by a continuous
group homomorphism.
-/
def primePowerCompletedGroupAlgebraMap
    (ψ : ContinuousMonoidHom G H) :
    PrimePowerCompletedGroupAlgebra ℓ G →+* PrimePowerCompletedGroupAlgebra ℓ H where
  toFun x := ⟨fun i =>
      primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
          (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x), by
    intro i j hij
    let hsource :
        (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) ≤
          (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2) :=
      ⟨hij.1, completedGroupAlgebraComapIndex_mono (G := G) (H := H) ψ hij.2⟩
    have hx := x.2
      (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)
      (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2)
      hsource
    change
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hsource
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
            (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2) x) =
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
          (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x at hx
    have hcompat := congrFun
      (congrArg DFunLike.coe
        (primePowerCompletedGroupAlgebraMapStage_compatible
          (ℓ := ℓ) (G := G) (H := H) ψ hij))
      (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
        (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2) x)
    rw [RingHom.comp_apply, RingHom.comp_apply] at hcompat
    rw [hx] at hcompat
    simpa [primePowerCompletedGroupAlgebraSystem] using hcompat⟩
  map_one' := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ H).ext
    intro i
    change
      primePowerCompletedGroupAlgebraMapStage
          (ℓ := ℓ) (G := G) (H := H) ψ i 1 = 1
    exact map_one _
  map_mul' := by
    intro x y
    apply (primePowerCompletedGroupAlgebraSystem ℓ H).ext
    intro i
    change
      primePowerCompletedGroupAlgebraMapStage
          (ℓ := ℓ) (G := G) (H := H) ψ i
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
            (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x *
           primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
            (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) y) =
        primePowerCompletedGroupAlgebraMapStage
            (ℓ := ℓ) (G := G) (H := H) ψ i
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
              (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x) *
          primePowerCompletedGroupAlgebraMapStage
            (ℓ := ℓ) (G := G) (H := H) ψ i
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
              (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) y)
    exact map_mul _ _ _
  map_zero' := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ H).ext
    intro i
    change
      primePowerCompletedGroupAlgebraMapStage
          (ℓ := ℓ) (G := G) (H := H) ψ i 0 = 0
    exact map_zero _
  map_add' := by
    intro x y
    apply (primePowerCompletedGroupAlgebraSystem ℓ H).ext
    intro i
    change
      primePowerCompletedGroupAlgebraMapStage
          (ℓ := ℓ) (G := G) (H := H) ψ i
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
            (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x +
           primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
            (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) y) =
        primePowerCompletedGroupAlgebraMapStage
            (ℓ := ℓ) (G := G) (H := H) ψ i
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
              (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x) +
          primePowerCompletedGroupAlgebraMapStage
            (ℓ := ℓ) (G := G) (H := H) ψ i
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
              (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) y)
    exact map_add _ _ _

/--
The finite-stage Fox-differential projection is computed by the prime-power completed
group-algebra projection formula.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_map
    (ψ : ContinuousMonoidHom G H) (i : PrimePowerCompletedGroupAlgebraIndex H)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := H) i
        (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ x) =
      primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
          (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x) := rfl


/--
The completed group-algebra map induced by a continuous homomorphism is continuous for the
inverse-limit topologies.
-/
theorem continuous_primePowerCompletedGroupAlgebraMap
    (ψ : ContinuousMonoidHom G H) :
    Continuous (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ) := by
  let S := primePowerCompletedGroupAlgebraSystem ℓ H
  let T := primePowerCompletedGroupAlgebraSystem ℓ G
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex H, TopologicalSpace (S.X i) :=
    fun i => S.topologicalSpace i
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, TopologicalSpace (T.X i) :=
    fun i => T.topologicalSpace i
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) (fun x =>
    (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ x).2)
  let sourceIndex : PrimePowerCompletedGroupAlgebraIndex G :=
    (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)
  let : TopologicalSpace (PrimePowerCompletedGroupAlgebraStage ℓ G sourceIndex) :=
    T.topologicalSpace sourceIndex
  let : DiscreteTopology (PrimePowerCompletedGroupAlgebraStage ℓ G sourceIndex) := ⟨rfl⟩
  let : TopologicalSpace (PrimePowerCompletedGroupAlgebraStage ℓ H i) :=
    S.topologicalSpace i
  have hstage :
      Continuous
        (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i) :=
    continuous_of_discreteTopology
  change Continuous (fun x : PrimePowerCompletedGroupAlgebra ℓ G =>
    primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
      (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) sourceIndex x))
  exact hstage.comp (T.continuous_projection sourceIndex)

end

end FoxDifferential
