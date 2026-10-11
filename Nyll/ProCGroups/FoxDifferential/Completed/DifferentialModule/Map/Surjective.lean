/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.DifferentialModule.Map.Limit

/-!
# Fox differential: completed — differential module — map — surjective

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraMapLiftOfSurjective`
  A choice of a lift along the surjective completed group-algebra map \(\Lambda_G \to \Lambda_H\),
  independent of the displayed differential premodule topology.
- `primePowerCompletedGroupAlgebraMap_surjective`
  If \(\psi : G \to H\) is surjective, then the induced map of prime-power completed group algebras
  is surjective.
- `primePowerCompletedGroupAlgebraMap_liftOfSurjective`
  The chosen lift maps back to the target coefficient.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
If \(\psi : G \to H\) is surjective, then the induced map of prime-power completed group
algebras is surjective.
-/
theorem primePowerCompletedGroupAlgebraMap_surjective
    (ψ : ContinuousMonoidHom G H) (hψ : Function.Surjective ψ) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ) := by
  classical
  let S := primePowerCompletedGroupAlgebraSystem ℓ H
  let T := primePowerCompletedGroupAlgebraSystem ℓ G
  let f : PrimePowerCompletedGroupAlgebra ℓ G → PrimePowerCompletedGroupAlgebra ℓ H :=
    primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
  let : Nonempty (PrimePowerCompletedGroupAlgebraIndex H) :=
    ⟨(0, _root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex H)⟩
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex H, TopologicalSpace (S.X i) :=
    fun i => S.topologicalSpace i
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex H, DiscreteTopology (S.X i) :=
    fun _ => ⟨rfl⟩
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex H, CompactSpace (S.X i) :=
    fun i => by
      let : Finite (S.X i) := by
        dsimp [S, primePowerCompletedGroupAlgebraSystem]
        infer_instance
      let : Fintype (S.X i) := Fintype.ofFinite _
      infer_instance
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex H, T2Space (S.X i) :=
    fun _ => inferInstance
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, TopologicalSpace (T.X i) :=
    fun i => T.topologicalSpace i
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, DiscreteTopology (T.X i) :=
    fun _ => ⟨rfl⟩
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, CompactSpace (T.X i) :=
    fun i => by
      let : Finite (T.X i) := by
        dsimp [T, primePowerCompletedGroupAlgebraSystem]
        infer_instance
      let : Fintype (T.X i) := Fintype.ofFinite _
      infer_instance
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, T2Space (T.X i) :=
    fun _ => inferInstance
  let : CompactSpace (PrimePowerCompletedGroupAlgebra ℓ G) :=
    inferInstance
  let : T2Space (PrimePowerCompletedGroupAlgebra ℓ H) :=
    S.t2Space_inverseLimit
  have hf_continuous : Continuous f :=
    continuous_primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf_continuous).isClosed
  have hprojection_images :
      ∀ i : PrimePowerCompletedGroupAlgebraIndex H,
        S.projection i '' Set.range f =
          S.projection i '' (Set.univ : Set (PrimePowerCompletedGroupAlgebra ℓ H)) := by
    intro i
    apply Set.Subset.antisymm
    · rintro z ⟨y, _hy, rfl⟩
      exact ⟨y, trivial, rfl⟩
    · rintro z ⟨y, _hy, rfl⟩
      rcases primePowerCompletedGroupAlgebraMapStage_surjective
          (ℓ := ℓ) (G := G) (H := H) ψ hψ i (S.projection i y) with
        ⟨c, hc⟩
      let sourceIndex : PrimePowerCompletedGroupAlgebraIndex G :=
        (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)
      rcases primePowerCompletedGroupAlgebraProjection_surjective
          (ℓ := ℓ) (G := G) sourceIndex c with
        ⟨x, hx⟩
      refine ⟨f x, ⟨x, rfl⟩, ?_⟩
      change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := H) i
          (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ x) =
        S.projection i y
      rw [primePowerCompletedGroupAlgebraProjection_map]
      change primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) sourceIndex x) =
        S.projection i y
      rw [hx, hc]
  have hclosure :
      closure (Set.range f) =
        (Set.univ : Set (PrimePowerCompletedGroupAlgebra ℓ H)) := by
    have hclosure' :
        closure (Set.range f) =
          closure (Set.univ : Set (PrimePowerCompletedGroupAlgebra ℓ H)) :=
        S.closure_eq_of_projection_images_eq_of_subsets
          (directed_primePowerCompletedGroupAlgebraIndex (G := H))
        (Set.range f)
        (Set.univ : Set (PrimePowerCompletedGroupAlgebra ℓ H))
        hprojection_images
    simpa using hclosure'
  intro y
  have hy_closure : y ∈ closure (Set.range f) := by
    rw [hclosure]
    simp only [Set.mem_univ]
  have hy_range : y ∈ Set.range f := by
    rwa [hclosed.closure_eq] at hy_closure
  rcases hy_range with ⟨x, hx⟩
  exact ⟨x, hx⟩

/--
A choice of a lift along the surjective completed group-algebra map \(\Lambda_G \to \Lambda_H\),
independent of the displayed differential premodule topology.
-/
def primePowerCompletedGroupAlgebraMapLiftOfSurjective
    (ψ : ContinuousMonoidHom G H) (hψ : Function.Surjective ψ)
    (a : PrimePowerCompletedGroupAlgebra ℓ H) :
    PrimePowerCompletedGroupAlgebra ℓ G :=
  Classical.choose
    (primePowerCompletedGroupAlgebraMap_surjective
      (ℓ := ℓ) (G := G) (H := H) ψ hψ a)

/-- The chosen lift maps back to the target coefficient. -/
@[simp]
theorem primePowerCompletedGroupAlgebraMap_liftOfSurjective
    (ψ : ContinuousMonoidHom G H) (hψ : Function.Surjective ψ)
    (a : PrimePowerCompletedGroupAlgebra ℓ H) :
    primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
        (primePowerCompletedGroupAlgebraMapLiftOfSurjective
          (ℓ := ℓ) (G := G) (H := H) ψ hψ a) = a :=
  Classical.choose_spec
    (primePowerCompletedGroupAlgebraMap_surjective
      (ℓ := ℓ) (G := G) (H := H) ψ hψ a)

end

end FoxDifferential
