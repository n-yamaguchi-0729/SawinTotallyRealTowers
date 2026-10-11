/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.ProCGroups.Abelian.FiniteCharacterCriterion
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Circle

/-!
# Roots of unity detect profinite abelian isomorphisms

A finite subgroup of the circle is cyclic. Its order identifies it with the
actual roots of unity of a separably closed characteristic-zero field.
Transporting characters along this finite coefficient isomorphism reduces
isomorphism detection to roots-of-unity coefficients.
-/

noncomputable section

namespace ProCGroups.Duality

private theorem bijective_compLeft_of_coefficient_equiv
    {G H A B : Type*} [Group G] [Group H] [CommGroup A] [CommGroup B]
    [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B]
    (f : G →ₜ* H) (e : A ≃ₜ* B)
    (h : Function.Bijective (f.compLeft A)) : Function.Bijective (f.compLeft B) := by
  constructor
  · intro χ ψ hχψ
    have hh : (e.symm : B →ₜ* A).comp χ =
        (e.symm : B →ₜ* A).comp ψ := by
      apply h.injective
      exact congrArg (fun z : G →ₜ* B => (e.symm : B →ₜ* A).comp z) hχψ
    apply ContinuousMonoidHom.ext
    intro x
    apply e.symm.injective
    exact congrArg (fun z : H →ₜ* A => z x) hh
  · intro χ
    obtain ⟨ψ, hψ⟩ := h.surjective ((e.symm : B →ₜ* A).comp χ)
    refine ⟨(e : A →ₜ* B).comp ψ, ?_⟩
    apply ContinuousMonoidHom.ext
    intro x
    have hx := congrArg (fun z : G →ₜ* A => z x) hψ
    change ψ (f x) = e.symm (χ x) at hx
    change e (ψ (f x)) = χ x
    rw [hx, e.apply_symm_apply]

/-- Roots of unity over a separably closed characteristic-zero field suffice
as finite coefficients for detecting a profinite abelian isomorphism. -/
def equivOfBijectiveRootsOfUnityPullback
    (K : Type*) [Field K] [IsSepClosed K] [CharZero K]
    {G H : Type*} [CommGroup G] [CommGroup H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    [CompactSpace G] [CompactSpace H]
    [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace H]
    (f : G →ₜ* H)
    (hf : ∀ n : ℕ+, let _ : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥;
      let _ : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩;
      Function.Bijective (f.compLeft (rootsOfUnity (n : ℕ) K))) : G ≃ₜ* H := by
  apply equivOfBijectiveFiniteCharacterPullback f
  intro A hA
  have : IsCyclic A := isCyclic_of_injective_ringHom (Circle.coeHom.comp A.subtype)
    (Circle.coe_injective.comp Subtype.val_injective)
  let n : ℕ+ := ⟨Nat.card A, Nat.card_pos⟩
  let _ : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let _ : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let e : rootsOfUnity (n : ℕ) K ≃* A :=
    mulEquivOfCyclicCardEq (HasEnoughRootsOfUnity.natCard_rootsOfUnity K (n : ℕ))
  let eTop : rootsOfUnity (n : ℕ) K ≃ₜ* A :=
    { toMulEquiv := e
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  exact bijective_compLeft_of_coefficient_equiv f eTop (hf n)

end ProCGroups.Duality
