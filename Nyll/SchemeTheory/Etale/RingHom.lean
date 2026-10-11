/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/RingHom/Etale.lean
Original mathlib source:
https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/RingTheory/RingHom/Etale.lean
-/

module

public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth

/-!
# Local criteria for étale ring homomorphisms

Étaleness is characterized by local standard smoothness of relative dimension
zero, including the degenerate subsingleton algebra case.
-/

@[expose] public section

universe u

namespace Algebra

variable {ι : Type*}

@[nontriviality]
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Subsingleton S]
    (n : ℕ) : IsStandardSmoothOfRelativeDimension n R S := by
  let P' : Generators R S (Fin (n + 1)) := .ofSurjective (fun _ : Fin (n + 1) ↦ 0) <| by
    intro s
    exact ⟨0, Subsingleton.elim _ _⟩
  have hker : P'.ker = ⊤ := le_antisymm le_top (fun x _ ↦ Subsingleton.elim _ _)
  let P : SubmersivePresentation R S (Fin (n + 1)) Unit :=
    { __ := P'
      relation _ := 1
      span_range_relation_eq_ker := by simp [hker]
      map _ := (0 : Fin (n + 1))
      map_inj _ _ _ := rfl
      jacobian_isUnit := isUnit_of_subsingleton _ }
  refine ⟨Fin (n + 1), Unit, inferInstance, inferInstance, P, ?_⟩
  simp [Presentation.dimension]

instance (priority := low) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsStandardSmooth R S] [FormallyUnramified R S] :
    IsStandardSmoothOfRelativeDimension 0 R S := by
  nontriviality S
  obtain ⟨α, β, _, _, ⟨P⟩⟩ := IsStandardSmooth.out (R := R) (S := S)
  have : Module.rank S (Ω[S⁄R]) = P.dimension := P.rank_kaehlerDifferential
  have : Subsingleton (Ω[S⁄R]) := inferInstance
  refine ⟨α, β, inferInstance, inferInstance, P, ?_⟩
  apply Nat.cast_injective (R := Cardinal)
  rw [← P.rank_kaehlerDifferential, rank_subsingleton', CharP.cast_eq_zero]

end Algebra

namespace RingHom

lemma Etale.eq_and :
    @Etale = fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.FormallyUnramified ∧ f.Smooth := by
  ext
  rw [etale_iff_formallyUnramified_and_smooth]

theorem Etale.iff_locally_isStandardSmoothOfRelativeDimension
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.Etale ↔ Locally (IsStandardSmoothOfRelativeDimension 0) f := by
  rw [etale_iff_formallyUnramified_and_smooth, smooth_iff_locally_isStandardSmooth]
  refine ⟨fun ⟨hr, hs⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · have : Locally (fun f ↦ f.FormallyUnramified ∧ f.IsStandardSmooth) f := by
      obtain ⟨s, hs, H⟩ := hs
      refine ⟨s, hs, fun t ht ↦ ⟨?_, H t ht⟩⟩
      exact
        FormallyUnramified.propertyIsLocal.StableUnderCompositionWithLocalizationAwayTarget _ t _ hr
    refine locally_of_locally ?_ this
    intro R S _ _ f hf
    algebraize [f]
    have : Algebra.FormallyUnramified R S := hf.1
    have : Algebra.IsStandardSmooth R S := hf.2
    change Algebra.IsStandardSmoothOfRelativeDimension 0 R S
    infer_instance
  · rw [← locally_iff_of_localizationSpanTarget FormallyUnramified.respectsIso
      FormallyUnramified.ofLocalizationSpanTarget]
    refine locally_of_locally ?_ h
    intro R S _ _ f hf
    algebraize [f]
    have : Algebra.IsStandardSmoothOfRelativeDimension 0 R S := hf
    change Algebra.FormallyUnramified R S
    infer_instance
  · refine locally_of_locally ?_ h
    intro R S _ _ f hf
    exact hf.isStandardSmooth

end RingHom
