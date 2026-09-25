/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.RamificationSupport

set_option autoImplicit false

/-!
# Ramification support under an equivalence of top fields

An algebra equivalence preserves the permitted finite places on the base.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v w

namespace ClassFieldTower.Sawin.IsUnramifiedAtFinitePlacesOutside

/-- Replacing the top number field by an equivalent algebra preserves
unramifiedness outside the same set of finite places of the base. -/
theorem congrTop
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) {S : Set (HeightOneSpectrum (𝓞 K))}
    (h : IsUnramifiedAtFinitePlacesOutside K L S) :
    IsUnramifiedAtFinitePlacesOutside K M S := by
  let : Algebra L M := e.toRingHom.toAlgebra
  let : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (e.commutes x).symm)
  let eLM : L ≃ₐ[L] M :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun _ ↦ rfl)
  let eOLM : (𝓞 L) ≃ₐ[𝓞 L] (𝓞 M) :=
    NumberField.RingOfIntegers.mapAlgEquiv eLM
  let : Algebra.FormallyUnramified (𝓞 L) (𝓞 M) :=
    Algebra.FormallyUnramified.of_equiv eOLM
  intro P hP
  let q : HeightOneSpectrum (𝓞 L) := finitePlaceBelow (K := L) P
  have hOutside : finitePlaceBelow (K := K) q ∉ S := by
    simpa only [q, finitePlaceBelow_finitePlaceBelow] using hP
  let : P.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  let : Algebra.IsUnramifiedAt (𝓞 K) q.asIdeal := h q hOutside
  exact Algebra.IsUnramifiedAt.comp (R := 𝓞 K) q.asIdeal P.asIdeal

end ClassFieldTower.Sawin.IsUnramifiedAtFinitePlacesOutside
