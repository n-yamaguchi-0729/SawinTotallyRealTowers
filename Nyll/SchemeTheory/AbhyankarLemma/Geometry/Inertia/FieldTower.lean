/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.BaseChange
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup

/-!
# Inertia in a normal intermediate field

This file isolates the group-theoretic tower map used in the proof of
SGA 1, Expose X, Lemma 3.6.  A valuation subring `A` of a field `E` restricts
to a valuation subring of every intermediate field `M`.  When `M / K` is
normal, restriction of automorphisms carries the inertia group of `A` over
`K` to the inertia group of the restricted valuation.

The kernel is the relative inertia group of `E / M`, embedded by scalar
restriction.  No completeness, Henselianity, discreteness, or finiteness is
needed for this kernel calculation.
-/

noncomputable section

universe u v

namespace TameAbhyankar
namespace SGA1

open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring
open HilbertRamification
open HilbertRamification.ValuationSubring

variable (K : Type u) {E : Type v} [Field K] [Field E] [Algebra K E]

section Intermediate

variable (M : IntermediateField K E)

/-- Forgetting the intermediate-field scalars embeds relative inertia into
the inertia group over the ground field. -/
theorem relativeInertiaInclusion_injective
    (A : _root_.ValuationSubring E) :
    Function.Injective
      (inertiaGroupRestrictScalars (K := K) (M := M) A) := by
  intro sigma tau h
  apply Subtype.ext
  apply Subtype.ext
  apply decompositionGroupRestriction_restrictAutomorphismScalars_injective
    (K := K) (M := M)
  exact congrArg
    (fun iota : inertiaGroup K A =>
      ((((iota : inertiaGroup K A) : decompositionGroup K A) : E ≃ₐ[K] E))) h

end Intermediate

section NormalIntermediate

variable (M : IntermediateField K E) [Normal K M]

/-- Restriction from the inertia group over `K` to the inertia group on a
normal intermediate field `M`. -/
noncomputable def inertiaRestriction
    (A : _root_.ValuationSubring E) :
    inertiaGroup K A →*
      inertiaGroup K (A.comap M.val.toRingHom) := by
  let tauK : K →+* K := RingHom.id K
  let tauM : M →+* E := M.val
  have hsquare :
      tauM.comp (algebraMap K M) =
        (algebraMap K E).comp tauK := by
    ext x
    rfl
  exact galoisPullback_inertiaGroupMap tauK tauM hsquare A

/-- The inertia restriction has the expected action on elements of the
intermediate field. -/
@[simp]
theorem inertiaRestriction_apply_coe
    (A : _root_.ValuationSubring E) (sigma : inertiaGroup K A) (x : M) :
    (((((inertiaRestriction K M A sigma :
          inertiaGroup K (A.comap M.val.toRingHom)) :
        decompositionGroup K (A.comap M.val.toRingHom)) :
      M ≃ₐ[K] M) x : M) : E) =
      ((((sigma : inertiaGroup K A) : decompositionGroup K A) :
        E ≃ₐ[K] E) (x : E)) := by
  let tauK : K →+* K := RingHom.id K
  let tauM : M →+* E := M.val
  have hsquare :
      tauM.comp (algebraMap K M) =
        (algebraMap K E).comp tauK := by
    ext y
    rfl
  exact galoisPullback_galoisPullback_commutes tauK tauM hsquare
    ((((sigma : inertiaGroup K A) : decompositionGroup K A) :
      E ≃ₐ[K] E)) x

/-- The relative inertia group `I(E/M)` embeds into `I(E/K)` by forgetting
scalars.  Its range is exactly the kernel of restriction to `M`.

This is the inertia-group kernel identification in the tower
`K ⊆ M ⊆ E`. -/
theorem inertiaRestriction_ker_eq_range_relative
    (A : _root_.ValuationSubring E) :
    MonoidHom.ker (inertiaRestriction K M A) =
      (inertiaGroupRestrictScalars (K := K) (M := M) A).range := by
  ext sigma
  constructor
  · intro hsigma
    have hres : inertiaRestriction K M A sigma = 1 :=
      MonoidHom.mem_ker.mp hsigma
    let sigmaE : E ≃ₐ[K] E :=
      (((sigma : inertiaGroup K A) : decompositionGroup K A) : E ≃ₐ[K] E)
    have hfix : ∀ x : M, sigmaE (x : E) = (x : E) := by
      intro x
      have hx := congrArg
        (fun rho : inertiaGroup K (A.comap M.val.toRingHom) =>
          (((rho : decompositionGroup K (A.comap M.val.toRingHom)) :
            M ≃ₐ[K] M) x : M)) hres
      have hx' :
          (((((inertiaRestriction K M A sigma :
                inertiaGroup K (A.comap M.val.toRingHom)) :
              decompositionGroup K (A.comap M.val.toRingHom)) :
            M ≃ₐ[K] M) x : M) : E) = (x : E) := by
        simpa using congrArg (fun y : M => (y : E)) hx
      rw [inertiaRestriction_apply_coe] at hx'
      exact hx'
    let sigmaM : E ≃ₐ[M] E :=
      { sigmaE with
        commutes' := hfix }
    have hsigmaM_decomposition :
        sigmaM ∈ decompositionGroup M A := by
      apply (mem_decompositionGroup_restrictScalars_iff
        (K := K) (M := M) A sigmaM).mp
      change sigmaE ∈ decompositionGroup K A
      exact ((sigma : decompositionGroup K A)).property
    let deltaM : decompositionGroup M A :=
      ⟨sigmaM, hsigmaM_decomposition⟩
    have hrestrict_deltaM :
        decompositionGroupRestrictScalars (K := K) (M := M) A deltaM =
          (sigma : decompositionGroup K A) := by
      apply Subtype.ext
      rfl
    have hdeltaM_inertia : deltaM ∈ inertiaGroup M A := by
      apply (mem_inertiaGroup_restrictScalars_iff
        (K := K) (M := M) A deltaM).mp
      rw [hrestrict_deltaM]
      exact sigma.property
    let iotaM : inertiaGroup M A := ⟨deltaM, hdeltaM_inertia⟩
    refine ⟨iotaM, ?_⟩
    apply Subtype.ext
    exact hrestrict_deltaM
  · rintro ⟨iotaM, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    ext x
    rw [inertiaRestriction_apply_coe]
    exact
      ((((iotaM : inertiaGroup M A) : decompositionGroup M A) :
        E ≃ₐ[M] E).commutes x)

end NormalIntermediate

end SGA1
end TameAbhyankar
